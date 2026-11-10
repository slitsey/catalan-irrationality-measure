"""Route-I build manifest (Sean, 6 Nov: "nothing built twice").

One row per module in the route-I closure: module, owner, plan row, wave, status, source sha256, note.
File: work/tools/lanes/manifest.tsv. Header lines `# scope: <prefix>` name the prefixes under
which a NEW module must be listed before it can build.

Status:
  planned      listed, never built; the owner may build it once.
  needs-build  reused module whose olean is missing or older than its source; built once.
  built        built with rc 0 from the recorded source sha; never rebuilt without rebuild-ok.
  rebuild-ok   coordinator allowed ONE rebuild (note says why); returns to built on rc 0.

The lanes driver calls `refusal(target, owner)` before admitting a build, and `mark_built`
after rc 0. Coordinator CLI:
  manifest.py init                    (re)generate from EA44 + RouteI files (keeps existing rows)
  manifest.py add <module> <owner> <row> <wave> [note]
  manifest.py rebuild-ok <module> <reason>
  manifest.py owner <module> <owner>
  manifest.py show [prefix]
"""
import hashlib, json, os, sys, time, uuid, ctypes
from contextlib import contextmanager
from functools import wraps
from pathlib import Path

ROOT = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK = ROOT / 'work/catalan-uniform'
MAN = ROOT / 'work/tools/lanes/manifest.tsv'
EA44 = ROOT / ('outputs/Compatibility programme/leads-tests-2026-11-02/g-design-rescreen/'
               'chebengine/routei-pricing/FK-EA44-LOCAL-1046.json')
COLS = ['module', 'owner', 'row', 'wave', 'status', 'src_sha', 'note']
DEFAULT_SCOPE = ['CatalanMeasure.GenD.Signed.RouteI', 'CatalanMeasure.GenD.Signed.Davis.DesignWeights',
                 'CatalanMeasure.GenD.Signed.ChebSquare', 'CatalanMeasure.GenD.Signed.Count']


@contextmanager
def write_lock(timeout=30):
    """Process-wide writer mutex, keyed by the actual manifest path.

    Windows releases abandoned mutex ownership if a writer exits. The mutex
    is reentrant on one thread, so mark_built/main may safely call save.
    Readers see the prior or next complete atomic file and need no lock.
    """
    from ctypes import wintypes
    kernel = ctypes.WinDLL('kernel32', use_last_error=True)
    kernel.CreateMutexW.argtypes = [ctypes.c_void_p, wintypes.BOOL, wintypes.LPCWSTR]
    kernel.CreateMutexW.restype = wintypes.HANDLE
    kernel.WaitForSingleObject.argtypes = [wintypes.HANDLE, wintypes.DWORD]
    kernel.WaitForSingleObject.restype = wintypes.DWORD
    kernel.ReleaseMutex.argtypes = [wintypes.HANDLE]
    kernel.ReleaseMutex.restype = wintypes.BOOL
    kernel.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel.CloseHandle.restype = wintypes.BOOL
    key = hashlib.sha256(str(MAN.resolve()).lower().encode('utf-8')).hexdigest()
    handle = kernel.CreateMutexW(None, False, 'Local\\CodexManifestWrite_' + key)
    if not handle:
        raise ctypes.WinError(ctypes.get_last_error())
    acquired = False
    try:
        result = kernel.WaitForSingleObject(handle, int(timeout * 1000))
        if result not in (0, 0x80):
            if result == 0x102:
                raise TimeoutError('manifest writer mutex timed out: ' + str(MAN))
            raise ctypes.WinError(ctypes.get_last_error())
        acquired = True
        yield
    finally:
        if acquired:
            kernel.ReleaseMutex(handle)
        kernel.CloseHandle(handle)


def _write_locked(fn):
    @wraps(fn)
    def wrapped(*args, **kwargs):
        with write_lock():
            return fn(*args, **kwargs)
    return wrapped


def src_path(m):
    return WORK / (m.replace('.', '/') + '.lean')


def olean(m):
    return WORK / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')


def sha(m):
    try:
        return hashlib.sha256(src_path(m).read_bytes()).hexdigest()
    except OSError:
        return ''


def load():
    scope, rows = [], {}
    if not MAN.exists():
        return list(DEFAULT_SCOPE), rows
    for l in MAN.read_text(encoding='utf-8').splitlines():
        if l.startswith('# scope:'):
            scope.append(l.split(':', 1)[1].strip())
        elif l and not l.startswith('#') and not l.startswith('module\t'):
            f = l.split('\t') + [''] * len(COLS)
            rows[f[0]] = dict(zip(COLS, f[:len(COLS)]))
    return scope, rows


@_write_locked
def save(scope, rows):
    out = ['# Route-I build manifest. Edit only via scripts/claude/manifest.py (the driver also writes it).']
    out += [f'# scope: {s}' for s in scope]
    out.append('\t'.join(COLS))
    out += ['\t'.join(rows[m].get(c, '') for c in COLS) for m in sorted(rows)]
    tmp = MAN.with_name(MAN.name + f'.{os.getpid()}.{uuid.uuid4().hex}.tmp')
    try:
        tmp.write_text('\n'.join(out) + '\n', encoding='utf-8')
        deadline = time.monotonic() + 5
        while True:
            try:
                tmp.replace(MAN)
                break
            except PermissionError:
                if time.monotonic() >= deadline:
                    raise
                time.sleep(.05)
    finally:
        if tmp.exists():
            tmp.unlink()


def fresh(m):
    # Baseline: an olean exists. Its source sha is recorded now, so any later edit is caught.
    # Staleness from upstream edits is checked by the driver's preflight at submit time
    # (mtimes are unreliable here: git operations touched sources without changing them).
    return olean(m).exists() and src_path(m).exists()


def in_scope(target, scope):
    return any(target == p or target.startswith(p + '.') for p in scope)


def refusal(target, owner):
    """None = admit. ('ok', msg) = already built and current: answer rc 0 without building.
    (rc, msg) otherwise. Targets outside the manifest and its scope are not governed."""
    scope, rows = load()
    r = rows.get(target)
    if r is None:
        if in_scope(target, scope):
            return 93, (f'{target} is in the route-I scope but not in the manifest; the coordinator adds it '
                        '(manifest.py add) with owner, plan row and wave before it is built')
        return None
    owner = owner or 'coordinator'
    if r['owner'] != owner:
        return 93, f'{target} is owned by {r["owner"]} (manifest), not {owner}; set LANES_OWNER or ask the coordinator'
    st, cur = r['status'], sha(target)
    if st in ('planned', 'needs-build', 'rebuild-ok'):
        return None
    if st == 'built':
        if cur != r['src_sha']:
            return 93, (f'{target} was built from source {r["src_sha"][:12]} and has since been edited ({cur[:12]}); '
                        'a rebuild needs coordinator rebuild-ok (build-once rule)')
        return 'check-stale', f'{target} already built from this source (manifest)'
    return 93, f'{target} has unknown manifest status {st!r}'


@_write_locked
def mark_built(target, rc):
    if rc != 0:
        return
    scope, rows = load()
    r = rows.get(target)
    if r is None or (r['status'] == 'built' and r['src_sha'] == sha(target)):
        return
    r.update(status='built', src_sha=sha(target),
             note=(r['note'] + ' ' if r['note'] else '') + time.strftime('built %Y-%m-%dT%H:%MZ', time.gmtime()))
    save(scope, rows)


@_write_locked
def init():
    scope, rows = load()
    added = 0
    d = json.loads(EA44.read_text(encoding='utf-8'))
    for e in d['rows']:
        m = e['module']
        if m in rows:
            continue
        rows[m] = dict(module=m, owner='coordinator', row='reuse:' + e.get('EX_class', ''), wave='A',
                       status='built' if fresh(m) else 'needs-build', src_sha=sha(m), note='EA44')
        added += 1
    for f in sorted((WORK / 'CatalanMeasure/GenD/Signed/RouteI').glob('*.lean')):
        m = 'CatalanMeasure.GenD.Signed.RouteI.' + f.stem
        if m not in rows:
            rows[m] = dict(module=m, owner='decay2', row='T0', wave='A',
                           status='built' if fresh(m) else 'planned', src_sha=sha(m), note='terminal chain')
            added += 1
    for m, own, row, wave, note in [
            ('CatalanMeasure.GenD.Signed.ChebSquare', 'l3', 'X1', 'C', 'C-SQ shared checker (L36)'),
            ('CatalanMeasure.GenD.Signed.Davis.DesignWeights', 'l3', 'T6w', 'A', 'generic weights; D58 instance (L36)')]:
        if m not in rows:
            rows[m] = dict(module=m, owner=own, row=row, wave=wave,
                           status='planned', src_sha=sha(m), note=note)
            added += 1
    # a module listed `built` must really have a current olean
    for m, r in rows.items():
        if r['status'] == 'built' and not fresh(m) and r['note'] == 'EA44':
            r['status'] = 'needs-build'
    save(scope, rows)
    c = {}
    for r in rows.values():
        c[r['status']] = c.get(r['status'], 0) + 1
    print(f'manifest: {len(rows)} modules ({added} added); {c}')


@_write_locked
def main():
    a = sys.argv[1:]
    if not a or a[0] == 'init':
        init()
    elif a[0] == 'add':
        scope, rows = load()
        m, own, row, wave = a[1:5]
        rows[m] = dict(module=m, owner=own, row=row, wave=wave, status='planned', src_sha='',
                       note=' '.join(a[5:]))
        save(scope, rows); print('added', m)
    elif a[0] == 'rebuild-ok':
        scope, rows = load()
        held = [l for l in (MAN.parent / 'hold.txt').read_text(encoding='utf-8').splitlines()
                if l.partition('#')[0].strip() and a[1].startswith(l.partition('#')[0].strip())]
        if held:
            sys.exit('refused: module is under a coordinator hold, lift it first: ' + held[0])
        rows[a[1]].update(status='rebuild-ok', note=rows[a[1]]['note'] + ' | rebuild-ok: ' + ' '.join(a[2:]))
        save(scope, rows); print('rebuild-ok', a[1])
    elif a[0] == 'owner':
        scope, rows = load()
        rows[a[1]]['owner'] = a[2]; save(scope, rows); print('owner', a[1], a[2])
    elif a[0] == 'show':
        scope, rows = load()
        for m in sorted(rows):
            if len(a) < 2 or m.startswith(a[1]):
                print('\t'.join(rows[m][c] for c in COLS))


if __name__ == '__main__':
    main()
