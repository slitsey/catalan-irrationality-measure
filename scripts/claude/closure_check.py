"""Import-closure check for the public-root theorems (LOOSE-ENDS item 5).

For each target module, walk `import` lines through this repository's own Lean sources (packages under
.lake are external and skipped) and report the modules of the closure whose files are untracked or
modified in git.  usage: closure_check.py [--json out.json] Module1 Module2 ..."""
import json, os, re, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
IMPORT = re.compile(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)


def path_of(mod):
    p = os.path.join(ROOT, *mod.split('.')) + '.lean'
    return p if os.path.exists(p) else None


def closure(targets):
    seen, stack, missing = {}, list(targets), set()
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        p = path_of(m)
        if p is None:
            missing.add(m)          # external (Mathlib, packages) or absent
            continue
        seen[m] = p
        with open(p, encoding='utf-8') as fh:
            head = fh.read(20000)   # imports precede the first declaration
        stack.extend(IMPORT.findall(head.split('\nnamespace', 1)[0]))
    return seen, missing


def git_state():
    out = subprocess.run(['git', 'status', '--porcelain', '-uall'], cwd=ROOT, capture_output=True,
                         text=True, check=True).stdout
    state = {}
    for line in out.splitlines():
        code, path = line[:2], line[3:].strip().strip('"')
        state[os.path.normpath(os.path.join(ROOT, path))] = code.strip()
    return state


if __name__ == '__main__':
    args = sys.argv[1:]
    out_json = None
    if args[:1] == ['--json']:
        out_json, args = args[1], args[2:]
    state = git_state()
    report = {}
    for t in args:
        mods, _ = closure([t])
        bad = {m: state[os.path.normpath(p)] for m, p in mods.items() if os.path.normpath(p) in state}
        report[t] = {'modules': len(mods), 'untracked_or_modified': dict(sorted(bad.items()))}
        print(f'{t}: {len(mods)} repo modules, {len(bad)} untracked/modified')
        for m, c in sorted(bad.items()):
            print(f'    {c:2} {m}')
    if out_json:
        with open(out_json, 'w', encoding='utf-8') as fh:
            json.dump(report, fh, indent=1)
