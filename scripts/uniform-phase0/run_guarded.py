"""Serial guarded Lean build with Windows memory observations; never kills jobs."""
import ctypes as C
from ctypes import wintypes as W
import json, subprocess, sys, time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')

ROOT = Path(r'C:\Users\seanl\Documents\Codex\2026-10-11\plea')
WORK = ROOT/'work/catalan-uniform'
LAKE = ROOT/'work/lean-runtime/lean-4.35.0-rc2-windows/bin/lake.exe'
GUARD = ROOT/'work/tools/guard-proof-safe.ps1'
OUT = ROOT/'outputs/Compatibility programme/lean-plan-2026-10-27/evidence/phase1/logs'
OUT.mkdir(parents=True, exist_ok=True)
k32 = C.WinDLL('kernel32', use_last_error=True)
psapi = C.WinDLL('psapi', use_last_error=True)
class Entry(C.Structure):
    _fields_ = [('size', W.DWORD), ('usage', W.DWORD), ('pid', W.DWORD),
        ('heap', C.c_size_t), ('module', W.DWORD), ('threads', W.DWORD),
        ('parent', W.DWORD), ('priority', W.LONG), ('flags', W.DWORD), ('exe', W.WCHAR*260)]
class Memory(C.Structure):
    _fields_ = [('cb',W.DWORD), ('faults',W.DWORD)] + [(n,C.c_size_t) for n in
        ('peak','working','peakpaged','paged','peaknonpaged','nonpaged','pagefile','peakpagefile')]
k32.CreateToolhelp32Snapshot.restype=W.HANDLE
k32.Process32FirstW.argtypes=[W.HANDLE,C.POINTER(Entry)]
k32.Process32NextW.argtypes=[W.HANDLE,C.POINTER(Entry)]
k32.OpenProcess.argtypes=[W.DWORD,W.BOOL,W.DWORD]; k32.OpenProcess.restype=W.HANDLE
k32.CloseHandle.argtypes=[W.HANDLE]
psapi.GetProcessMemoryInfo.argtypes=[W.HANDLE,C.POINTER(Memory),W.DWORD]
k32.GetProcessTimes.argtypes=[W.HANDLE]+[C.POINTER(W.FILETIME)]*4
k32.GetSystemTimeAsFileTime.argtypes=[C.POINTER(W.FILETIME)]
def filetime(t): return (t.dwHighDateTime<<32)+t.dwLowDateTime
def creation(handle):
    times=[W.FILETIME() for _ in range(4)]
    if not k32.GetProcessTimes(handle,*[C.byref(t) for t in times]): return None
    return filetime(times[0])

def snapshot(root,root_birth):
    # Pin handles and bind every parent edge to birth time, as the enforcement
    # guard does. Reused parent PIDs must never import unrelated processes.
    cutoff_ft=W.FILETIME(); k32.GetSystemTimeAsFileTime(C.byref(cutoff_ft))
    cutoff=filetime(cutoff_ft)
    handle=k32.CreateToolhelp32Snapshot(2,0); entry=Entry(); entry.size=C.sizeof(entry)
    rows=[]; ok=k32.Process32FirstW(handle,C.byref(entry))
    while ok:
        rows.append((entry.pid,entry.parent,entry.exe)); ok=k32.Process32NextW(handle,C.byref(entry))
    k32.CloseHandle(handle)
    pinned={}
    def pin(pid):
        if pid in pinned: return pinned[pid]
        h=k32.OpenProcess(0x410,False,pid)
        if not h: return None
        born=creation(h)
        if born is None or born>cutoff:
            k32.CloseHandle(h); return None
        pinned[pid]=(h,born); return pinned[pid]
    try:
        root_identity=pin(root)
        if root_identity is None or root_identity[1]!=root_birth: return 0,{}
        ids={root}; changed=True
        while changed:
            changed=False
            for pid,parent,name in rows:
                if pid in ids or parent not in ids: continue
                child=pin(pid); par=pinned[parent]
                if child is not None and par[1]<=child[1]<=cutoff:
                    ids.add(pid); changed=True
        total=0; peaks={}
        for pid,parent,name in rows:
            if pid not in ids: continue
            h,born=pinned[pid]; m=Memory(); m.cb=C.sizeof(m)
            if psapi.GetProcessMemoryInfo(h,C.byref(m),m.cb):
                total+=m.working
                if name.lower()=='lean.exe': peaks[pid]=m.peak
        return total,peaks
    finally:
        for h,born in pinned.values(): k32.CloseHandle(h)

target=sys.argv[1]; mode=sys.argv[2] if len(sys.argv)>2 else 'preflight'
assert mode in ('preflight','build')
# Parent-authorized exact provider gate; new invocations only, before reservation.
_bank_provider_marker = OUT.parent/'bank-provider-hold.json'
_bank_announced = False
while target == 'CatalanMeasure.GenD.Uniform.Bank.Providers532' and _bank_provider_marker.exists():
    _bank_cfg = json.loads(_bank_provider_marker.read_text(encoding='utf-8-sig'))
    if _bank_cfg.get('target') != target:
        raise RuntimeError('invalid exact bank-provider hold marker')
    if not _bank_announced:
        print(json.dumps(dict(admission='held-before-reservation',target=target,
            marker=str(_bank_provider_marker))),flush=True)
        _bank_announced = True
    time.sleep(1)
# Parent-authorized exact/prefix admission hold; running guards are untouched.
# Control metadata is external and atomically replaced by its coordinator.
_admission_marker = OUT.parent/'arithmetic-cache-hold.json'
_announced_hold = False
while _admission_marker.exists():
    # Never let even malformed arithmetic metadata affect an unrelated lane.
    _owned_exact = ('CatalanMeasure.GenD.OddProfile','CatalanMeasure.GenD.PL',
        'CatalanMeasure.GenD.PrimeGrowth','CatalanMeasure.GenD.Denominator')
    _owned_prefixes = ('CatalanMeasure.Parametric.UpperPrime',
        'CatalanMeasure.GenD.Uniform.Arithmetic.')
    if target not in _owned_exact and not any(target.startswith(x) for x in _owned_prefixes):
        break
    try:
        _admission_cfg = json.loads(_admission_marker.read_text(encoding='utf-8'))
    except FileNotFoundError:
        continue
    _exact = _admission_cfg.get('targets', [])
    _prefixes = _admission_cfg.get('prefixes', [])
    if not all(isinstance(x,str) and x and '*' not in x for x in _exact+_prefixes):
        raise RuntimeError('invalid scoped admission marker')
    if target not in _exact and not any(target.startswith(x) for x in _prefixes):
        break
    if not _announced_hold:
        print(json.dumps(dict(admission='held-before-reservation',target=target,
            marker=str(_admission_marker))),flush=True)
        _announced_hold = True
    time.sleep(1)
label=target.replace('.','_')+'-'+mode
if (OUT/(label+'.log')).exists():
    label += '-'+time.strftime('%Y%m%d-%H%M%S')
args='build '+target+(' --no-build' if mode=='preflight' else '')
cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),
    '-Kind','lean','-Dir',str(WORK),'-BudgetGB',(sys.argv[3] if len(sys.argv)>3 else '4'),'-Exe',str(LAKE),'-ArgString',args]
start=time.perf_counter(); peak_tree=0; peaks={}
with (OUT/(label+'.log')).open('w',encoding='utf-8') as log:
    p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT)
    root_birth=creation(int(p._handle))
    while p.poll() is None:
        total,observed=snapshot(p.pid,root_birth); peak_tree=max(peak_tree,total)
        for pid,value in observed.items(): peaks[pid]=max(peaks.get(pid,0),value)
        time.sleep(.15)
    rc=p.wait()
result=dict(target=target,mode=mode,rc=rc,wrapper_wall_seconds=time.perf_counter()-start,
    sampled_wrapper_tree_peak_bytes=peak_tree,lean_process_peak_working_sets_bytes=peaks,
    log=str(OUT/(label+'.log')), observer='creation-bound-v2',
    note='Tree includes wrapper/guard/Lake; individual Lean values are OS lifetime peaks. No CPU/kernel estimate inferred from wrapper time.')
(OUT/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
logtext=(OUT/(label+'.log')).read_text(encoding='utf-8')
print('\n'.join(line for line in logtext.splitlines() if any(key in line for key in
    ('Built ', 'Building ', 'Build completed', 'error:', 'depends on axioms', 'does not depend on any axioms', 'Some required targets'))),flush=True)
sys.exit(rc)

