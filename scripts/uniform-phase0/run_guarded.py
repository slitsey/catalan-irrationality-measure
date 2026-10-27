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
OUT = WORK/'phase0/logs'
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
def snapshot(root):
    handle=k32.CreateToolhelp32Snapshot(2,0); entry=Entry(); entry.size=C.sizeof(entry)
    rows=[]; ok=k32.Process32FirstW(handle,C.byref(entry))
    while ok:
        rows.append((entry.pid,entry.parent,entry.exe)); ok=k32.Process32NextW(handle,C.byref(entry))
    k32.CloseHandle(handle)
    ids={root}; changed=True
    while changed:
        more={p for p,parent,name in rows if parent in ids}; changed=not more<=ids; ids|=more
    total=0; peaks={}
    for pid,parent,name in rows:
        if pid not in ids: continue
        h=k32.OpenProcess(0x410,False,pid)
        if not h: continue
        m=Memory(); m.cb=C.sizeof(m); ts=[W.FILETIME() for _ in range(4)]
        if psapi.GetProcessMemoryInfo(h,C.byref(m),m.cb):
            total+=m.working
            if name.lower()=='lean.exe': peaks[pid]=m.peak
        k32.CloseHandle(h)
    return total,peaks

target=sys.argv[1]; mode=sys.argv[2] if len(sys.argv)>2 else 'preflight'
assert mode in ('preflight','build')
label=target.replace('.','_')+'-'+mode
if (OUT/(label+'.log')).exists():
    label += '-'+time.strftime('%Y%m%d-%H%M%S')
args='build '+target+(' --no-build' if mode=='preflight' else '')
cmd=['powershell.exe','-NoProfile','-ExecutionPolicy','Bypass','-File',str(GUARD),
    '-Kind','lean','-Dir',str(WORK),'-BudgetGB','4','-Exe',str(LAKE),'-ArgString',args]
start=time.perf_counter(); peak_tree=0; peaks={}
with (OUT/(label+'.log')).open('w',encoding='utf-8') as log:
    p=subprocess.Popen(cmd,stdout=log,stderr=subprocess.STDOUT)
    while p.poll() is None:
        total,observed=snapshot(p.pid); peak_tree=max(peak_tree,total)
        for pid,value in observed.items(): peaks[pid]=max(peaks.get(pid,0),value)
        time.sleep(.15)
    rc=p.wait()
result=dict(target=target,mode=mode,rc=rc,wrapper_wall_seconds=time.perf_counter()-start,
    sampled_wrapper_tree_peak_bytes=peak_tree,lean_process_peak_working_sets_bytes=peaks,
    log=str(OUT/(label+'.log')),
    note='Tree includes wrapper/guard/Lake; individual Lean values are OS lifetime peaks. No CPU/kernel estimate inferred from wrapper time.')
(OUT/(label+'.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result),flush=True)
logtext=(OUT/(label+'.log')).read_text(encoding='utf-8')
print('\n'.join(line for line in logtext.splitlines() if any(key in line for key in
    ('Built ', 'Build completed', 'error:', 'depends on axioms', 'does not depend on any axioms'))),flush=True)
sys.exit(rc)
