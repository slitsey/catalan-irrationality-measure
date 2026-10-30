"""Build a set of modules leaf-first through the lanes driver, one dependency level per wave.

usage: build_waves.py GB Module1 Module2 ...  (modules outside the set are assumed up to date)
Each wave submits its modules concurrently (`lanes.py submit`), waits for all, and stops at the first
failure.  Prints one line per module with its rc."""
import os, subprocess, sys, json
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from closure_check import path_of, IMPORT

PY = sys.executable
GB, mods = sys.argv[1], sys.argv[2:]
S = set(mods)
deps = {}
for m in mods:
    with open(path_of(m), encoding='utf-8') as fh:
        deps[m] = {d for d in IMPORT.findall(fh.read(20000).split('\nnamespace', 1)[0]) if d in S}
level, left = [], set(mods)
while left:
    ready = sorted(m for m in left if not (deps[m] & left))
    if not ready: sys.exit('cycle among: ' + ', '.join(sorted(left)))
    level.append(ready); left -= set(ready)
print(f'{len(mods)} modules in {len(level)} waves', flush=True)

def submit(m):
    r = subprocess.run([PY, '-I', '-X', 'utf8', 'scripts/claude/lanes.py', 'submit', m, GB], capture_output=True, text=True)
    rc = None
    for line in r.stdout.splitlines()[::-1]:
        if line.startswith('{') and '"rc"' in line:
            rc = json.loads(line).get('rc'); break
    return m, rc

for i, wave in enumerate(level):
    with ThreadPoolExecutor(max_workers=min(6, len(wave))) as ex:
        res = list(ex.map(submit, wave))
    for m, rc in res: print(f'wave {i}: {m} rc={rc}', flush=True)
    if any(rc != 0 for _, rc in res):
        sys.exit(f'stopping after wave {i}: a module failed')
print('all built', flush=True)
