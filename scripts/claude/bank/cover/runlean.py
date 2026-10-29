"""Run `lake env lean --run <file> args...` from the worktree, stdout to a file.  usage: runlean.py <out> <file.lean> args..."""
import subprocess, sys, os
ROOT = r'C:\Users\seanl\Documents\Codex\2026-10-11\plea'
WT = os.path.join(ROOT, 'work', 'catalan-uniform')
LAKE = os.path.join(ROOT, 'work', 'lean-runtime', 'lean-4.35.0-rc2-windows', 'bin', 'lake.exe')
out = sys.argv[1]
with open(out, 'w', encoding='utf-8', newline='\n') as f:
    r = subprocess.run([LAKE, 'env', 'lean', '--run'] + sys.argv[2:], cwd=WT, stdout=f, stderr=subprocess.STDOUT)
sys.exit(r.returncode)
