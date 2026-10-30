"""usage: pipe.py exact.json NAME  -> rec, bp, asm, mp, sum with outputs in d16/NAME-*.json"""
import subprocess,sys
O=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16'
ex,name=sys.argv[1:3];S=r'scripts\claude\bank\screen'
def run(script,*a,log=None):
    subprocess.run([sys.executable,'-I','-X','utf8',rf'{S}\{script}',*a],stdout=open(O+rf'\{name}-{script[:-3]}.log','w'),stderr=subprocess.STDOUT)
run('recover.py',ex,O+rf'\{name}-rec.json')
run('bp.py',ex,O+rf'\{name}-bp.json')
run('assemble.py',ex,O+rf'\{name}-bp.json',O+rf'\{name}-asm.json')
run('mp.py',ex,O+rf'\{name}-mp.json')
run('summary.py',ex,O+rf'\{name}-rec.json',O+rf'\{name}-bp.json',O+rf'\{name}-asm.json',O+rf'\{name}-mp.json',O+rf'\{name}-sum.json')
