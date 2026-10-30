import subprocess,sys
for tag in ('FIFTH','THIRD','LAMB','CHI3'):
    for lay in ('g1','g2','g3','g4','g5','g6','g7'):
        r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\fewer.py',tag,lay],capture_output=True,text=True)
        print(([l for l in r.stdout.splitlines() if l.startswith('RESULT')] or [tag,lay,'FAIL',r.stderr[-300:]]),flush=True)
