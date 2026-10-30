import subprocess,sys
for k in ('c3','g1','g4','g5','s1','s2','s3','s4','s5','s6','s7','s8'):
    for dg in ((None,) if k in ('c3','g1','g4','g5') else (3,4,5)):
        lay=k if dg is None else f'{k}d{dg}'
        r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\fewer7.py',lay],capture_output=True,text=True)
        l=[x for x in r.stdout.splitlines() if x.startswith('RESULT')]
        print(l[0] if l else ('FAIL',lay,r.stderr[-300:].replace('\n',' ')),flush=True)
