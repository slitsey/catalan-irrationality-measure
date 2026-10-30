import subprocess,sys
tags=sys.argv[1].split(',')
for t in tags:
  for k in ('s1','s2','s3','s4','s5','s6','s7','s8'):
    for dg in (3,4,5):
        r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\fewer.py',t,f'{k}d{dg}'],capture_output=True,text=True)
        l=[x for x in r.stdout.splitlines() if x.startswith('RESULT')]
        print(l[0] if l else ('FAIL',t,k,dg,r.stderr[-200:].replace('\n',' ')),flush=True)
