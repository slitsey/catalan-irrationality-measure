import subprocess,sys,json
F=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer'
M=('1/100000','1/1000','1/100000')
for spec in sys.argv[1:]:
    t,lay=spec.split('-')
    gen='fewer7.py' if t=='A' else 'fewer.py'
    r=subprocess.run([sys.executable,'-I','-X','utf8','-u',rf'scripts\claude\bank\screen\{gen}',*( [lay,'p'] if t=='A' else [t,lay,'p'])],capture_output=True,text=True)
    print([l for l in r.stdout.splitlines() if l.startswith('RESULT')] or r.stderr[-300:],flush=True)
    r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\rec16.py',f'{t}-{lay}p',*M],capture_output=True,text=True)
    try:
        d=json.load(open(F+rf'\exact-{t}-{lay}p.json'))
        print('E',t,lay+'p',d['total_potential_cells'],{k:v['merged'] for k,v in d['covers_counts'].items()},'D',d['D_lower_F'],'mu',d['mu_upper_M3_F'],flush=True)
    except Exception as e:print('E FAIL',t,lay,r.stderr[-300:].replace('\n',' '),flush=True)
    subprocess.run([sys.executable,'-I','-X','utf8',r'scripts\claude\bank\screen\pipe.py',F+rf'\exact-{t}-{lay}p.json',f'{t}-{lay}p'])
