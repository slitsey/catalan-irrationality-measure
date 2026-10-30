import subprocess,sys,json
F=r'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer'
for spec in sys.argv[1].split(','):
    t,lay=spec.split('-')
    for mr,ms in (('1/10000','1/1000'),('1/1000','1/1000'),('1/1000','1/100')):
        sfx='-m'+mr.split('/')[1]+'s'+ms.split('/')[1]
        r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\rec16.py',f'{t}-{lay}',mr,ms,mr,sfx],capture_output=True,text=True)
        try:
            d=json.load(open(F+rf'\exact-{t}-{lay}{sfx}.json'))
            print('M',t,lay,mr,ms,d['total_potential_cells'],{k:v['merged'] for k,v in d['covers_counts'].items()},'D',d['D_lower_F'],'mu',d['mu_upper_M3_F'],flush=True)
        except Exception as e:print('M FAIL',t,lay,mr,ms,r.stderr[-200:].replace('\n',' '),flush=True)
