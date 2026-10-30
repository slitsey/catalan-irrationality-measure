import subprocess,sys
M={'A':('1/100000','1/1000','1/100000'),'FIFTH':('1/100000','1/1000','1/100000'),'THIRD':('1/100000','1/1000','1/100000'),'LAMB':('1/100000','1/1000','1/100000'),'CHI3':('1/100000','1/1000','1/100000')}
tags=sys.argv[1].split(',');lays=sys.argv[2].split(',')
for lay in lays:
  for t in tags:
    r=subprocess.run([sys.executable,'-I','-X','utf8','-u',r'scripts\claude\bank\screen\rec16.py',f'{t}-{lay}',*M[t]],capture_output=True,text=True)
    import json
    try:
        d=json.load(open(rf'C:\Users\seanl\Documents\Codex\2026-10-11\plea\outputs\Compatibility programme\decay-cell-reduction-2026-10-28\d16\fewer\exact-{t}-{lay}.json'))
        print('E',t,lay,d['total_potential_cells'],{k:v['merged'] for k,v in d['covers_counts'].items()},'D',d['D_lower_F'],'mu',d['mu_upper_M3_F'],flush=True)
    except Exception as e:print('E FAIL',t,lay,r.stderr[-400:],flush=True)
