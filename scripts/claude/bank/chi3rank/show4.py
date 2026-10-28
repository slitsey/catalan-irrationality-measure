import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from vsel import *
for cls,keys in ((1,[(1,3,1,1),(2,3,1,1)]),(5,[(0,1,0,0),(0,2,0,0)])):
  for k in keys:
    c=cert(cls,*k)
    print('class',cls,'key',k,'R',c['R'],'C',c['C'])
    print(' lf',{d:str(v) for d,v in c['lf'].items()},'ee',{d:str(v) for d,v in c['ee'].items()})
    for nm in ('Lq','Lq_','Pq','Pq_'): print(' ',nm,{kk:str(v) for kk,v in c[nm].items() if True})
    print(' kr',c['kr'],'kc',c['kc'],'rload',{d:(str(a),str(b)) for d,(a,b) in c['rload'].items()},'cload',{d:(str(a),str(b)) for d,(a,b) in c['cload'].items()})
