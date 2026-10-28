import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from tbl import *
V={1:(Q(1),Q(1,78)),5:(Q(1),Q(46,2295))}
for cls in (1,5):
  print('class',cls)
  for k1,k2 in FEAS:
    row=[]
    for zA in (0,1):
      for zB in (0,1):
        c=cert(cls,k1,k2,zA,zB)
        row.append(gain(c,V[cls]))
    print((k1,k2),row, [ (c_:=cert(cls,k1,k2,0,0))['rload'] and {d:(str(a),str(b)) for d,(a,b) in c_['rload'].items()}, {e:(str(a),str(b)) for e,(a,b) in c_['cload'].items()}])
