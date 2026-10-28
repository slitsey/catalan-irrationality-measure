import sys,os; sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from vsel import *
FEAS=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,1),(2,3),(3,3)]
if __name__=='__main__':
 for cls in (1,5):
  print('class',cls)
  for k1,k2 in FEAS:
      for zA in (0,1):
        for zB in (0,1):
          c=cert(cls,k1,k2,zA,zB)
          print((k1,k2,zA,zB),'R',c['R'],'C',c['C'],'kr',c['kr'],'kc',c['kc'])
