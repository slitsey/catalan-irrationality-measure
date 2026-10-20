from pathlib import Path
from fractions import Fraction as F
from pathlib import Path
import json
a=F(1,8);end=F(5,4);ev=lambda f,x:f[0]+f[1]*x
rows=[];gain=F(0)
for c in [1,3]:
 ps=[j for j in range(32) if j%4 in [0,c]]
 br={F(1,4),F(3,5)}
 for j in ps[1:]:
  for x in [F(4,j),4*end/j]:
   if F(1,4)<x<F(3,5):br.add(x)
 br=sorted(br);area=F(0)
 for lo,hi in zip(br,br[1:]):
  mid=(lo+hi)/2;short=(F(0),F(0));long=[]
  for j,k in zip(ps,ps[1:]):
   left=(F(1),F(0)) if j*mid/4<1 else (F(0),F(j,4))
   right=(end,F(0)) if k*mid/4>end else (F(0),F(k,4))
   span=(right[0]-left[0],right[1]-left[1])
   if ev(span,mid)<=0:continue
   if k-j==1:short=(short[0]+span[0],short[1]+span[1])
   else:long.append((span,j,k))
  fs=[((F(0),F(0)),0,0)]+[((s[0]-a+short[0],s[1]-F(1,4)+short[1]),j,k) for s,j,k in long]
  cut={lo,hi}
  for f,_,_ in fs:
   for g,_,_ in fs:
    if f[1]!=g[1]:
     x=(g[0]-f[0])/(f[1]-g[1])
     if lo<x<hi:cut.add(x)
  cut=sorted(cut)
  for l,h in zip(cut,cut[1:]):
   f,j,k=max(fs,key=lambda t:ev(t[0],(l+h)/2))
   if ev(f,(l+h)/2)<=0:continue
   area+=f[0]*(h-l)+f[1]*(h*h-l*l)/2
   row=(c,l,h,*f,j,k)
   if rows and rows[-1][0]==c and rows[-1][2]==l and rows[-1][3:]==row[3:]:rows[-1]=(c,rows[-1][1],h,*row[3:])
   else:rows.append(row)
 gain+=area/2
 print('class',c,area,float(area))
ratio=F(76444,10000)/(F(39028,10000)-F(184137,50000)+gain)
print('CONDITIONAL gain',gain,float(gain),'ratio',ratio,float(ratio),'rows',len(rows))
Path(__file__).with_name('nonclean-exact-forecast.json').write_text(json.dumps(dict(gain=str(gain),ratio=str(ratio),rows=[[str(x) for x in row] for row in rows]),indent=2))
