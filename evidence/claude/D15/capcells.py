import re,glob
from fractions import Fraction as Fr
cells=[]
for f in sorted(glob.glob('CatalanCore/Uniform/Bank/Chi3/Cap/B0*.lean')):
    s=open(f,encoding='utf-8').read()
    for m in re.finditer(r'def (k\d+_\d+) : TCell2 × ℚ := decodeCap raw_ints% \[([^\]]*)\] raw_ints% \[([^\]]*)\]',s):
        name=m.group(1)
        ub=[int(x) for x in m.group(2).split(',')]
        t=[int(x) for x in m.group(3).replace('\n',' ').split(',')]
        a=Fr(t[0],t[1]); b=Fr(t[2],t[3]); k=t[4]
        if k==1: n=t[5]; 
        elif k==2: n=t[5]
        else: n=None
        cells.append((name,a,b,Fr(ub[0],ub[1]),k,n,f.split('/')[-1]))
if __name__=='__main__':
    print(len(cells))
    mp=Fr(23147017380990627,10**16)
    over=0
    for c in cells:
        ov=(c[2]-c[1])*max(c[3]-mp,0)
        over+=ov
        print(c[0],float(c[1]),float(c[2]),'w=%.2e'%float(c[2]-c[1]),'ub-m=%.3e'%float(c[3]-mp),'kind',c[4],'n',c[5],'ov=%.2e'%float(ov))
    print('sum overshoot',float(over))
