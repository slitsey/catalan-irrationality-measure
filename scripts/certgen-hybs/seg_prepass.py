# Lean-consistent thresholds for the segment cells: gamma = min(JSON gamma, floor((flat Lean bound - s) 2^32)); writes refined_seg.json and Sbase.
from hsmirror import *
import sys, json
D=data(); PTS=pts_sorted(); MP=F(D['info']['MP'])
S=F(int(sys.argv[1]),10**9) if len(sys.argv)>1 else F(4,10**6)
from multiprocessing import Pool
def f(c):
    a,b,g=c
    lb=F(-near_sum((a,b,0,0),PTS),2**97)-realRest((a,b))
    return min(g, math.floor((lb-S)*2**32))
if __name__=='__main__':
    L0=[tuple(c) for c in D['seg']]
    import os
    MG=int(os.environ.get('HS_SEGMERGE','1'))
    L=[(L0[i][0], L0[min(i+MG,len(L0))-1][1], min(c[2] for c in L0[i:i+MG])) for i in range(0,len(L0),MG)]
    with Pool(6) as p: gs=p.map(f,L,chunksize=50)
    cells=[[a,b,g] for (a,b,_),g in zip(L,gs)]
    lowered=sum(1 for (a,b,g0),g in zip(L,gs) if g<g0)
    Sb=sum(F(b-a,Z)*min(F(g,2**32)-MP,0) for a,b,g in cells)
    Sb0=F(D['info']['Sbase'])
    print('cells',len(cells),'lowered',lowered,'max drop',max(g0-g for (a,b,g0),g in zip(L,gs))/2**32,'Sbase',float(Sb),'was',float(Sb0))
    json.dump(dict(cells=cells,Sbase=str(Sb)),open('refined_seg.json','w'))
