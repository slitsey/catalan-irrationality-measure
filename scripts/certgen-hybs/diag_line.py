from hsmirror import *
import sys
D=data(); PTS=pts_sorted(); GM=F(D['info']['gmin'])
from multiprocessing import Pool
def f(c):
    a,b=c
    return float(F(-near_sum((a,b,0,0),PTS),2**97)-realRest((a,b))-GM)
if __name__=='__main__':
    L=[tuple(c) for c in D['line']]
    with Pool(6) as p: r=p.map(f,L,chunksize=50)
    bad=[(i,x) for i,x in enumerate(r) if x<0]
    print(len(L), 'bad', len(bad), 'min margin', min(r), bad[:10])
    import collections
    print('hist', sorted(r)[:10])
