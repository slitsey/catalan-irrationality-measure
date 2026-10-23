# Refine the line cells so that the Lean flat bound (all atoms near, utB + uexAxisUp) clears GMIN; writes refined_line.json
from hsmirror import *
import sys, json
D=data(); PTS=pts_sorted(); GM=F(D['info']['gmin'])
SLACK=F(int(sys.argv[1]),10**9) if len(sys.argv)>1 else F(3,10**6)   # extra slack to leave room for the Taylor far field
from multiprocessing import Pool
def ok(c):
    a,b=c
    return F(-near_sum((a,b,0,0),PTS),2**97)-realRest((a,b)) >= GM+SLACK
def refine(c):
    out=[]; st=[c]
    while st:
        a,b=st.pop()
        if ok((a,b)): out.append((a,b))
        else:
            assert b-a>1
            m=(a+b)//2; st.append((m,b)); st.append((a,m))
    return sorted(out)
if __name__=='__main__':
    L=[tuple(c) for c in D['line']]
    with Pool(6) as p: r=p.map(refine,L,chunksize=20)
    cells=[c for rr in r for c in rr]
    print(len(L),'->',len(cells))
    assert cells[0][0]==0 and cells[-1][1]==Z and all(cells[i][1]==cells[i+1][0] for i in range(len(cells)-1))
    json.dump(cells,open('refined_line.json','w'))
