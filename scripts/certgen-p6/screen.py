import sys, json, time
sys.path.insert(0,'.')
from p6mirror import *
d=json.load(open('C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/claude-2026-10-16/FX-lean-wp/CERTD/hcells_D.json'))
cells=d['ray']; st=int(sys.argv[1]); mp=F(sys.argv[2])
t=time.time(); bad=[]; n=0
for i in range(0,len(cells),st):
    a,b,l=cells[i]; bx=mkbox(F(a),F(b))
    lb=F(-near_sum(bx,spts),2**97)-ray_rest(bx); n+=1
    if lb<mp: bad.append((i,round(a,4),float(lb-mp)))
print(n,len(bad),bad[:25],time.time()-t)
