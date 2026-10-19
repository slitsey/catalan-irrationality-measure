import sys, json
sys.path.insert(0,'.')
import genray as g
from genray import *
cells = json.load(open(CELLS))['ray']
boxes = [mkbox(F(a), F(b)) for a, b, l in cells]
for MM in (16, 8):
    nmac = (len(boxes) + MM - 1) // MM
    res=[]
    for mi in range(nmac):
        bs = boxes[mi*MM:mi*MM+MM]; bs = bs + [bs[-1]] * (MM - len(bs))
        res.append(macro_choose(bs, ray_rest, MP))
    ws=[r[4]-r[3] for r in res]
    tot=sum(r[0] for r in res)
    print(MM, 'max near', max(ws), 'cost/cell', tot/(nmac*MM), 'macros with near>150:', sum(1 for w in ws if w>150))
