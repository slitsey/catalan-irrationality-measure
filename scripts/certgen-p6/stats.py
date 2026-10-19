import sys, json
sys.path.insert(0,'.')
from genray import *
cells = json.load(open(CELLS))['ray']
boxes = [mkbox(F(a), F(b)) for a, b, l in cells]
nmac = (len(boxes) + M - 1) // M
res=[]
for mi in range(nmac):
    bs = boxes[mi*M:mi*M+M]; bs = bs + [bs[-1]] * (M - len(bs))
    c = macro_choose(bs, ray_rest, MP); res.append(c)
for n in range(13):
    ws=[r[4]-r[3] for r in res[n*32:(n+1)*32]]
    print(n, 'u~', cells[n*1024][0], 'max near', max(ws), 'avg', sum(ws)/len(ws))
