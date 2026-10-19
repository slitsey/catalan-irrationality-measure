import sys, json
sys.path.insert(0,'.')
from genray import *
cells = json.load(open(CELLS))['ray']
boxes = [mkbox(F(a), F(b)) for a, b, l in cells]
for mi in range(288, 320):
    bs = boxes[mi*M:mi*M+M]; bs = bs + [bs[-1]] * (M - len(bs))
    c = macro_choose(bs, ray_rest, MP)
    if c[4]-c[3] > 100:
        print('macro', mi, 'near', c[4]-c[3], 'u range', cells[mi*M][0], cells[min(mi*M+M-1,len(cells)-1)][1])
        for k,b in enumerate(bs):
            m = F(-near_sum(b, spts), 2**97) - ray_rest(b) - MP
            print(k, round(cells[mi*M+k][0],6), round(cells[mi*M+k][1]-cells[mi*M+k][0],7), float(m))
        break
