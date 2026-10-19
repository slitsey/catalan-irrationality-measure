# Stage B: fresh hybrid ray cells (list HYB) from y = YEND to y = 4.5 (u = 3/2) with threshold MT.
import sys, json, time
from hybmirror import *
from multiprocessing import Pool
OUTD = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/'
HYBLST = Lst(HYB)
A = json.load(open(OUTD + 'A.json'))
YEND = A['YEND']; MT = F(A['MT'])
SLACK = F(sys.argv[1]) if len(sys.argv) > 1 else F(3, 10 ** 6)
YTOP = 9 * Z // 2
def okflat(a, b):
    bx = mkbox(a, b)
    return boxLBH(sig_flat(HYBLST, bx), bx) >= MT + SLACK
def greedy(a):
    w0 = 2 ** 22
    if not okflat(a, a + w0): return None
    lo = a + w0; step = w0
    while lo < YTOP and okflat(a, min(lo + step, YTOP)):
        lo = min(lo + step, YTOP); step *= 2
        if lo >= YTOP: return YTOP
    hi = min(lo + step, YTOP)
    while hi - lo > 2 ** 16:
        mid = (lo + hi) // 2
        if okflat(a, mid): lo = mid
        else: hi = mid
    return lo
def macro_job(args):
    boxes, = args
    return macro_choose(HYBLST, boxes, boxLBH, lambda k, l: l >= MT)
if __name__ == '__main__':
    t0 = time.time()
    cuts = [YEND]
    while cuts[-1] < YTOP:
        b = greedy(cuts[-1]); assert b is not None, cuts[-1]
        cuts.append(b)
        if len(cuts) % 20 == 0: print(len(cuts), cuts[-1] / Z / 3, time.time() - t0, flush=True)
    groups = list(zip(cuts[:-1], cuts[1:]))
    print('cells', len(groups), 'time', time.time() - t0, flush=True)
    boxes = [mkbox(a, b) for a, b in groups]
    for M in (32, 16, 8, 4, 2, 1):
        n = (len(boxes) + M - 1) // M
        todo = [boxes[m * M:(m + 1) * M] for m in range(n)]
        with Pool(6) as pool:
            res = pool.map(macro_job, [(b,) for b in todo], chunksize=2)
        nbad = sum(r is None for r in res)
        print('M', M, 'macros', n, 'failed', nbad, flush=True)
        if nbad == 0: break
    cost = sum(r[0] for r in res)
    print('cost units', cost, 'per cell', cost / len(boxes))
    json.dump(dict(YTOP=YTOP, M=M, groups=groups, boxes=boxes, macros=[[r[1], r[2], r[3], r[4]] for r in res]), open(OUTD + 'B.json', 'w'))
