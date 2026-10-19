# Stage A: coarse h-cells over legacy fine ray cells with u <= U1 (region A) -- greedy merge + Taylor macros.
import sys, json, time
from hybmirror import *
from multiprocessing import Pool

OUTD = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/'
LAMLST = Lst(LAM)
U1 = F(sys.argv[1]) if len(sys.argv) > 1 else F(12, 100)
MT = F(sys.argv[2]) if len(sys.argv) > 2 else F(22143, 10000)       # target m'
SLACK = F(sys.argv[3]) if len(sys.argv) > 3 else F(3, 10 ** 6)
MPRAY = F(197179, 100000)
GT = MT - MPRAY
YEND = int(3 * U1 * Z)

def okflat(a, b):
    bx = mkbox(a, b)
    return hLB(sig_flat(LAMLST, bx), bx) >= GT + SLACK

def greedy(a):
    # largest b in (a, YEND] with okflat(a, b); fixed minimum width 2^20 units
    if not okflat(a, a + 2 ** 20): return None
    lo = a + 2 ** 20; step = 2 ** 20
    while lo < YEND and okflat(a, min(lo + step, YEND)):
        lo = min(lo + step, YEND); step *= 2
        if lo >= YEND: return YEND
    hi = min(lo + step, YEND)
    while hi - lo > 2 ** 14:
        mid = (lo + hi) // 2
        if okflat(a, mid): lo = mid
        else: hi = mid
    return lo

def macro_job(args):
    boxes, = args
    return macro_choose(LAMLST, boxes, hLB, lambda k, l: l >= GT)

if __name__ == '__main__':
    t0 = time.time()
    print('GT', float(GT), 'YEND', YEND)
    cuts = [0]
    while cuts[-1] < YEND:
        b = greedy(cuts[-1]); assert b is not None, cuts[-1]
        cuts.append(b)
    groups = list(zip(cuts[:-1], cuts[1:]))
    print('coarse cells', len(groups), 'time', time.time() - t0, flush=True)
    boxes = [mkbox(a, b) for a, b in groups]
    for M in (32, 16, 8, 4, 2, 1):
        n = (len(boxes) + M - 1) // M
        todo = [boxes[m * M:(m + 1) * M] for m in range(n)]
        with Pool(6) as pool:
            res = pool.map(macro_job, [(b,) for b in todo], chunksize=4)
        nbad = sum(r is None for r in res)
        print('M', M, 'macros', n, 'failed', nbad, 'time', time.time() - t0, flush=True)
        if nbad == 0: break
    cost = sum(r[0] for r in res)
    lbs = [l for r in res for l in r[5]]
    print('cost units', cost, 'per coarse cell', cost / len(boxes), 'min lb', float(min(lbs)), 'mp_A', float(MPRAY + min(lbs)))
    json.dump(dict(YEND=YEND, M=M, groups=groups, boxes=boxes, macros=[[r[1], r[2], r[3], r[4], [str(l) for l in r[5]]] for r in res], U1=str(U1), MT=str(MT)),
              open(OUTD + 'A.json', 'w'))
