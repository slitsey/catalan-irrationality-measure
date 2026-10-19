# Stage S (segment coarse h-cells over the 2816 legacy cells) and L (line cells on [0,1], list HYB).
import sys, json, time
from hybmirror import *
from multiprocessing import Pool
OUTD = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/'
LAMLST = Lst(LAM); HYBLST = Lst(HYB)
MT = F(json.load(open(OUTD + 'A.json'))['MT'])
GL = F(sys.argv[1]) if len(sys.argv) > 1 else F(-16093, 10000)   # line threshold
GRP = 4
sc = legacy_seg()
def hseg_job(args):
    boxes, = args
    flat = [hLB(sig_flat(LAMLST, b), b) for b in boxes]
    return macro_choose(LAMLST, boxes, hLB, lambda k, l: l >= flat[k] - F(2, 10 ** 7))
def lbox_job(args):
    cells, = args
    flat = [sig_flat(HYBLST, (a, b, 0, 0)) - ut_B(a, b) - uexAxisUp(a, b) for a, b in cells]
    xs = min(c[0] for c in cells); xe = max(c[1] for c in cells); x0 = (xs + xe) // 2
    for Dd in DS:
        i0, i1 = window(HYBLST, x0, Dd)
        far = HYB[:i0] + HYB[i1:]
        fd = far_data(x0, 0, far)
        lbs = [lLB(HYBLST, x0, 0, i0, i1, fd, a, b) for a, b in cells]
        if all(l >= GL for l in lbs): return (len(cells) * (i1 - i0) + 2.0 * len(far), x0, 0, i0, i1, lbs)
    return None
def line_flat_ok(a, b):
    return sig_flat(HYBLST, (a, b, 0, 0)) - ut_B(a, b) - uexAxisUp(a, b) >= GL + F(1, 10 ** 6)
def adapt(a, b):
    out = []; stack = [(a, b)]
    while stack:
        lo, hi = stack.pop()
        ok = (hi - lo) <= 2 ** 32 and (hi != Z or lo >= 3 * 2 ** 38) and line_flat_ok(lo, hi)
        if ok: out.append((lo, hi))
        else:
            m = (lo + hi) // 2; stack.append((m, hi)); stack.append((lo, m))
    return sorted(out)
if __name__ == '__main__':
    t0 = time.time()
    # ---- segment
    nco = len(sc) // GRP
    boxes = [(sc[GRP * j][0], sc[GRP * j + GRP - 1][1], 0, 0) for j in range(nco)]
    for j in range(nco):
        for k in range(GRP): assert boxes[j][0] <= sc[GRP * j + k][0] and sc[GRP * j + k][1] <= boxes[j][1]
    for M in (32, 16, 8):
        n = nco // M
        todo = [boxes[m * M:(m + 1) * M] for m in range(n)]
        with Pool(6) as pool:
            res = pool.map(hseg_job, [(b,) for b in todo])
        nbad = sum(r is None for r in res); print('seg M', M, 'failed', nbad, flush=True)
        if nbad == 0: break
    assert nco % M == 0
    gam = [int((l * 2 ** 32).__floor__()) for r in res for l in r[5]]
    cost = sum(r[0] for r in res); print('seg h cost units', cost)
    S = F(0)
    for i, (a, b, g) in enumerate(sc):
        S += F(b - a, Z) * min(F(g + gam[i // GRP], 2 ** 32) - MT, 0)
    print('Sbase (unscaled sum)', float(S), 'S_h = 2*Sbase', float(2 * S), flush=True)
    json.dump(dict(GRP=GRP, M=M, boxes=boxes, gam=gam, macros=[[r[1], r[2], r[3], r[4]] for r in res], Sbase=str(S)), open(OUTD + 'S.json', 'w'))
    # ---- line
    cells = adapt(0, Z)
    print('line cells', len(cells), 'time', time.time() - t0, flush=True)
    for M in (16, 8, 4):
        while len(cells) % (4 * M): 
            k = max(range(len(cells)), key=lambda i: cells[i][1] - cells[i][0]); a, b = cells.pop(k); m = (a + b) // 2; cells[k:k] = [(a, m), (m, b)]
        n = len(cells) // M
        todo = [cells[m * M:(m + 1) * M] for m in range(n)]
        with Pool(6) as pool:
            res = pool.map(lbox_job, [(c,) for c in todo])
        nbad = sum(r is None for r in res); print('line M', M, 'n', n, 'failed', nbad, flush=True)
        if nbad == 0: break
    lbs = [l for r in res for l in r[5]]
    print('line cost', sum(r[0] for r in res), 'min lb', float(min(lbs)), 'cells', len(cells))
    json.dump(dict(M=M, cells=cells, macros=[[r[1], r[2], r[3], r[4]] for r in res], gmin=str(min(lbs))), open(OUTD + 'L.json', 'w'))
