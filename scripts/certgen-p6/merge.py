# Greedy merge of ray u-cells under the exact Lean baseline check (full corner sum), on the 2^-40 u-grid.
import sys, json, time
sys.path.insert(0, '.')
from p6mirror import *
from multiprocessing import Pool
CELLS = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/claude-2026-10-16/FX-lean-wp/CERTD/hcells_D.json'
MP = F(1883395, 1000000)
UMAX = 3 * Z // 2
SLACK = F(int(sys.argv[1]), 10 ** 6) if len(sys.argv) > 1 else F(0)   # extra margin demanded of merged cells (for the Taylor loss)
def box40(a, b):
    W = F(1, 2 ** 30)
    return (math.floor((-R0 - F(b, Z) - W) * Z), math.ceil((-R0 - F(a, Z) + W) * Z), 3 * a, 3 * b)
def ok(a, b):
    bx = box40(a, b)
    return F(-near_sum(bx, spts), 2 ** 97) - ray_rest(bx) >= MP + SLACK
def greedy(a0, hi):
    # largest b in (a0, hi] with ok(a0,b); assumes ok(a0, a0+1)
    lo_ok = a0 + 1
    if not ok(a0, lo_ok): return None
    step = 1 << 10
    b = lo_ok
    while b < hi:
        nb = min(b + step, hi)
        if ok(a0, nb): b = nb; step <<= 1
        else:
            if step == 1: break
            step >>= 1
            # keep trying with smaller step from b
    return b
def job(args):
    a0, hi = args
    return greedy(a0, hi)
if __name__ == '__main__':
    t = time.time(); a = 0; cells = []
    while a < UMAX:
        b = greedy(a, UMAX)
        assert b is not None, a
        cells.append((a, b)); a = b
    print('merged cells', len(cells), 'time', time.time() - t)
    json.dump(cells, open('merged_cells.json', 'w'))
    ws = [b - a for a, b in cells]
    print(min(ws) / Z, max(ws) / Z)
