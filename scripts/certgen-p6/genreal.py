# Real-axis cells for row D (port of gen_real.py + mirror3.py): SegA, SegB (segment cells on [-r0,0]), LineM (line cells on [-1/64,1])
import sys, json, time
sys.path.insert(0, '.')
from p6mirror import *
from math import isqrt
OUT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
def l_lo(N): return F(logLoS(N), 2 ** 65)
def l_up(N): return F(logUpS(N), 2 ** 65)
def ut_A(xlo, xhi):
    assert xhi <= 0 and xlo >= -Z
    if xhi == 0: F1 = F(0)
    else:
        T1 = -xhi; T2 = -xlo; a = l_lo(T1 * T1); b = l_up(T2 * T2)
        F1 = max(F(T1, Z) * a, F(T1, Z) * b, F(T2, Z) * a, F(T2, Z) * b)
    S1 = F(Z - xhi, Z); Ll = l_lo((Z - xhi) ** 2)
    return 1 + F1 - S1 * Ll
def tlogUB(t1, t2):
    if t1 == 0: return 2 * F(isqrt(t2 * Z) + 1, Z)
    a = l_lo(t1 * t1); b = l_up(t2 * t2)
    return max(-F(t1, Z) * a, -F(t1, Z) * b, -F(t2, Z) * a, -F(t2, Z) * b)
def ut_B(xlo, xhi):
    assert 0 <= xlo <= xhi <= Z
    return 1 + tlogUB(xlo, xhi) + tlogUB(Z - xhi, Z - xlo)
def ut(xlo, xhi): return ut_A(xlo, xhi) if xhi <= 0 else ut_B(xlo, xhi)
def full_sig(xlo, xhi): return F(-near_sum((xlo, xhi, 0, 0), spts), 2 ** 97)
def macro_choose_real(cells, thr_fn):
    xs = min(c[0] for c in cells); xe = max(c[1] for c in cells)
    x0 = (xs + xe) // 2; y0 = 0
    uts = [ut(*c) for c in cells]; fulls = [full_sig(*c) for c in cells]
    for Dd in DS:
        i0, i1 = window(x0, Dd)
        far = spts[:i0] + spts[i1:]
        fd = far_data(x0, y0, far)
        lbs = [sig_lb(x0, y0, i0, i1, fd, (c[0], c[1], 0, 0)) for c in cells]
        if all(thr_fn(k, lbs[k], fulls[k], uts[k]) for k in range(len(cells))):
            return (len(cells) * (i1 - i0) + 2.0 * len(far), x0, y0, i0, i1, [l - u for l, u in zip(lbs, uts)])
    raise Exception("none")
BIAS = 2 ** 62; M = 32
GMIN = F(-14419, 10000); MP = F(1883395, 1000000)
NSEG = int(sys.argv[1]) if len(sys.argv) > 1 else 2048
def pack(slots):
    assert all(abs(v) < BIAS for v in slots)
    return sum((v + BIAS) << (64 * k) for k, v in enumerate(slots))
a0 = math.floor(-R0 * Z); step = -(a0 // NSEG)
assert (NSEG - 1) * step < -a0 <= NSEG * step
seg_cells = [(a0 + i * step, min(a0 + (i + 1) * step, 0)) for i in range(NSEG)]
def lb(c): return full_sig(*c) - ut(*c)
def adapt(lo_, hi_, thr, maxw=2 ** -8):
    out = []; stack = [(lo_, hi_)]
    while stack:
        a, b = stack.pop()
        if (b - a) <= int(maxw * Z) and lb((a, b)) >= thr: out.append((a, b))
        else:
            assert b - a > 1
            m = (a + b) // 2; stack.append((m, b)); stack.append((a, m))
    return sorted(out)
def macro_slots(cells, mode):
    if mode == 'seg': thr = lambda i, lb_, fl, u: lb_ >= fl - F(1, 10 ** 4)
    else: thr = lambda i, lb_, fl, u: lb_ - u >= GMIN
    cost, x0, y0, i0, i1, gs = macro_choose_real(cells, thr)
    sl = [x0, y0, i0, i1]
    for (xl, xh), g in zip(cells, gs):
        sl += [xl, xh, math.floor(g * 2 ** 32) if mode == 'seg' else 0]
    return sl, cost, gs
def work(a):
    cells, mode = a
    return macro_slots(cells, mode)
def write_module(pool, name, cells, mode, G, M=M):
    nmac = len(cells) // M
    res = pool.map(work, [(cells[k * M:(k + 1) * M], mode) for k in range(nmac)])
    slots = []; cost = 0; allg = []
    for sl, c, gs in res: slots += sl; cost += c; allg += gs
    modeS = 'true' if mode == 'seg' else 'false'
    txt = ["module\n\npublic import CatalanCore.Cert.SigmaP6.RealCells\n\n@[expose] public section\n\n/-! Generated (scripts/certgen-p6/genreal.py): %s, %d cells in %d macros of %d. -/\nnamespace CatalanCore.Cert.SigmaP6\n\nset_option maxRecDepth 100000\n\ndef %sP : Nat := %d\n\n" % (name, len(cells), nmac, M, name, pack(slots))]
    for k in range(nmac // 4):
        txt.append("theorem %s_c%d : (List.range 4).all (fun j => realMacroOK %s %s %d %sP (%d + j)) = true := by decide +kernel\n" % (name, k, modeS, G, M, name, 4 * k))
    txt.append("\ntheorem %s_ok : ∀ j < %d, realMacroOK %s %s %d %sP j = true := by\n  have h := chunks_all (fun j => realMacroOK %s %s %d %sP j) %d (by\n    intro k hk\n    interval_cases k\n    exacts [%s])\n  exact h\n" % (name, nmac, modeS, G, M, name, modeS, G, M, name, nmac // 4, ", ".join("%s_c%d" % (name, k) for k in range(nmac // 4))))
    txt.append("\nend CatalanCore.Cert.SigmaP6\n")
    open(OUT + name + '.lean', 'w', encoding='utf-8', newline='\n').write("".join(txt))
    return cost, allg
if __name__ == '__main__':
    from multiprocessing import Pool
    t = time.time()
    pool = Pool(6)
    half = NSEG // 2
    c1, g1 = write_module(pool, 'SegA', seg_cells[:half], 'seg', '0')
    c2, g2 = write_module(pool, 'SegB', seg_cells[half:], 'seg', '0')
    gam = [math.floor(g * 2 ** 32) for g in g1 + g2]
    S = F(0)
    for (a, b), g in zip(seg_cells, gam): S += F(b - a, Z) * min(F(g, 2 ** 32) - MP, 0)
    print('seg cells', NSEG, 'Sbase', float(S), 'cost/cell', (c1 + c2) / NSEG, flush=True)
    line_cells = adapt(-(Z // 64), 0, GMIN) + adapt(0, Z, GMIN)
    while len(line_cells) % (4 * M) != 0:
        k = max(range(len(line_cells)), key=lambda i: line_cells[i][1] - line_cells[i][0])
        a, b = line_cells.pop(k); m = (a + b) // 2; line_cells[k:k] = [(a, m), (m, b)]
    c3, g3 = write_module(pool, 'LineM', line_cells, 'line', '(%d / %d : ℚ)' % (GMIN.numerator, GMIN.denominator), 16)
    print('line cells', len(line_cells), 'min lb', float(min(g3)), 'cost/cell', c3 / len(line_cells), 't', time.time() - t)
    json.dump({'seg': [(a, b, g) for (a, b), g in zip(seg_cells, gam)], 'line': line_cells, 'Sbase': str(S)}, open('real_cells.json', 'w'))
