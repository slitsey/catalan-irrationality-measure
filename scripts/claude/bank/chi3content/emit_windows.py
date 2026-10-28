"""Emit Lean for the chi3 M3 windows (B3c) and brute-force check them in Python first."""
import sys, math
from fractions import Fraction as F
sys.dont_write_bytecode = True
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/chi3content')
import gen_windows as G

MARG = 3


def kA(cls, p): return (p + 2) // 3 if cls == 1 else (2 * p + 2) // 3
def kB(p): return (p + 1) // 2
def kA_s(cls): return '(p+2)/3' if cls == 1 else '(2*p+2)/3'


KB_S = '(p+1)/2'


def pos_expr(cls, key, sign):
    """Lean expression and python function for a cut line position, with margin."""
    i, s = key
    mg = (' + %d' % MARG) if sign > 0 else (' - %d' % MARG)
    if i == 1:
        j = int(s)
        return ('r + %d*p%s' % (j, mg), lambda r, m, p: r + j * p + sign * MARG)
    n = math.floor(s)
    fr = s - n
    base = '%d*p' % n
    if fr == 0:
        return (base + mg, lambda r, m, p: n * p + sign * MARG)
    if fr == G.KAP[cls][0]:
        return (base + ' + ' + kA_s(cls) + mg, lambda r, m, p: n * p + kA(cls, p) + sign * MARG)
    if fr == F(1, 2):
        return (base + ' + ' + KB_S + mg, lambda r, m, p: n * p + kB(p) + sign * MARG)
    raise ValueError(key)


def endpoints(cls, tag):
    _, Atag, Akey, Btag, Bkey = tag
    if Atag == 'lo_r':
        a = ('r', lambda r, m, p: r)
    elif Atag == 'lo_p':
        a = ('r + 2*m - p', lambda r, m, p: r + 2 * m - p)
    else:
        a = pos_expr(cls, Akey, +1)
    if Btag == 'hi_m':
        b = ('r + 2*m', lambda r, m, p: r + 2 * m)
    elif Btag == 'hi_p':
        b = ('r + p', lambda r, m, p: r + p)
    else:
        b = pos_expr(cls, Bkey, -1)
    return a, b


def nvals(cls, tag, s, t):
    (ae, af), (be, bf) = endpoints(cls, tag)
    r = 10 ** 6 * 12
    m = r // 4
    res = []
    for w in (F(1, 1000), F(1, 2), F(999, 1000)):
        th = s + (t - s) * w
        pr = th * r
        kAr = (pr + 2) / 3 if cls == 1 else (2 * pr + 2) / 3
        kBr = (pr + 1) / 2

        def ev(e):
            env = dict(r=F(r), m=F(m), p=pr)
            txt = e.replace('(p+2)/3', 'KA').replace('(2*p+2)/3', 'KA').replace('(p+1)/2', 'KB')
            env['KA'] = kAr
            env['KB'] = kBr
            return eval(txt, {}, env)
        a = ev(ae)
        b = ev(be)
        res.append((a, b, pr))
    n0s = {math.floor(a / pr) for a, b, pr in res}
    assert len(n0s) == 1, ('n0', tag, n0s)
    n0 = n0s.pop()
    n3s = {math.floor((a - r) / pr) for a, b, pr in res}
    assert len(n3s) == 1, ('n3', tag, n3s)
    n3 = n3s.pop()
    n1 = min(math.floor((3 * a - 2) / pr) for a, b, pr in res)
    K1 = max(math.ceil((3 * b - 2) / pr) for a, b, pr in res) - n1 - 1
    n2 = min(math.floor((2 * a - 1) / pr) for a, b, pr in res)
    K2 = max(math.ceil((2 * b - 1) / pr) for a, b, pr in res) - n2 - 1
    assert 0 <= K1 <= 4 and 0 <= K2 <= 4, (K1, K2, tag)
    return n0, n1, K1, n2, K2, n3


def lcm(a, b): return a * b // math.gcd(a, b)


def piece_args(s, t, ln):
    D = lcm(ln.i.denominator, ln.s.denominator)
    return (s.numerator, s.denominator, t.numerator, t.denominator, int(ln.i * D), int(ln.s * D), 100 * D, D)


def brute(cls, s, t, ln, tag):
    sn, sd, tn, td, A, B, E, D = piece_args(s, t, ln)
    bad = 0
    usedm3 = 0
    cnt = 0
    if tag == 'old':
        return 0, 0, 0
    for r in list(range(100, 520)) + [3000, 3001, 3002, 3003]:
        for m in range(math.ceil(r / 4), (r + 3) // 4 + 1):
            if not (r <= 4 * m <= r + 3):
                continue
            lo = sn * r // sd
            hi = tn * r // td
            for p in range(lo + 1, hi + 1):
                if p % 6 != cls or p < 5:
                    continue
                cnt += 1
                oldv = 11 * r - 4 * p + 100
                (ae, af), (be, bf) = endpoints(cls, tag)
                a = af(r, m, p)
                b = bf(r, m, p)
                ap = max(a, r + 2 * m - p)
                if ap + 8 <= b:
                    usedm3 += 1
                    assert r <= a <= b and b <= r + 2 * m and b <= r + p, ('win', cls, r, m, p, a, b, tag)
                    for t_ in range(a + 1, b):
                        assert not ((t_ % p == 0) or ((3 * t_ - 2) % p == 0) or ((2 * t_ - 1) % p == 0) or ((t_ - r) % p == 0)), ('cut', cls, r, m, p, a, b, t_, tag)
                    price = 2 * r + (2 * m - (b - ap))
                    assert D * price <= A * r + B * p + E, ('line', cls, r, m, p, price, tag)
                else:
                    if not (D * oldv <= 4 * (A * r + B * p + E)):
                        bad += 1
                        print('FALLBACK FAIL', cls, r, m, p, tag, a, b)
    return cnt, usedm3, bad


def emit_class(cls):
    ps = G.pieces_for_class(cls)
    out = []
    names = []
    for k, (s, t, ln, tag) in enumerate(ps):
        sn, sd, tn, td, A, B, E, D = piece_args(s, t, ln)
        name = 'cov%d_%d' % (cls, k)
        names.append(name)
        cnt, um, bad = brute(cls, s, t, ln, tag)
        print('class', cls, 'piece', k, s, t, 'samples', cnt, 'm3', um, 'bad', bad, file=sys.stderr)
        assert bad == 0
        cl = 'one' if cls == 1 else 'five'
        orx = 'Or.inl' if cls == 1 else 'Or.inr'
        head = ('theorem %s {r m : ℕ} (hm1 : r ≤ 4 * m) (hm2 : 4 * m ≤ r + 3) (hr : 100 ≤ r) :\n'
                '    Covers (%d : ZMod 6) (fun p => (Wn r m p : ℝ)) r (mkPiece %d %d %d %d (%d) (%d) %d %d) :=\n'
                '  CatalanFrames.HybGen.covers_mkM (%d : ZMod 6) (fun p => p %% 6 = %d) (fun p _ h => cls_%s h) (Wn r m) r %d %d %d %d (%d) (%d) %d %d (by norm_num)\n'
                '    (fun p hs ht hpp hcn => by\n'
                '      have hold := W_old_first hm1 hm2 hr (%s hcn) (by omega) (by omega)\n'
                '      have hWW := Wn_le_W r m p\n'
                % (name, cls, sn, sd, tn, td, A, B, E, D, cls, cls, cl, sn, sd, tn, td, A, B, E, D, orx))
        if tag == 'old':
            body = '      omega)\n'
        else:
            (ae, _), (be, _) = endpoints(cls, tag)
            n0, n1, K1, n2, K2, n3 = nvals(cls, tag, s, t)
            body = ('      by_cases hlen : max (%s) (r + 2 * m - p) + 8 ≤ %s\n'
                    '      · have h26 : 26 ≤ p := by omega\n'
                    '        have hpp2 : 26 * p ≤ p * p := Nat.mul_le_mul_right p h26\n'
                    '        have hM : M3Hyp r m p (%s) (%s) :=\n'
                    '          ⟨hpp, by omega, by omega, by omega, by omega, by omega, by omega, by omega,\n'
                    '            nocut_window p r (%s) (%s) (by omega) %d %d %d %d %d %d\n'
                    '              ⟨by omega, by omega⟩ ⟨by omega, by omega⟩\n'
                    '              (by intro i hi1 hi2; interval_cases i <;> omega)\n'
                    '              ⟨by omega, by omega⟩\n'
                    '              (by intro i hi1 hi2; interval_cases i <;> omega) ⟨by omega, by omega⟩⟩\n'
                    '        have he := (Wn_le_e r m p).trans (eExp_le_m3 hM)\n'
                    '        unfold m3price at he\n'
                    '        omega\n'
                    '      · omega)\n') % (ae, be, ae, be, ae, be, n0, n1, K1, n2, K2, n3)
        out.append(head + body)
    plist = ', '.join('mkPiece %d %d %d %d (%d) (%d) %d %d' % piece_args(s, t, ln) for s, t, ln, tag in ps)
    out.append('noncomputable def newFirst%d : List Piece :=\n  [%s]\n' % (cls, plist))
    out.append('theorem newFirst%d_chain : Chain (1/4) newFirst%d := by\n  simp only [newFirst%d, Chain, mkPiece]; norm_num\n' % (cls, cls, cls))
    out.append('theorem newFirst%d_end : lastEnd (1/4) newFirst%d = 1/2 := by\n  simp [newFirst%d, lastEnd, mkPiece] <;> norm_num\n' % (cls, cls, cls))
    alts = ' | '.join(['rfl'] * len(ps))
    ex = ', '.join('%s hm1 hm2 hr' % n for n in names)
    out.append('theorem newFirst%d_covers {r m : ℕ} (hm1 : r ≤ 4 * m) (hm2 : 4 * m ≤ r + 3) (hr : 100 ≤ r) :\n'
               '    ∀ P ∈ newFirst%d, Covers (%d : ZMod 6) (fun p => (Wn r m p : ℝ)) r P := by\n'
               '  intro P hP\n'
               '  simp only [newFirst%d, List.mem_cons, List.mem_nil_iff, or_false] at hP\n'
               '  rcases hP with %s\n'
               '  exacts [%s]\n' % (cls, cls, cls, cls, alts, ex))
    return '\n'.join(out), ps


HEADER = '''module

public import CatalanCore.Uniform.Bank.Chi3Content.Weight

@[expose] public section

/-!
# Class %d: the M3D windows on the first tropical piece (lane B, B3c; generated by
`scripts/claude/bank/chi3content/emit_windows.py`).  The first old piece `11/4 - theta` on
`(1/4, 1/2]` is replaced by %d pieces; every cover is `omega`-checkable affine arithmetic
(`nocut_window` + `M3Hyp`), with the old bound as fallback where the segment is shorter than 8.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.P6 CatalanFrames.P6Hybrid

set_option maxHeartbeats 3200000
set_option maxRecDepth 4000

namespace CatalanCore.Uniform.Bank.Chi3Content

'''

if __name__ == '__main__':
    root = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/CatalanCore/Uniform/Bank/Chi3Content/'
    for cls in (1, 5):
        txt, ps = emit_class(cls)
        open(root + 'Win%d.lean' % cls, 'w', encoding='utf-8').write(
            HEADER % (cls, len(ps)) + txt + '\nend CatalanCore.Uniform.Bank.Chi3Content\n')
        print('wrote class', cls, len(ps), 'pieces')
