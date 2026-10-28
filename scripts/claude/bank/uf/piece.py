"""H13: template pieces for the thirds UF layer -> Lean `UFBound` lemmas (UFFamily4/PieceDemo*.lean).

  piece.py synth FAMS.json OUT.json [RMAX]   synthetic strip pieces (theta = k/10 .. (k+1)/10, k=3..38):
                                             alpha r + beta p + C dominating the Lean UF price (sampled), as a
                                             stand-in template (the real pieces come from the bank receipts)
  piece.py emit  FAMS.json PIECES.json OUTFILE MODNAME   write the Lean lemmas (omega per family)
Pieces: list of {name, s:[n,d], t:[n,d], alpha:"a/b", beta:"a/b", C:"a/b", depth:int}.
"""
import sys, os, json, math
from fractions import Fraction as F
from math import lcm
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import regs


def synth(fams_path, out, rmax, depth=0):
    fams = [regs.Fam(f) for f in regs.load(fams_path)]
    strips = {k: [] for k in range(3, 39)}
    for r in range(32, rmax + 1, 2):
        for p in range(max(60, (3 * r) // 10 + 1), (39 * r) // 10 + 1):
            if p % 2 == 0 or p % 3 == 0: continue
            for Fm in fams:
                if Fm.holds(r, p):
                    k = (10 * p - 1) // r          # theta in (k/10, (k+1)/10]
                    k = max(3, min(38, (10 * p + r - 1) // r - 1))
                    strips[k].append((r, p, Fm.price(r, p) + depth))
                    break
    pieces = []
    for k, pts in strips.items():
        s, t = F(k, 10), F(k + 1, 10)
        best = None
        for bn in range(-40, 41):                  # beta in units of 1/8 .. : price/r = alpha + beta*theta
            beta = F(bn, 8)
            alpha = max(F(v, r) - beta * F(p, r) for r, p, v in pts)
            alpha = F(math.ceil(alpha * 100), 100) + F(1, 50)
            area = alpha + beta * (s + t) / 2
            if best is None or area < best[0]: best = (area, alpha, beta)
        _, alpha, beta = best
        C = max(0, max(math.ceil(v - alpha * r - beta * p) for r, p, v in pts))
        pieces.append(dict(name=f'k{k}', s=[s.numerator, s.denominator], t=[t.numerator, t.denominator],
                           alpha=str(alpha), beta=str(beta), C=str(C), depth=depth))
        print(k, len(pts), alpha, beta, C, float(best[0]))
    json.dump(pieces, open(out, 'w'))


FAM_N = None


def emit(fams_path, pieces_path, outfile, modname):
    nf = len(regs.load(fams_path))
    pieces = json.load(open(pieces_path))
    L = []
    L.append("module\n\npublic import CatalanCore.Uniform.Content.UFFamily4.Piece\n\n@[expose] public section\n")
    L.append("open CatalanCore CatalanCore.Uniform.Content.UFFamily3\n")
    L.append("namespace CatalanCore.Uniform.Content.UFFamily4\n")
    for pc in pieces:
        s = F(*pc['s']); t = F(*pc['t']); a = F(pc['alpha']); b = F(pc['beta']); c = F(pc['C'])
        D = lcm(a.denominator, b.denominator, c.denominator)
        A, B, Cc = int(a * D), int(b * D), int(c * D)
        sa, sb, ta, tb = s.numerator, s.denominator, t.numerator, t.denominator
        dep = pc['depth']
        nm = pc['name']
        L.append(f"set_option maxHeartbeats 3200000 in\ntheorem piece_{nm} :\n"
                 f"    UFBound {dep} ((({sa} : ℕ) : ℝ) / ({sb} : ℕ)) ((({ta} : ℕ) : ℝ) / ({tb} : ℕ))\n"
                 f"      ((({A} : ℤ) : ℝ) / ({D} : ℕ)) ((({B} : ℤ) : ℝ) / ({D} : ℕ)) ((({Cc} : ℤ) : ℝ) / ({D} : ℕ)) :=\n"
                 f"  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) ({A}) ({B}) ({Cc}) (by\n"
                 f"    intro r p hr hb hs ht i hi\n    obtain ⟨h60, hlo, hhi⟩ := hb\n    match i, hi with")
        for i in range(nf):
            L.append(f"    | {i}, hi =>\n      have hi' : F{i}.Reg r p := hi\n      obtain ⟨⟩ := hi'\n"
                     f"      first\n        | (simp only [baseOf, T0Of, TVOf, F{i}.T0, F{i}.TV, base3]; omega)\n"
                     f"        | (simp only [baseOf, T0Of, TVOf, F{i}.T0, F{i}.TV, base3] at *; omega)")
        L.append(f"    | n + {nf}, hi => exact absurd hi (by simp [RegOf]))\n")
    L.append("end CatalanCore.Uniform.Content.UFFamily4\n")
    open(outfile, 'w', encoding='utf-8').write('\n'.join(L))


if __name__ == '__main__':
    if sys.argv[1] == 'synth':
        synth(sys.argv[2], sys.argv[3], int(sys.argv[4]) if len(sys.argv) > 4 else 800)
    else:
        emit(sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5] if len(sys.argv) > 5 else '')
