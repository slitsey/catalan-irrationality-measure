# Energy data for SigmaHybS: I_rho of the hybrid list from the scaled-integer lower log bounds, TRIANGULAR (symmetric) row sums,
# cut into cost-balanced chunks (one Lean module each).  Writes IBoundDef.lean, IChunk<k>.lean, IBoundData.lean (the numbers).
import sys, os, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsmirror import *
from multiprocessing import Pool
PTS = pts_sorted(); K = len(PTS)
PAIRS = int(os.environ.get('HS_CHUNK_PAIRS', '27000'))

def qII(p, q): return (p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2 + RHO2
def iRow(p, rest): return sum(q[2] * logLoS(qII(p, q)) for q in rest)
def rowT(r):
    p = PTS[r]
    return p[2] * (p[2] * logLoS(qII(p, p)) + 2 * iRow(p, PTS[r + 1:]))

def chunks():
    out = []; a = 0; acc = 0
    for r in range(K):
        acc += (K - r)
        if acc >= PAIRS or r == K - 1:
            out.append((a, r + 1 - a)); a = r + 1; acc = 0
    return out

def chunk_val(ch):
    a, n = ch
    return sum(rowT(a + i) for i in range(n))

HDR = "module\n\npublic import CatalanCore.Cert.SigmaHybS.%s\n\n@[expose] public section\n\n"
NSP = "namespace CatalanCore.Cert.SigmaHybS" + chr(10) + chr(10) + "set_option maxRecDepth 100000" + chr(10) + "set_option Elab.async false" + chr(10) + chr(10)
END = "\nend CatalanCore.Cert.SigmaHybS\n"
def w(n, s): open(OUTD + n + '.lean', 'w', encoding='utf-8', newline='\n').write(s)

if __name__ == '__main__':
    CH = chunks(); NCH = len(CH)
    with Pool(6) as pool: vals = pool.map(chunk_val, CH)
    tot = sum(vals)
    # float sanity: I(m) = -tot/2^129 ; Irho(wt) = (64/81) I(m)
    Im = F(-tot, 2 ** 129)
    Iwt = F(64, 81) * Im
    IB = F(math.ceil(Iwt * 10 ** 7), 10 ** 7)
    print('chunks', NCH, 'I(m)', float(Im), 'I(wt)', float(Iwt), 'IBound', IB, float(IB), 'json IB', float(F(data()['info']['Ibound'])))
    NL = chr(10)
    defs = ("/-! Generated (scripts/certgen-hybs/genI.py): the triangular energy sum for `I_rho(sigma)` and its chunk tables. -/" + NL + NSP +
        "def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 56" + NL + NL +
        "def iRow (p : Pt) : List Pt → ℤ" + NL + "  | [] => 0" + NL + "  | q :: qs => (q.2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII p q) + iRow p qs" + NL + NL +
        "/-- row `r` of the triangle: the diagonal term and twice the pairs with the later points. -/" + NL +
        "def rowT (L : List Pt) (r : ℕ) : ℤ :=" + NL + "  ((L.getD r (0, 0, 0)).2.2 : ℤ) * (((L.getD r (0, 0, 0)).2.2 : ℤ) * CatalanLambda.Cert.logLoS (qII (L.getD r (0, 0, 0)) (L.getD r (0, 0, 0)))" + NL +
        "    + 2 * iRow (L.getD r (0, 0, 0)) (L.drop (r + 1)))" + NL + NL +
        "def rowsSum (a n : ℕ) : ℤ := ((List.range n).map (fun i => rowT sigH (a + i))).sum" + NL + NL +
        "def NCH : ℕ := %d" % NCH + NL + NL +
        "def chunkLen : ℕ → ℕ" + NL + "".join("  | %d => %d" % (k, n) + NL for k, (a, n) in enumerate(CH)) + "  | _ => 0" + NL + NL +
        "def chunkStart : ℕ → ℕ" + NL + "  | 0 => 0" + NL + "  | k + 1 => chunkStart k + chunkLen k" + NL + NL +
        "def chunkVal : ℕ → ℤ" + NL + "".join("  | %d => (%d : ℤ)" % (k, v) + NL for k, v in enumerate(vals)) + "  | _ => 0" + NL + NL +
        "def cumVal : ℕ → ℤ" + NL + "  | 0 => 0" + NL + "  | k + 1 => cumVal k + chunkVal k" + NL + NL +
        "def ITOT : ℤ := %d" % tot + NL + NL +
        "def IBOUNDS : ℚ := %d / %d" % (IB.numerator, IB.denominator) + NL + END)
    w('IBoundDef', HDR % 'Sigma' + defs)
    G = 3
    NMOD = (NCH + G - 1) // G
    for m in range(NMOD):
        ks = list(range(m * G, min(NCH, (m + 1) * G)))
        w('IChunk%d' % m, HDR % 'IBoundDef' + "/-! Generated (genI.py): rows of triangle chunks %s (one kernel cell each). -/" % ks + NL + NSP +
          "".join("theorem iChunk_%d : rowsSum (chunkStart %d) (chunkLen %d) = chunkVal %d := by decide +kernel" % (k, k, k, k) + NL + NL for k in ks) + END)
    # IBound.lean: patch imports and the chunk table
    import re
    p = OUTD + 'IBound.lean'
    s = open(p, encoding='utf-8').read()
    pat1 = r'(public import CatalanCore\.Cert\.SigmaHybS\.IChunk\d+' + chr(10) + r')+'
    s = re.sub(pat1, ''.join('public import CatalanCore.Cert.SigmaHybS.IChunk%d' % m + NL for m in range(NMOD)), s, count=1)
    pat2 = r'  exacts \[iChunk_0.*?\]' + chr(10)
    s = re.sub(pat2, '  exacts [' + ', '.join('iChunk_%d' % k for k in range(NCH)) + ']' + NL, s, count=1, flags=re.S)
    open(p, 'w', encoding='utf-8', newline=NL).write(s)
    print('chunk modules', NMOD)
    json.dump(dict(chunks=CH, vals=[str(v) for v in vals], tot=str(tot), IBound=str(IB), Iwt=float(Iwt)), open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cfg_I.json'), 'w'))
