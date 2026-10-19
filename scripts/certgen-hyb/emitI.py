from hybmirror import *
def iTotL(B, A):
    t = 0
    for p in A:
        row = 0
        for q in B:
            N = (p[0]-q[0])**2 + (p[1]-q[1])**2 + 2**60
            row += q[2] * logLoS(N)
        t += p[2] * row
    return t
lines = []
s1 = [iTotL(LAM, SIG[30*r:30*r+30]) for r in range(10)]
s2 = [iTotL(LAM, LAM[30*r:30*r+30]) for r in range(6)]
print(sum(s1), sum(s2))
out = ["module\n\npublic import CatalanCore.Cert.SigmaHyb.HSymm\npublic import CatalanLambda.Cert.IBound\n\n@[expose] public section\n\n/-! Generated (emitI.py): cross and lambda-lambda energy sums, chunked. -/\nnamespace CatalanCore.Cert.SigmaHyb\n\nopen CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\n"]
out.append("def iTotL (B : List Pt) : List Pt → ℤ\n  | [] => 0\n  | p :: ps => (p.2.2 : ℤ) * iRow p B + iTotL B ps\n\n")
out.append("def sChunk (r : ℕ) : List Pt := (sigmaS.drop (30 * r)).take 30\ndef lChunk (r : ℕ) : List Pt := (lamS.drop (30 * r)).take 30\n\n")
for r in range(10):
    out.append("theorem X1_%d : iTotL lamS (sChunk %d) = (%d : ℤ) := by decide +kernel\n" % (r, r, s1[r]))
for r in range(6):
    out.append("theorem X2_%d : iTotL lamS (lChunk %d) = (%d : ℤ) := by decide +kernel\n" % (r, r, s2[r]))
out.append("\ntheorem sigmaS_chunks' : sigmaS = " + " ++ ".join("sChunk %d" % r for r in range(10)) + " := by decide +kernel\n")
out.append("theorem lamS_chunks : lamS = " + " ++ ".join("lChunk %d" % r for r in range(6)) + " := by decide +kernel\n")
out.append("\nend CatalanCore.Cert.SigmaHyb\n")
open(ROOT + 'work/catalan-thmA/CatalanCore/Cert/SigmaHyb/IData.lean', 'w', encoding='utf-8', newline='\n').write("".join(out))
