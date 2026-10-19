from hybmirror import *
idx = {p: k for k, p in enumerate(LAM)}
cj = [idx[(X, -Y, n)] for X, Y, n in LAM]
assert all(cj[cj[k]] == k for k in range(len(LAM)))
open(ROOT + 'work/catalan-thmA/CatalanCore/Cert/SigmaHyb/ConjL.lean', 'w', encoding='utf-8', newline='\n').write(
 "module\n\npublic import CatalanCore.Cert.SigmaHyb.HBridge\n\n@[expose] public section\n\n/-! Generated (emitconj.py): conjugation involution on `lamS`. -/\nnamespace CatalanCore.Cert.SigmaHyb\n\ndef conjIdxL : List ℕ := [%s]\n\nend CatalanCore.Cert.SigmaHyb\n" % ", ".join(map(str, cj)))
