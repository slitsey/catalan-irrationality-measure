# Port the legacy sigma300 certificate engine (CatalanLambda/Cert/*) to the P6 row-D parameters:
#   rho = 1/2048 (2^60 -> 2^58 in the scaled integer ball), 300 -> 699 points, sigmaS -> sigD, namespace CatalanCore.Cert.SigmaP6.
# Hand-written files (Tail, Final glue, thetaX in Box) are NOT produced here.
import re, sys
SRC = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-repo/CatalanLambda/Cert/'
DST = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
PFX = 'CatalanCore.Cert.SigmaP6.'
MAP = {'RayBox': 'Box', 'SigTaylor': 'Taylor', 'RayTaylor': 'RayTaylor', 'SegLine': 'SegLine', 'RealCells': 'RealCells',
       'Bridge': 'Bridge', 'Symm': 'Symm', 'IBound': 'IBound'}
LEG = ('LogBounds', 'ArctanBounds', 'Tables')
def conv(name, txt):
    out = []
    for ln in txt.split('\n'):
        m = re.match(r'public import CatalanLambda\.Cert\.(\w+)$', ln)
        if m:
            n = m.group(1)
            if n in MAP: ln = 'public import ' + PFX + MAP[n]
            elif n in LEG: pass
            elif n == 'SigmaSorted': ln = 'public import ' + PFX + 'Sigma'
            elif n in ('IBoundData', 'ConjData'): ln = 'public import ' + PFX + n
        out.append(ln)
    t = '\n'.join(out)
    t = t.replace('namespace CatalanLambda.Cert', 'namespace CatalanCore.Cert.SigmaP6\n\nopen CatalanLambda.Cert')
    t = t.replace('end CatalanLambda.Cert', 'end CatalanCore.Cert.SigmaP6')
    t = t.replace('sigmaS', 'sigD')
    t = re.sub(r'(?<![\w.])Decay\.', 'CatalanLambda.Decay.', t)
    t = t.replace('2 ^ 60', '2 ^ 58').replace('1 / 1024', '1 / 2048').replace('(1 : ℝ) / 1024', '(1 : ℝ) / 2048')
    t = t.replace('Fin 300', 'Fin 699').replace('range 300', 'range 699').replace('< 300', '< 699').replace('= 300', '= 699').replace('% 300', '% 699')
    return t
for src, dst in MAP.items():
    t = open(SRC + src + '.lean', encoding='utf-8').read()
    open(DST + dst + '.lean', 'w', encoding='utf-8', newline='\n').write(conv(src, t))
