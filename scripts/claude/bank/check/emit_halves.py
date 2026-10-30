"""Halves content emitter (q=2): LP2-widened catalogue plus prefix branches.
Wraps emit_bank_uf (imported unchanged) with the halves Bank patch of the Codex session (half_content.py).
Usage: emit_halves.py scan | control | emit [nmax]"""
import sys, json
from pathlib import Path
from fractions import Fraction as F
sys.dont_write_bytecode = True
ROOT = Path('C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform')
HERE = Path('C:/Users/seanl/Documents/Codex/2026-10-29/handoff-codex-2026-10-29-halves')
sys.path.insert(0, str(ROOT / 'scripts/claude/bank/check'))
import emit_bank_uf as E
receipt = json.loads((HERE / 'exact-HALF.json').read_text())
price = json.loads((HERE / 'HALF-price-work/prices-strict/prices-m3/q2-a1-alpha3_20.json').read_text())
old_bank = E.CK.Bank
def halves_bank(name, uf):
    if name != 'halves':
        return old_bank(name, uf)
    b = old_bank.__new__(old_bank)
    b.bank = name; b.uf = uf; b.q = 2; b.al = F(3, 20); b.M = 2; b.members = [1]; b.kappas = [F(1, 2)]; b.H = F(13, 5)
    assert not E.CK.TC.MODE['R_json']
    b.rk = dict(q=2, alpha='3/20', cases=[dict(pole_cut='1/2', cells=[])])
    return b
E.CK.Bank = halves_bank
B = dict(q=2, M=2, members=[1], Pbad=4, cF=16, alpha0=F(23, 10), t0=F(1, 1000), alpha0b=F(23, 10), n_min=150,
         lp2w=True, pre_nmax=6,
         D=F(receipt['D_lower']), c=F(receipt['c_upper']), target=F(327, 50),
         lam_rat=F(price['Lambda_LP_M3_rational']), lam_log2=F(price['Lambda_log2']),
         module='CatalanCore.Uniform.Bank.HalvesContent.AutoData',
         path='CatalanCore/Uniform/Bank/HalvesContent/AutoData.lean', ns='CatalanCore.Uniform.Bank.HalvesContent.Auto')
if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'control':
        b = dict(B, lp2w=False, pre_nmax=0)
        print('control Lambda_fin(150) =', E.lam_fin('halves', b, 150))
        print(float(E.lam_fin('halves', b, 150)))
    elif mode == 'scan':
        for k in (0, 1, 2, 3, 4, 6, 8):
            b = dict(B, lp2w=True, pre_nmax=k)
            lf = E.lam_fin('halves', b, 150)
            print('nmax', k, 'mu(n=150)', float(E.mu(b, lf)), flush=True)
        import decimal
        for k in (0, 6):
            b = dict(B, lp2w=True, pre_nmax=k)
            n, mu_ex, sl = E.choose_n('halves', b)
            print('nmax', k, 'exact mu', mu_ex, 'n', n, flush=True)
    elif mode == 'emit':
        b = dict(B, pre_nmax=int(sys.argv[2]))
        if len(sys.argv) > 3: b['target'] = F(sys.argv[3])
        n, mu_ex, slack = E.choose_n('halves', b)
        print('halves n', n, 'mu exact', mu_ex, 'slack', slack, 'target', b['target'], flush=True)
        D, names, used = E.build('halves', b, b.get('windows', E.G.WINDOWS), n)
        wins = sorted({tuple(map(int, w[1:].split('_'))) for w in used if w.startswith('W')})
        D, names, used = E.build('halves', b, wins, n)
        ok, st = E.X.check(D); assert ok, st
        T = E.E.lean_form(D); E.E.unit_check(D, T)
        out = E.emit('halves', b, D, T, wins, n)
        print('windows', wins, 'pieces', {j: len(D['tmpls'][j][1]) for j in D['tmpls']})
        print('Lam_fin', float(D['Lam']), 'mu_fin', float(E.mu(b, D['Lam'])), 'excess', float(E.dec(E.mu(b, D['Lam'])) - mu_ex))
        print('wrote', out)
