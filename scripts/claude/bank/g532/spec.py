"""G10: full packet spec: ranks, exact affine weights (via compression members), central, value form, window checks."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys, json
sys.dont_write_bytecode = True
from fractions import Fraction as F
import packetinfo as PI, rowgen as RG
def spec(key):
    P = PI.packets()[key]; leaf = P['leaf']; comp = PI.comp(leaf)
    s, maps = RG.packet_maps(key)
    pcm = {g['source_map']: g for g in s['point_chain_metadata']}
    cmap = {}
    for m in comp['maps']:
        for sm in m['members']: cmap[sm] = m
    ranks = P['ranks']; ranks = eval(ranks) if isinstance(ranks, str) else ranks
    d = int(P['d']); n = int(P['n'])
    mp = []
    for z in maps:
        j = int(z['compressed_map_index']); mem = z['members']
        assert len(mem) == 1, (key, mem)
        m = cmap[mem[0]]
        wf = PI.form(m['weight'])
        assert PI.form(pcm[mem[0]]['weight']) == wf, (key, j, 'weight mismatch')
        r = int(ranks[str(j)] if str(j) in ranks else ranks[j])
        assert r <= len(z['matrix']) and r <= d
        mp.append(dict(j=j, sm=mem[0], w=wf, r=r))
    assert [x['j'] for x in mp] == list(range(len(mp)))
    cen = PI.form(comp['central_coefficient'])
    to = PI.to_Np
    val = [to(cen)[i] * d for i in range(3)]
    for x in mp:
        w = to(x['w'])
        for i in range(3): val[i] -= w[i] * x['r']
    return dict(key=key, leaf=leaf, n=n, d=d, maps=mp, central=cen, val=val, names=s['coordinate_names'], P=P,
                domain=comp['source_binding']['domain'], zero_maps=comp.get('zero_maps'))
def odd_points(a, b, N0, span=60):
    import math
    for N in range(N0, N0 + span):
        lo = math.floor(a * N) + 1; hi = math.floor(b * N)
        ps = set(range(lo, min(hi, lo + 40) + 1)) | set(range(max(lo, hi - 40), hi + 1))
        for p in sorted(ps):
            if p % 2 == 1: yield N, p
def form_ok(f, a, b, N0):
    """f over (1,N,hp) nonneg at all odd p of the window (integer brute force) -- f given as dict"""
    for N, p in odd_points(a, b, N0):
        hp = (p - 1) // 2
        if f.get('1', 0) + f.get('N', 0) * N + f.get('hp', 0) * hp < 0: return False
    return True
def check_domain(sp, a, b, N0):
    bad = []
    for dm in sp['domain']:
        if dm['name'].startswith('inward'): continue
        if not form_ok(PI.form(dm['form']), a, b, N0): bad.append(dm['name'])
    return bad
def weights_ok(sp, a, b, N0):
    bad = []
    for x in sp['maps']:
        if not form_ok(x['w'], a, b, N0): bad.append(x['j'])
    if not form_ok(sp['central'], a, b, N0): bad.append('central')
    return bad
if __name__ == '__main__':
    for key in sys.argv[1:]:
        sp = spec(key); v = sp['val']
        print(key, 'n', sp['n'], 'd', sp['d'], 'm', len(sp['maps']), 'val', [str(x) for x in v], 'central', sp['central'])
