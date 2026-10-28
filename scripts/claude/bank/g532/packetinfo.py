"""G10: per packet: affine value p*d - sum w_j r_j in (N,p) from compression.json weights and packet ranks."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys, json
sys.dont_write_bytecode = True
from fractions import Fraction as F
R = "C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/"
PK = None
def packets():
    global PK
    if PK is None: PK = json.load(open(R + 'G-content-closed-form-2026-10-27/data/packets.json'))
    return PK
def comp(leaf):
    return json.load(open(R + 'thin-windows-2026-10-24/complete29/production/%s/compression.json' % leaf))['compression']
def form(d):  # {'1':..,'N':..,'hp':..} -> dict of Fractions
    return {k: F(v) for k, v in d.items()}
def to_Np(f):
    """convert form in (1,N,hp) into (c0, cN, cp) with hp=(p-1)/2"""
    c1, cN, chp = f.get('1', F(0)), f.get('N', F(0)), f.get('hp', F(0))
    return (c1 - chp / 2, cN, chp / 2)   # const + N*cN + p*cp
def info(key):
    P = packets()[key]; leaf = P['leaf']; c = comp(leaf)
    ranks = P['ranks']; ranks = eval(ranks) if isinstance(ranks, str) else ranks
    d = int(P['d'])
    maps = sorted(c['maps'], key=lambda m: m['group_id'])
    cen = to_Np(form(c['central_coefficient']))
    val = [cen[0] * d, cen[1] * d, cen[2] * d]
    ws = []
    for j, m in enumerate(maps):
        r = int(ranks[str(j)] if str(j) in ranks else ranks[j])
        assert r <= m['rank'], (key, j, r, m['rank'])
        w = to_Np(form(m['weight'])); ws.append((m['group_id'], r, m['rank'], w))
        for i in range(3): val[i] -= w[i] * r
    return dict(key=key, leaf=leaf, d=d, n=int(P['n']), val=val, ws=ws, central=cen, interval=P['interval'], knot=P['knot'], dom=c['source_binding']['domain'])
if __name__ == '__main__':
    for k in sys.argv[1:]:
        i = info(k); print(k, 'n', i['n'], 'd', i['d'], 'val const,N,p =', [str(x) for x in i['val']], 'interval', i['interval'], 'ngroups', len(i['ws']))
