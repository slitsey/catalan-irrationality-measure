"""G10: original-label chart rows for any packet, from compile_cell of the leaf's cell + the packet's own
point_chain_metadata row labels.  Validated: rowspace of each map's label rows == stored map matrix."""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys, json, re, glob
sys.dont_write_bytecode = True
from fractions import Fraction as Q
R = "C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/Compatibility programme/"
TW = R + "thin-windows-2026-10-24/"
sys.path.insert(0, TW + "complete13")
import window_ir as W
import raw_cell as RC
LOWNAME = None

def packet_file(key):
    leaf, side = key.split('|')
    if side in ('left', 'right'): return TW + 'complete29/production/%s/%s.json' % (leaf, side)
    return TW + 'complete30/production/%s/%s-normal.json' % (leaf, side)
def leaf_cell(leaf):
    rc = json.load(open(TW + 'complete29/production/%s/receipt.json' % leaf))
    return json.load(open(rc['binding_file'].replace('binding.json', 'binding.json')))  # binding -> leaf_file
def leaf_json(leaf):
    b = json.load(open(TW + 'complete29/production/%s/binding.json' % leaf))
    return json.load(open(b['leaf_file']))
def compile_leaf(leaf):
    lj = leaf_json(leaf); cell = lj['cell']
    wit = lj['rational_witness']; val = {'N': Q(wit['N']), 'hp': Q(wit['hp'])}
    def ev(f):
        f = W.form(f); return sum(v * (1 if k == '1' else val[k]) for k, v in f.items())
    def leq(a, b, label): return ev(a) <= ev(b)
    out = RC.compile_cell(cell, leq)
    return out, lj
def rowvec(coeff, names):
    v = [Q(0)] * len(names)
    for k, c in coeff.items():
        if k not in names: raise KeyError(k)
        v[names.index(k)] += Q(c)
    return v
def label_rows(key, cc, names, labels):
    """labels -> rational rows over `names` (the packet coordinate_names)"""
    cond = {c['name']: c for c in cc['spec']['conditions']}
    lowname = [n for n in names if n.startswith('@low:')]
    out = []
    for lab in labels:
        m = re.match(r'(.+)\.(sourcejet|source_top)$', lab)
        if m:
            out.append(rowvec({m.group(1): 1}, names)); continue
        m = re.match(r'(.+):C_minus\.prefix$', lab)           # e.g. C[-1]:C_minus.prefix
        if m:
            nm = m.group(1); c = cond[nm + ':C_minus']
            out.append(rowvec(c['coeff'], names)); continue
        if lab == 'left_centre:centre.prefix':
            out.append(rowvec(cond['left_centre:centre']['coeff'], names)); continue
        m = re.match(r'raw\[(\d+),(\d)\]\.(prefix|degree|graph|slack_top)$', lab)
        if m:
            c = cond['raw[%s,%s]' % (m.group(1), m.group(2))]
            v = rowvec(c['coeff'], [n for n in names]) if True else None
            ln = '@low:raw[%s,%s]' % (m.group(1), m.group(2))
            if m.group(3) == 'graph':
                v[names.index(ln)] += Q(-1)
            if m.group(3) == 'slack_top':
                v = rowvec({ln: 1}, names)
            out.append(v); continue
        m = re.match(r'(bottom_virtual|top_virtual):(E_degree|F_degree|E_zero)\.(degree|prefix)$', lab)
        if m:
            nm = m.group(1) + ':' + m.group(2)
            out.append(rowvec(cond[nm]['coeff'], names)); continue
        raise ValueError(lab)
    return out
def rank(rows, ncol=None):
    A = [r[:] for r in rows]; rk = 0
    ncol = ncol or (len(A[0]) if A else 0)
    for c in range(ncol):
        p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for i in range(len(A)):
            if i != rk and A[i][c] != 0:
                q = A[i][c] / A[rk][c]; A[i] = [x - q * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk
def packet_maps(key):
    s = json.load(open(packet_file(key)))
    maps = sorted(s['active_maps'] + s['dropped_zero_weight_maps'], key=lambda z: int(z['compressed_map_index']))
    return s, maps
def build(key, verbose=True):
    leaf = key.split('|')[0]
    cc, lj = compile_leaf(leaf)
    s, maps = packet_maps(key)
    names = s['coordinate_names']
    meta = {g['source_map']: g for g in s['point_chain_metadata']}
    res = []
    ok = True
    for z in maps:
        j = int(z['compressed_map_index']); mem = z['members']
        labels = []
        for g in mem: labels += meta[g]['row_labels']
        rows = label_rows(key, cc, names, labels)
        M = [[Q(x) for x in r] for r in z['matrix']]
        r1, r2, r3 = rank(rows), rank(M), rank(rows + M)
        eq = (r1 == r2 == r3)
        if not eq: ok = False
        if verbose: print(' map', j, 'members', mem, 'rows', len(rows), 'ranks', r1, r2, r3, 'EQUAL' if eq else 'DIFF')
        res.append(dict(j=j, members=mem, rows=rows, ok=eq))
    return res, names, ok
if __name__ == '__main__':
    for key in sys.argv[1:]:
        print(key)
        try:
            res, names, ok = build(key)
            print(' ALL OK' if ok else ' MISMATCH')
        except Exception as e:
            import traceback; traceback.print_exc()
