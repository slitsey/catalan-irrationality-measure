import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/g532')
from fractions import Fraction as F
import packetinfo as PI, gaps13 as G, profile13 as P
pcs = G.pieces()
def leaf_pieces(leaf): return [(a, b, c0, c1) for (lf, a, b, c0, c1) in pcs if lf == leaf and (c0 or c1)]
if __name__ == '__main__':
    for leaf in sys.argv[1:]:
        print(leaf)
        for (a, b, c0, c1) in leaf_pieces(leaf): print('  piece', a, b, 'K=', c0, '+', c1, 'x')
        for k, p in PI.packets().items():
            if p['leaf'] == leaf:
                i = PI.info(k); v = i['val']
                print('  packet', k, 'n', i['n'], 'd', i['d'], 'K= %s + %s x  const %s' % (v[1], v[2], v[0]), 'iv', i['interval'])
