"""H13: dry-run planner for any UF bank (no Lean data generated).

Usage: plan_bank.py BANK [RMAX]      (BANK in banks.BANKS)
Samples the banked band (r even, p prime >= P0), groups (r, p) into polygons
(rho, jm, j1, br, meets) exactly as gen.plan does for thirds, picks the best feasible J-window run
by base3_exact, and prints the polygon / family counts and the number of distinct start types
(= LU records) and ordered type pairs (= kill pairs).  Negative control: `plan_bank.py thirds`
reproduces 41 polygons / 52 families.
"""
import sys, os, collections
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import plan as P
import banks as BK
C = P.C


def sig(B, rho, A, Bb, cache={}):
    key = (B['name'], rho, A, Bb)
    if key not in cache:
        q, o = B['q'], B['o']
        nodes = [(A - j, Bb - q * j) for j in range(1, A + 1)]
        items = tuple((a1 - A, C.cval(1, q, o, rho, a1, a2), C.cval(2, q, o, rho, a1, a2)) for a1, a2 in nodes)
        cache[key] = (items, C.cval(1, q, o, rho, A, Bb))
    return cache[key]


def run(B, rmax):
    polys = collections.OrderedDict()
    pairs = set(); types = set()

    def sweep(rs):
        for r in rs:
            plo, phi = BK.band(B, r)
            for p in range(plo, phi + 1):
                if not P.isprime(p) or p <= B['q']: continue
                S = BK.run_structure(B, r, p)
                m, N0, rho = S['m'], S['N0'], S['rho']
                runs = S['runs']
                meets = tuple(bool(R['start'] <= R['end'] and R['start'] < N0) for R in runs)
                br = (B['q'] * r - B['o']) // p if meets[0] else None
                key = (rho, S['jm'], S['j1'], br, meets)
                cands = []
                for i, R in enumerate(runs):
                    if not meets[i]: continue
                    J = sig(B, rho, *R['stype'])
                    ok = all(sig(B, rho, *runs[k]['stype']) != J for k in range(3) if k != i and meets[k])
                    cands.append(dict(i=i, ok=ok, base=P.base3_exact(m, r, p, R['start'], R['end'])))
                feas = [c for c in cands if c['ok']]
                e = polys.setdefault(key, dict(n=0, best=collections.Counter(), ex=(r, p)))
                e['n'] += 1
                for R in runs: types.add((rho,) + tuple(R['stype']))
                if feas:
                    b = min(feas, key=lambda c: (c['base'], c['i']))
                    e['best'][b['i']] += 1
                    for k in range(3):
                        if meets[k] and k != b['i']: pairs.add((rho, runs[b['i']]['stype'], runs[k]['stype']))
                else:
                    e['best'][-1] += 1
    sweep(range(max(2, B['P0'] // 2), min(1200, rmax), 2))
    sweep(range(1200, rmax, 26))
    nfam = sum(len([w for w in e['best'] if w >= 0]) for e in polys.values())
    infeas = {k: e for k, e in polys.items() if -1 in e['best']}
    return polys, nfam, pairs, types, infeas


if __name__ == '__main__':
    B = BK.BANKS[sys.argv[1]]
    rmax = int(sys.argv[2]) if len(sys.argv) > 2 else 3000
    polys, nfam, pairs, types, infeas = run(B, rmax)
    print(B['name'], 'q', B['q'], 'o', B['o'], 'c', B['c'], 'band', B['left'], B['right'], 'P0', B['P0'])
    print('polygons', len(polys), 'families', nfam, 'start types', len(types), 'ordered kill pairs', len(pairs),
          'polygons with infeasible points', len(infeas))
