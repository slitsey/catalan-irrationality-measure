"""Empirical coverage of the band by the family polygons (independent random sample, large r)."""
import sys, json, random
sys.path.insert(0, 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/scripts/claude/bank/uf')
import plan as P, gen as G
fams = json.load(open(sys.argv[1]))
keys = {tuple(f['key'][:4]) + (tuple(f['key'][4]),) for f in fams if not f.get('infeasible')}
random.seed(1); tot = 0; miss = 0; missed = {}
for _ in range(int(sys.argv[2])):
    r = 2 * random.randint(50, 30000)
    p = random.randint(max(60, 3 * r // 10 + 1), 39 * r // 10)
    if not P.isprime(p) or p % 3 == 0: continue
    S, key, meets = G.structure(r, p)
    tot += 1
    if key not in keys:
        miss += 1; missed[key] = missed.get(key, 0) + 1
print('tested', tot, 'uncovered', miss, missed)
