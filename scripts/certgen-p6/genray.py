# Ray macros for row D: reads the pcert (Arb) cells, chooses Taylor windows, writes RayM<k>.lean.
# Every module holds CPM = 1024 cells; its macro size M is 32, or 16/8 when a 32-macro needs a huge near window
# (huge windows blow the kernel memory budget).
import sys, json, time
sys.path.insert(0, '.')
from p6mirror import *
from multiprocessing import Pool
OUT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
CELLS = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/outputs/claude-2026-10-16/FX-lean-wp/CERTD/hcells_T1.8834.json'
MP = F(1883395, 1000000)
CPM = 1024; BIAS = 2 ** 62; NEARMAX = 120
def work(bs):
    return macro_choose(bs, ray_rest, MP)
def pack(slots):
    assert all(abs(v) < BIAS for v in slots)
    return sum((v + BIAS) << (64 * k) for k, v in enumerate(slots))
def mkmod(pool, cellsMod, M):
    todo = [cellsMod[k * M:(k + 1) * M] for k in range(CPM // M)]
    return todo, pool.map(work, todo, chunksize=2)
if __name__ == '__main__':
    cells = json.load(open(CELLS))['ray']
    boxes = [mkbox(F(a), F(b)) for a, b, l in cells]
    nmod = (len(boxes) + CPM - 1) // CPM
    boxes += [boxes[-1]] * (nmod * CPM - len(boxes))     # pad with the last cell
    cfg = dict(nmod=nmod, ncell=nmod * CPM, CPM=CPM, Ms=[])
    t = time.time(); tot = 0
    with Pool(6) as pool:
        for n in range(nmod):
            cm = boxes[n * CPM:(n + 1) * CPM]
            for M in (32, 16, 8, 4):
                todo, res = mkmod(pool, cm, M)
                if all(r is not None for r in res) and max(r[4] - r[3] for r in res) <= NEARMAX: break
            assert all(r is not None for r in res)
            cfg['Ms'].append(M); PER = CPM // M; tot += sum(r[0] for r in res)
            slots = []
            for bs, c in zip(todo, res):
                slots += [c[1], c[2], c[3], c[4]]
                for b in bs: slots += list(b)
            name = 'RayM%d' % n
            txt = ["module\n\npublic import CatalanCore.Cert.SigmaP6.RayTaylor\n\n@[expose] public section\n\n/-! Generated (scripts/certgen-p6/genray.py): row-D ray macros of module %d (M=%d, %d macros). -/\nnamespace CatalanCore.Cert.SigmaP6\n\nset_option maxRecDepth 100000\n\ndef %sP : Nat := %d\n\n" % (n, M, PER, name, pack(slots))]
            for k in range(PER // 4):
                txt.append("theorem %s_c%d : (List.range 4).all (fun j => rayMacroOK MPRAY %d %sP (%d + j)) = true := by decide +kernel\n" % (name, k, M, name, 4 * k))
            txt.append("\ntheorem %s_ok : ∀ j < %d, rayMacroOK MPRAY %d %sP j = true := by\n  have h := chunks_all (fun j => rayMacroOK MPRAY %d %sP j) %d (by\n    intro k hk\n    interval_cases k\n    exacts [%s])\n  exact h\n" % (name, PER, M, name, M, name, PER // 4, ", ".join("%s_c%d" % (name, k) for k in range(PER // 4))))
            txt.append("\nend CatalanCore.Cert.SigmaP6\n")
            open(OUT + name + '.lean', 'w', encoding='utf-8', newline='\n').write("".join(txt))
            print('module', n, 'M', M, 'max near', max(r[4] - r[3] for r in res), flush=True)
    json.dump(cfg, open('ray_cfg.json', 'w'))
    print('modules', nmod, 'Ms', cfg['Ms'], 'cost units per cell', tot / (nmod * CPM), 'time', time.time() - t)
