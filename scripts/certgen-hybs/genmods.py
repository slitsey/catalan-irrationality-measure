# Generate the SigmaHybS ray / segment / line data modules from final4_tight.json with the exact integer mirror.
# usage: genmods.py ray|seg|line [first_module last_module]    (run under guard.ps1 -Kind python)
import sys, json, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsmirror import *
from multiprocessing import Pool

KIND = sys.argv[1]
D = data()
PTS = pts_sorted()
KX = [p[0] for p in PTS]
MP = F(D['info']['MP']); GMIN = F(D['info']['gmin'])
CPM = 1024          # cells per module
NEARMAX = int(os.environ.get('HS_NEARMAX', '200'))
MSEQ = (64, 32, 16, 8, 4)
if KIND == 'line': MSEQ = (32, 16, 8, 4)
NW = int(os.environ.get('HS_NW', '6'))
PRE = {'ray': 'RayM', 'seg': 'SegM', 'line': 'LineM'}[KIND]

def cells_of(kind):
    if kind == 'ray':
        # x-range recomputed from the y-range with exact integer arithmetic (tube of p = (2 ylo/5, 2 yhi/5) 2^-40, r0 = 7/50, W = 2^-30)
        cs = []
        for r in D['ray']:
            yl, yh = r['box'][2], r['box'][3]
            cs.append((( -7 * Z - 20 * yh - 51200) // 50, -((7 * Z + 20 * yl - 51200) // 50), yl, yh))
        pad = cs[-1]
    elif kind == 'seg':
        cs = [tuple(c) for c in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'refined_seg.json')))['cells']]
        pad = (0, 0, cs[-1][2])        # zero-width cell at 0 with the last threshold (valid at x = 0)
    else:
        cs = [(a, b, 0) for a, b in json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'refined_line.json')))]
        pad = cs[-1]
    n = (len(cs) + CPM - 1) // CPM
    cs = cs + [pad] * (n * CPM - len(cs))
    return cs, n

def work(args):
    kind, cells = args
    if kind == 'ray':
        rests = [rayRest(c) for c in cells]
        return macro_choose(PTS, KX, cells, rests, lambda k: MP)
    rests = [realRest(c) for c in cells]
    boxes = [(c[0], c[1], 0, 0) for c in cells]
    if kind == 'seg':
        thr = lambda k: F(cells[k][2], 2 ** 32)
    else:
        thr = lambda k: GMIN
    return macro_choose(PTS, KX, boxes, rests, thr, y0=0)

def module_text(name, n, M, macros_cells, res, kind):
    PER = CPM // M
    slots = []
    for cs, r in zip(macros_cells, res):
        slots += [r[1], r[2], r[3], r[4]]
        for c in cs:
            if kind == 'ray': slots += list(c)
            else: slots += [c[0], c[1], c[2]]
    if kind == 'ray': call = 'gMacroOK sigH MPRAY %d %sP' % (M, name)
    elif kind == 'seg': call = 'realMacroOKH sigH true 0 %d %sP' % (M, name)
    else: call = 'realMacroOKH sigH false GMINS %d %sP' % (M, name)
    t = ["module\n\npublic import CatalanCore.Cert.SigmaHybS.HDefs\npublic import CatalanCore.Cert.SigmaHybS.Sigma\n\n@[expose] public section\n\n"
         "/-! Generated (scripts/certgen-hybs/genmods.py): %s %d (M=%d, %d macros, %d cells). -/\nnamespace CatalanCore.Cert.SigmaHybS\n\n"
         "set_option maxRecDepth 100000\nset_option Elab.async false\n\ndef %sP : Nat := %d\n\n" % (KIND, n, M, PER, CPM, name, pack(slots))]
    for k in range(PER):
        t.append("theorem %s_j%d : %s %d = true := by decide +kernel\n" % (name, k, call, k))
    t.append("\ntheorem %s_ok : ∀ j < %d, %s j = true := by\n  intro j hj\n  interval_cases j\n  exacts [%s]\n"
             % (name, PER, call, ", ".join("%s_j%d" % (name, k) for k in range(PER))))
    t.append("\nend CatalanCore.Cert.SigmaHybS\n")
    return "".join(t)

if __name__ == '__main__':
    cells, nmod = cells_of(KIND)
    lo = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    hi = int(sys.argv[3]) if len(sys.argv) > 3 else nmod - 1
    cfgf = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'cfg_%s.json' % KIND)
    cfg = json.load(open(cfgf)) if os.path.exists(cfgf) else {'Ms': {}, 'cost': {}, 'minlb': {}}
    t0 = time.time()
    print(KIND, 'cells', len(cells), 'modules', nmod, flush=True)
    with Pool(NW) as pool:
        for n in range(lo, hi + 1):
            cm = cells[n * CPM:(n + 1) * CPM]
            for M in MSEQ:
                macs = [cm[k * M:(k + 1) * M] for k in range(CPM // M)]
                res = pool.map(work, [(KIND, m) for m in macs], chunksize=1)
                if all(r is not None for r in res) and max(r[4] - r[3] for r in res) <= NEARMAX: break
                print('  module', n, 'M', M, 'failed', sum(r is None for r in res), 'maxnear', max((r[4] - r[3]) for r in res if r), flush=True)
            if any(r is None for r in res):
                bad = [(k, [i for i in range(len(m))]) for k, (m, r) in enumerate(zip(macs, res)) if r is None]
                print('MODULE', n, 'HAS FAILING MACROS', [b[0] for b in bad], flush=True)
                cfg.setdefault('bad', {})[str(n)] = [b[0] for b in bad]
                json.dump(cfg, open(cfgf, 'w'))
                continue
            name = PRE + str(n)
            open(OUTD + name + '.lean', 'w', encoding='utf-8', newline='\n').write(module_text(name, n, M, macs, res, KIND))
            cost = sum(r[0] for r in res); minlb = min(min(r[5]) for r in res)
            cfg['Ms'][str(n)] = M; cfg['cost'][str(n)] = cost; cfg['minlb'][str(n)] = float(minlb)
            json.dump(cfg, open(cfgf, 'w'))
            print(name, 'M', M, 'max near', max(r[4] - r[3] for r in res), 'cost', cost, 'minlb', float(minlb), 'time', round(time.time() - t0), flush=True)
