# Emit Lean data modules for the hybrid certificate: Data.lean, A*, B*, S*, L* (+ family glue constants).
import sys, json
from hybmirror import *
OUTD = ROOT + 'outputs/claude-2026-10-16/FX-lean-wp/CERTH/'
LEAN = ROOT + 'work/catalan-thmA/CatalanCore/Cert/SigmaHyb/'
BIAS = 2 ** 62
MPM = 8   # macros per module

def pack(slots):
    assert all(abs(v) < BIAS for v in slots)
    return sum((v + BIAS) << (64 * k) for k, v in enumerate(slots))
def z(v): return "(%d : ℤ)" % v if v < 0 else str(v)

def write(name, txt):
    import os
    only = os.environ.get('ONLY')
    if only and not name.startswith(only): return
    open(LEAN + name + '.lean', 'w', encoding='utf-8', newline='\n').write(txt)

def emit_data():
    def lit(pts): return ",\n".join("  (%s, %s, %d)" % (z(X), z(Y), n) for X, Y, n in pts)
    txt = ("module\n\npublic import CatalanLambda.Cert.SigmaSorted\n\n@[expose] public section\n\n"
           "/-! Generated (scripts/certgen-hyb/emit.py): the correction measure `lamS` (180 points, mass 2^29/2^32 = 1/8, sorted by (X,Y)) and the merged list `hybS`. -/\n"
           "namespace CatalanCore.Cert.SigmaHyb\n\nopen CatalanLambda.Cert\n\nset_option maxHeartbeats 4000000 in\n"
           "def lamS : List Pt := [\n" + lit(LAM) + "]\n\nset_option maxHeartbeats 4000000 in\ndef hybS : List Pt := [\n" + lit(HYB) + "]\n\nend CatalanCore.Cert.SigmaHyb\n")
    write('Data', txt)

def family(fam, kind, listname, M, macros, cellsbymacro, extra, chunk=4):
    """macros: list of (x0,y0,i0,i1); cellsbymacro: list of list of cell tuples (5 slots for h/g, 3 for l)."""
    nmac = len(macros)
    nmod = (nmac + MPM - 1) // MPM
    while len(macros) < nmod * MPM:
        macros.append(macros[-1]); cellsbymacro.append(cellsbymacro[-1])
    names = []
    for m in range(nmod):
        slots = []
        for k in range(m * MPM, (m + 1) * MPM):
            slots += list(macros[k])
            for c in cellsbymacro[k]: slots += list(c)
        name = '%s%d' % (fam, m); names.append(name)
        chk = {'h': lambda j: "hMacroOK %s %d %sP (%s)" % (listname, M, name, j),
               'g': lambda j: "gMacroOK %s %s %d %sP (%s)" % (listname, extra, M, name, j),
               'l': lambda j: "lMacroOK %s %s %d %sP (%s)" % (listname, extra, M, name, j)}[kind]
        txt = ["module\n\npublic import CatalanCore.Cert.SigmaHyb.Data\npublic import CatalanCore.Cert.SigmaHyb.HMacro\n\n@[expose] public section\n\n"
               "/-! Generated (scripts/certgen-hyb/emit.py): family %s, module %d (%d macros of %d cells). -/\nnamespace CatalanCore.Cert.SigmaHyb\n\nopen CatalanLambda.Cert\n\nset_option maxRecDepth 100000\n\ndef %sP : Nat := %d\n\n" % (fam, m, MPM, M, name, pack(slots))]
        if chunk == 4:
            for k in range(MPM // 4):
                txt.append("theorem %s_c%d : (List.range 4).all (fun j => %s) = true := by decide +kernel\n" % (name, k, chk("%d + j" % (4 * k))))
            txt.append("\ntheorem %s_ok : ∀ j < %d, %s = true := by\n  have h := chunks_all (fun j => %s) %d (by\n    intro k hk\n    interval_cases k\n    exacts [%s])\n  exact h\n" % (
                name, MPM, chk('j'), chk('j'), MPM // 4, ", ".join("%s_c%d" % (name, k) for k in range(MPM // 4))))
        else:
            for k in range(MPM):
                txt.append("theorem %s_c%d : %s = true := by decide +kernel\n" % (name, k, chk(str(k))))
            txt.append("\ntheorem %s_ok : ∀ j < %d, %s = true := by\n  intro j hj\n  interval_cases j\n  exacts [%s]\n" % (
                name, MPM, chk('j'), ", ".join("%s_c%d" % (name, k) for k in range(MPM))))
        txt.append("\nend CatalanCore.Cert.SigmaHyb\n")
        write(name, "".join(txt))
    return names

def main():
    emit_data()
    info = {}
    # ---- A
    A = json.load(open(OUTD + 'A.json'))
    M = A['M']
    macros = []; cells = []
    boxes = A['boxes']
    for mi, mac in enumerate(A['macros']):
        x0, y0, i0, i1, lbs = mac
        macros.append((x0, y0, i0, i1))
        row = []
        for k, ls in enumerate(lbs):
            b = boxes[mi * M + k] if mi * M + k < len(boxes) else boxes[-1]
            g = int((F(ls) * 2 ** 32).__floor__())
            row.append((b[0], b[1], b[2], b[3], g))
        cells.append(row)
    # pad: macros were built from padded boxes? macro list length = ceil(n/M); last macro boxes shorter -> pad cells
    for row in cells:
        while len(row) < M: row.append(row[-1])
    namesA = family('HA', 'h', 'lamS', M, macros, cells, None)
    info['A'] = dict(M=M, n=len(boxes), names=namesA)
    # ---- B
    B = json.load(open(OUTD + 'B.json'))
    M = B['M']; macros = []; cells = []
    for mi, mac in enumerate(B['macros']):
        x0, y0, i0, i1 = mac
        macros.append((x0, y0, i0, i1))
        row = []
        for k in range(M):
            idx = min(mi * M + k, len(B['boxes']) - 1)
            b = B['boxes'][idx]; row.append((b[0], b[1], b[2], b[3], 0))
        cells.append(row)
    namesB = family("GB", "g", "hybS", M, macros, cells, "(22147 / 10000 : ℚ)", 1)
    info['B'] = dict(M=M, n=len(B['boxes']), names=namesB)
    # ---- S
    S = json.load(open(OUTD + 'S.json'))
    M = S['M']; macros = []; cells = []
    for mi, mac in enumerate(S['macros']):
        x0, y0, i0, i1 = mac
        macros.append((x0, y0, i0, i1))
        row = []
        for k in range(M):
            idx = mi * M + k
            b = S['boxes'][idx]; row.append((b[0], b[1], b[2], b[3], S['gam'][idx]))
        cells.append(row)
    namesS = family('HS', 'h', 'lamS', M, macros, cells, None)
    info['S'] = dict(M=M, n=len(S['boxes']), names=namesS, GRP=S['GRP'], Sbase=S['Sbase'])
    # ---- L
    L = json.load(open(OUTD + 'L.json'))
    M = L['M']; macros = []; cells = []
    for mi, mac in enumerate(L['macros']):
        x0, y0, i0, i1 = mac
        macros.append((x0, y0, i0, i1))
        cells.append([(c[0], c[1], 0) for c in L['cells'][mi * M:(mi + 1) * M]])
    namesL = family('LH', 'l', 'hybS', M, macros, cells, '(-16075 / 10000 : ℚ)')
    info['L'] = dict(M=M, n=len(L['cells']), names=namesL)
    json.dump(info, open(OUTD + 'emit_info.json', 'w'))
    print(json.dumps(info))

main()
