"""H13: generate the formal coverage lemma (UFFamily4/CoverRho*.lean): a sample-guided decision tree whose
leaves are checked by Lean (`exact` for a family whose literals are all decided, `omega` for empty branches).
Usage: cover.py FAMS.json OUTDIR [RMAX]"""
import sys, os, re, random, json
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import regs, plan as P

GLOBAL = {'hr', 'hp3', 'hlo', 'hhi', 'hp60'}
KNOWN = {'0 < r'}
B3PRE = 'base3 ((3 * r + 9) / 20) r p '


def split_rel(t):
    if '≤' in t:
        a, b = t.split('≤'); return a.strip(), '≤', b.strip()
    a, b = t.split('<'); return a.strip(), '<', b.strip()


def lit_of(text):
    x, op, y = split_rel(text)
    if op == '≤': return (('le', x, y), True)
    return (('le', y, x), False)          # x < y  <=>  not (y <= x)


def split_b3(s):
    rest = s[len(B3PRE):]
    toks = []; depth = 0; cur = ''
    for ch in rest:
        if ch == ' ' and depth == 0:
            if cur: toks.append(cur); cur = ''
            continue
        cur += ch
        if ch == '(': depth += 1
        if ch == ')': depth -= 1
    if cur: toks.append(cur)
    assert len(toks) == 2, (s, toks)
    return toks


def compile_expr(s):
    return compile(regs.pyexpr(s), 'e', 'eval')


def evaluator(a):
    _, x, y = a
    def mk(s):
        if s.startswith('base3'):
            t0, tv = split_b3(s); c0, cv = compile_expr(t0), compile_expr(tv)
            def f(r, p):
                env = dict(r=r, p=p)
                return P.base3_exact((3 * r + 9) // 20, r, p, eval(c0, {}, env), eval(cv, {}, env))
            return f
        c = compile_expr(s)
        return lambda r, p: eval(c, {}, dict(r=r, p=p))
    fx, fy = mk(x), mk(y)
    return lambda r, p: fx(r, p) <= fy(r, p)


def fam_lits(F):
    lin, cmps = regs.fields_of(F)
    lits = []
    for n, t in lin:
        if n in GLOBAL or t in KNOWN: continue
        lits.append(lit_of(t))
    for n, op, (a0, a1), (b0, b1) in cmps:
        lits.append(lit_of(f"{B3PRE}{a0} {a1} {op} {B3PRE}{b0} {b1}"))
    return lits


def sample_points(rmax):
    pts = []
    for r in range(2, 700, 2):
        for p in range(max(60, 3 * r // 10 + 1), 39 * r // 10 + 1):
            if p % 2 == 1 and p % 3 != 0 and 3 * r < 10 * p <= 39 * r: pts.append((r, p))
    random.seed(7)
    for r in range(700, rmax, 2):
        lo, hi = max(60, 3 * r // 10 + 1), 39 * r // 10
        for _ in range(60):
            p = random.randint(lo, hi)
            if p % 2 == 1 and p % 3 != 0 and 3 * r < 10 * p <= 39 * r: pts.append((r, p))
    return pts


def main():
    fams_json = regs.load(sys.argv[1]); outdir = sys.argv[2]
    rmax = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
    os.makedirs(outdir, exist_ok=True)
    pts = sample_points(rmax)
    fams = [regs.Fam(f) for f in fams_json]
    lits = [fam_lits(f) for f in fams_json]
    rhos = [f['key'][0] for f in fams_json]
    ev = {}
    allbits = (1 << len(pts)) - 1

    def atom_bits(a):
        if a not in ev:
            e = evaluator(a); b = 0
            for i, (r, p) in enumerate(pts):
                if e(r, p): b |= (1 << i)
            ev[a] = b
        return ev[a]
    cov = []
    for k, F in enumerate(fams):
        b = 0
        for i, (r, p) in enumerate(pts):
            if F.holds(r, p): b |= (1 << i)
        cov.append(b)
    rho_bits = {1: 0, 2: 0}
    for i, (r, p) in enumerate(pts): rho_bits[p % 3] |= (1 << i)
    out_lines = {1: [], 2: []}
    stats = dict(leaf=0, empty=0, nodes=0)
    counter = [0]

    def lit_bits(l):
        a, s = l
        b = atom_bits(a)
        return b if s else (allbits & ~b)

    def leaf_text(k, path):
        lin, cmps = regs.fields_of(fams_json[k])
        names = []
        for n, t in lin:
            if n in GLOBAL: names.append(n)
            elif t in KNOWN: names.append('hr0')
            else:
                a, s = lit_of(t); names.append(path[a][1])
        for n, op, (a0, a1), (b0, b1) in cmps:
            a, s = lit_of(f"{B3PRE}{a0} {a1} {op} {B3PRE}{b0} {b1}"); names.append(path[a][1])
        return f"exact ⟨{k}, show F{k}.Reg r p from ⟨{', '.join(names)}⟩⟩"

    lemmas = {1: [], 2: []}
    LIMIT = 45

    def srt(path):
        return sorted(path.items(), key=lambda kv: int(kv[1][1][1:]))

    def hyp_decls(path):
        out = []
        for a, (sign, h) in srt(path):
            _, x, y = a
            out.append(f"({h} : {x} ≤ {y})" if sign else f"({h} : {y} < {x})")
        return out

    def wrap(rho, path, lines, goal, kind, strip=0):
        counter[1] += 1
        nm = f"{kind}{rho}_{counter[1]}"
        hs = hyp_decls(path)
        names = ' '.join(h for a, (s_, h) in srt(path))
        NL = chr(10)
        head = (f"theorem {nm} {{r p : ℕ}} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)" + NL +
                "    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = " + str(rho) + ") (hr0 : 0 < r)" + NL + "    "
                + (NL + "    ").join(hs) + " :" + NL + "    " + goal + " := by" + NL)
        body = NL.join(l[strip:] for l in lines)
        pre = "set_option maxHeartbeats 1600000 in" + NL if kind == 'emp' else ''
        lemmas[rho].append(pre + head + body + NL)
        call = f"hr hp2 hlo hhi hp60 hp3 hr0 {names}"
        return nm, call

    def has_b3(path):
        return any('base3' in a[1] for a in path)

    def emit(rho, S, path, depth, fam_ids):
        ind = '  ' * depth
        if S == 0:
            stats['empty'] += 1
            if has_b3(path):
                nm, call = wrap(rho, path, ["  first | omega | (simp only [base3] at *; omega)"], "False", 'emp')
                return [ind + f"exact absurd ({nm} {call}) id"], 1
            return [ind + "exfalso; omega"], 1
        for k in fam_ids:
            if all(l[0] in path and path[l[0]][0] == l[1] for l in lits[k]):
                stats['leaf'] += 1
                return [ind + leaf_text(k, path)], 1
        best = max(fam_ids, key=lambda k: (S & cov[k]).bit_count())
        if (S & cov[best]).bit_count() == 0:
            stats['empty'] += 1
            return [ind + f"-- UNCOVERED SAMPLE POINTS: {S.bit_count()}", ind + "exfalso; omega"], 1
        und = [l for l in lits[best] if l[0] not in path]
        def score(l):
            t = (S & lit_bits(l)).bit_count(); f = S.bit_count() - t
            pen = 1000000 if 'base3' in l[0][1] else 0
            return pen + max(t, f)
        l = min(und, key=score)
        a = l[0]
        counter[0] += 1
        h = f"h{counter[0]}"
        stats['nodes'] += 1
        _, x, y = a
        lines = [ind + f"rcases le_or_gt ({x}) ({y}) with {h} | {h}"]
        size = 1
        for sign in (True, False):
            p2 = dict(path); p2[a] = (sign, h)
            S2 = S & (atom_bits(a) if sign else (allbits & ~atom_bits(a)))
            sub, sz = emit(rho, S2, p2, depth + 1, fam_ids)
            size += sz
            lines.append(ind + "· " + sub[0].lstrip())
            lines.extend(sub[1:])
        if size > LIMIT and depth > 1:
            nm, call = wrap(rho, path, [l[2 * (depth - 1):] for l in lines], "∃ i, RegOf i r p", 'sub')
            return [ind + f"exact {nm} {call}"], 1
        return lines, size

    counter.append(0)
    for rho in (1, 2):
        ids = [k for k in range(len(fams)) if rhos[k] == rho]
        out_lines[rho], _ = emit(rho, rho_bits[rho], {}, 1, ids)
    print(stats, 'points', len(pts))
    HDR = open(os.path.join(HERE, 'cover_hdr.txt'), encoding='utf-8').read()
    for rho in (1, 2):
        hdr = HDR.replace('@RHO@', str(rho))
        i = hdr.index('/-- Coverage')
        body = (hdr[:i] + "\n".join(lemmas[rho]) + "\n" + hdr[i:] + "\n".join(out_lines[rho])
                + "\n\nend CatalanCore.Uniform.Content.UFFamily4\n")
        open(os.path.join(outdir, f'CoverRho{rho}.lean'), 'w', encoding='utf-8').write(body)


main()
