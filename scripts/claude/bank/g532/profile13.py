"""G10: pointwise profile of the Lean ledger wins13 and its gap against the full content, per piece/leaf.
Usage: python -I -X utf8 profile13.py   (prints gain13, thresholds, per-leaf gaps)"""
import re, sys, json, importlib.util
from fractions import Fraction as F
sys.dont_write_bytecode = True
ROOT = "C:/Users/seanl/Documents/Codex/2026-10-11/plea/"
U = ROOT + "work/catalan-uniform/CatalanMeasure/GenD/Uniform/Bank535/"
PROG = ROOT + "outputs/Compatibility programme/"
spec = importlib.util.spec_from_file_location('w9', PROG + 'G532-scope-2026-10-28/profile/wins9.py')
w9 = importlib.util.module_from_spec(spec); spec.loader.exec_module(w9)

def num(s):
    s = s.strip().strip('()').split(':')[0].strip()
    if '/' in s:
        a, b = s.split('/'); return F(int(a)) / F(int(b))
    return F(int(s))
def parse(text, name):
    m = re.search(r'def %s : List KapWindow :=\s*\[(.*?)\]\s*\n\s*\n' % name, text, re.S)
    if not m: m = re.search(r'def %s : List KapWindow :=\s*\[(.*?)\]\s*\n' % name, text, re.S)
    out = []
    for g in re.finditer(r'cw\s+(\([^)]*\))\s+(\([^)]*\))\s+(\([^)]*\))\s+(\([^)]*\))', m.group(1)):
        out.append(tuple(num(x) for x in g.groups()))
    return out
def load():
    lW = parse(open(U + 'Ledger8/Merge10.lean', encoding='utf-8').read(), 'lWins')
    wW = parse(open(U + 'Ledger9/Merge11.lean', encoding='utf-8').read(), 'wWins')
    cW = parse(open(U + 'Ledger10/Merge12.lean', encoding='utf-8').read(), 'cWins')
    cp = parse(open(U + 'Ledger10/Merge13.lean', encoding='utf-8').read(), 'cpWins')
    return cp + lW + wW + cW + list(w9.wins9)
def area(w): a, b, c0, c1 = w; return c0 * (b - a) + c1 * (b * b - a * a) / 2
def line_area(c0, c1, a, b): return c0 * (b - a) + c1 * (b * b - a * a) / 2
if __name__ == '__main__':
    W = load(); print(len(W), float(sum(area(w) for w in W)))
    W.sort()
    for w1, w2 in zip(W, W[1:]):
        assert w1[1] <= w2[0], (w1, w2)
