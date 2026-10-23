# RayGlue.lean and SegLineGlue.lean for SigmaHybS (global cell indexing, geometry / chain checks, S_cert), from cfg_ray/seg/line.json
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hsmirror import *
HERE = os.path.dirname(os.path.abspath(__file__))
NL = chr(10)
CPM = 1024
def cfg(k): return json.load(open(os.path.join(HERE, 'cfg_%s.json' % k)))
def w(n, s): open(OUTD + n + '.lean', 'w', encoding='utf-8', newline=NL).write(s)
P = 'CatalanCore.Cert.SigmaHybS.'

def table(name, ty, vals, default):
    return "def %s : ℕ → %s" % (name, ty) + NL + "".join("  | %d => %s" % (k, v) for k, v in enumerate(vals)) .replace("  | ", NL + "  | ", 0) + NL
def tbl(name, ty, vals, default):
    s = "def %s : ℕ → %s" % (name, ty) + NL
    for k, v in enumerate(vals): s += "  | %d => %s" % (k, v) + NL
    return s + "  | _ => %s" % default + NL + NL

def per_module(prefix, n, fn, args=""):
    s = ""
    for k in range(n):
        s += "theorem %s_geom_%d : (List.range %d).all (fun i => %sGeomCell (%sCellG (%d * %d + i))) = true := by" % (prefix, k, CPM, prefix, prefix, CPM, k) + NL + "  decide +kernel" + NL + NL
    for k in range(n):
        s += "theorem %s_chain_%d : (List.range %d).all (fun i => %sChainCell (%d * %d + i)) = true := by" % (prefix, k, CPM, prefix, CPM, k) + NL + "  decide +kernel" + NL + NL
    s += "theorem %s_geom : ∀ m < %d, (List.range %d).all (fun i => %sGeomCell (%sCellG (%d * m + i))) = true := by" % (prefix, n, CPM, prefix, prefix, CPM) + NL + "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("%s_geom_%d" % (prefix, k) for k in range(n)) + NL + NL
    s += "theorem %s_chain : ∀ m < %d, (List.range %d).all (fun i => %sChainCell (%d * m + i)) = true := by" % (prefix, n, CPM, prefix, CPM) + NL + "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("%s_chain_%d" % (prefix, k) for k in range(n)) + NL + NL
    return s

# ------------------------------------------------------------------ RayGlue
cr = cfg('ray'); NR = len(cr['Ms']); Ms = [cr['Ms'][str(k)] for k in range(NR)]; NRC = NR * CPM
t = "module" + NL + NL + "".join("public import %sRayM%d" % (P, k) + NL for k in range(NR)) + "public import %sBridge" % P + NL + NL
t += "@[expose] public section" + NL + NL + "/-!" + NL + "# Glue for the ray cells: global indexing of the %d modules (%d cells), geometry (the cell box contains the tube of its `u`-interval), chain (cover of `[0,3/2]`)." % (NR, NRC) + NL + "-/" + NL + NL
t += "open Real" + NL + NL + "namespace CatalanCore.Cert.SigmaHybS" + NL + NL + "set_option maxRecDepth 100000" + NL + NL
t += tbl('rayM', 'ℕ', Ms, '1') + tbl('rayP', 'ℕ', ['RayM%dP' % k for k in range(NR)], '0')
t += ("theorem rayAll_ok : ∀ m < %d, ∀ j < %d / rayM m, gMacroOK sigH MPRAY (rayM m) (rayP m) j = true := by" % (NR, CPM) + NL +
      "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("RayM%d_ok" % k for k in range(NR)) + NL + NL +
      "theorem rayM_pos (m : ℕ) : 0 < rayM m := by" + NL + "  unfold rayM; split <;> norm_num" + NL + NL +
      "theorem rayM_dvd (m : ℕ) (hm : m < %d) : rayM m ∣ %d := by" % (NR, CPM) + NL + "  interval_cases m <;> decide" + NL + NL +
      "def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ :=" + NL +
      "  cellBox (rayM (i / %d)) (rayP (i / %d)) ((i %% %d) / rayM (i / %d)) (i %% rayM (i / %d))" % (CPM, CPM, CPM, CPM, CPM) + NL + NL +
      "theorem ray_sound (i : ℕ) (hi : i < %d) (x y : ℝ)" % NRC + NL +
      "    (h1 : ((rayCellG i).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((rayCellG i).2.1 : ℝ) / 2 ^ 40)" + NL +
      "    (h3 : ((rayCellG i).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((rayCellG i).2.2.2 : ℝ) / 2 ^ 40) :" + NL +
      "    (MPRAY : ℝ) ≤ gHR sigH x y :=" + NL +
      "  gMod_sound sigH MPRAY (rayM (i / %d)) (rayP (i / %d)) (%d / rayM (i / %d)) (rayAll_ok (i / %d) (by omega))" % (CPM, CPM, CPM, CPM, CPM) + NL +
      "    ((i %% %d) / rayM (i / %d))" % (CPM, CPM) + NL +
      "    (Nat.div_lt_div_of_lt_of_dvd (rayM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))) (i %% rayM (i / %d))" % CPM +
      " (Nat.mod_lt _ (rayM_pos _)) x y h1 h2 h3 h4" + NL + NL +
      "def rayGeomCell (b : ℤ × ℤ × ℤ × ℤ) : Bool :=" + NL +
      "  decide (b.2.1 < 0 ∧ 0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧" + NL +
      "    50 * b.1 ≤ -7 * 2 ^ 40 - 20 * b.2.2.2 - 51200 ∧" + NL +
      "    -7 * 2 ^ 40 - 20 * b.2.2.1 + 51200 ≤ 50 * b.2.1)" + NL + NL +
      "def rayChainCell (i : ℕ) : Bool :=" + NL +
      "  decide (%d ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)" % NRC + NL + NL)
# the per-module theorems use  rayGeomCell (rayCellG ..) -> adapt names
pm = per_module('ray', NR, None).replace("rayGeomCell (rayCellG (", "rayGeomCell (rayCellG (")
pm = pm.replace("rayGeomCell (rayCellG (%d * %d + i))" % (CPM, 0), "rayGeomCell (rayCellG (%d * %d + i))" % (CPM, 0))
t += pm
t += ("theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 15 * 2 ^ 40 ≤ 4 * (rayCellG %d).2.2.2 := by" % (NRC - 1) + NL + "  decide +kernel" + NL + NL +
      "lemma ray_geom' (i : ℕ) (hi : i < %d) :" % NRC + NL +
      "    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧" + NL +
      "    50 * (rayCellG i).1 ≤ -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.2 - 51200 ∧" + NL +
      "    -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.1 + 51200 ≤ 50 * (rayCellG i).2.1 := by" + NL +
      "  have h := List.all_eq_true.mp (ray_geom (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simpa [rayGeomCell] using h" + NL + NL +
      "lemma ray_chain' (i : ℕ) (hi : i + 1 < %d) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by" % NRC + NL +
      "  have h := List.all_eq_true.mp (ray_chain (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simp only [rayChainCell, decide_eq_true_eq] at h" + NL +
      "  rcases h with h | h" + NL + "  · omega" + NL + "  · exact h" + NL + NL + "end CatalanCore.Cert.SigmaHybS" + NL)
t = t.replace("rayGeomCell (rayCellG", "rayGeomCell (rayCellG")
# per_module generated 'rayGeomCell (rayCellG' only if prefix capitalised: fix names
t = t.replace("rayGeomCell(", "rayGeomCell (")
w('RayGlue', t)

# ------------------------------------------------------------------ SegLineGlue
cs = cfg('seg'); NS = len(cs['Ms']); SMs = [cs['Ms'][str(k)] for k in range(NS)]; NSC = NS * CPM
cl = cfg('line'); NLN = len(cl['Ms']); LMs = [cl['Ms'][str(k)] for k in range(NLN)]; NLC = NLN * CPM
# per-module sums V_k of the segment term
MPn, MPd = int(F(data()["info"]["MP"]) * 100000), 100000
refined = json.load(open(os.path.join(HERE, 'refined_seg.json')))['cells']
cellsS = [tuple(c) for c in refined]; cellsS += [(0, 0, cellsS[-1][2])] * (NSC - len(cellsS))
def fseg(c):
    a, b, g = c
    return (b - a) * (g * MPd - MPn * 2 ** 32 if g * MPd <= MPn * 2 ** 32 else 0)
V = [sum(fseg(c) for c in cellsS[k * CPM:(k + 1) * CPM]) for k in range(NS)]
SVAL = sum(V)
t = "module" + NL + NL + "".join("public import %sSegM%d" % (P, k) + NL for k in range(NS)) + "".join("public import %sLineM%d" % (P, k) + NL for k in range(NLN)) + "public import %sBridge" % P + NL + NL
t += "@[expose] public section" + NL + NL + "/-!" + NL + "# Glue for the real-axis cells: global indexing, chain/cover checks, the sum `S_cert`" + NL + "-/" + NL + NL
t += "open Real" + NL + NL + "namespace CatalanCore.Cert.SigmaHybS" + NL + NL + "set_option maxRecDepth 1000000" + NL + NL
t += '''/-- cover lemma for a chain of closed intervals. -/
lemma cover_chain (n : ℕ) (a b : ℕ → ℝ) (lo hi : ℝ) (hn0 : 0 < n) (h0 : a 0 ≤ lo)
    (hn : hi ≤ b (n - 1)) (hab : ∀ i, i + 1 < n → a (i + 1) ≤ b i) :
    ∀ x, lo ≤ x → x ≤ hi → ∃ i < n, a i ≤ x ∧ x ≤ b i := by
  have key : ∀ k, k < n → ∀ x, a 0 ≤ x → x ≤ b k → ∃ i < n, a i ≤ x ∧ x ≤ b i := by
    intro k
    induction k with
    | zero => intro hk x h1 h2; exact ⟨0, hk, h1, h2⟩
    | succ k ih =>
      intro hk x h1 h2
      by_cases hx : x ≤ b k
      · exact ih (by omega) x h1 hx
      · exact ⟨k + 1, hk, le_trans (hab k hk) (le_of_lt (not_le.mp hx)), h2⟩
  intro x hx1 hx2
  exact key (n - 1) (by omega) x (h0.trans hx1) (hx2.trans hn)

'''
def real_block(pre, Pre, n, Ms_, nc, mode, G):
    rhs = ('((((%sCellG i).2.2 : ℚ) / 2 ^ 32 : ℚ) : ℝ)' % pre) if mode == 'true' else '((GMINS : ℚ) : ℝ)'
    s = tbl(pre + 'M', 'ℕ', Ms_, '1') + tbl(pre + 'P', 'ℕ', ['%sM%dP' % (Pre, k) for k in range(n)], '0')
    s += ("theorem %sAll_ok : ∀ m < %d, ∀ j < %d / %sM m, realMacroOKH sigH %s %s (%sM m) (%sP m) j = true := by" % (pre, n, CPM, pre, mode, G, pre, pre) + NL +
          "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("%sM%d_ok" % (Pre, k) for k in range(n)) + NL + NL +
          "theorem %sM_pos (m : ℕ) : 0 < %sM m := by" % (pre, pre) + NL + "  unfold %sM; split <;> norm_num" % pre + NL + NL +
          "theorem %sM_dvd (m : ℕ) (hm : m < %d) : %sM m ∣ %d := by" % (pre, n, pre, CPM) + NL + "  interval_cases m <;> decide" + NL + NL +
          "def %sCellG (i : ℕ) : ℤ × ℤ × ℤ :=" % pre + NL +
          "  realCell (%sM (i / %d)) (%sP (i / %d)) ((i %% %d) / %sM (i / %d)) (i %% %sM (i / %d))" % (pre, CPM, pre, CPM, CPM, pre, CPM, pre, CPM) + NL + NL +
          "theorem %s_sound (i : ℕ) (hi : i < %d) (x : ℝ) (h1 : ((%sCellG i).1 : ℝ) / 2 ^ 40 ≤ x)" % (pre, nc, pre) + NL +
          "    (h2 : x ≤ ((%sCellG i).2.1 : ℝ) / 2 ^ 40) :" % pre + NL +
          "    %s ≤ gHR sigH x 0 := by" % rhs + NL)
    s += ("  have := realMacroH_sound sigH %s %s (%sM (i / %d)) (%sP (i / %d)) ((i %% %d) / %sM (i / %d))" % (mode, G, pre, CPM, pre, CPM, CPM, pre, CPM) + NL +
          "    (%sAll_ok (i / %d) (by omega) _ (Nat.div_lt_div_of_lt_of_dvd (%sM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))))" % (pre, CPM, pre) + NL +
          "    (i %% %sM (i / %d)) (Nat.mod_lt _ (%sM_pos _)) x h1 h2" % (pre, CPM, pre) + NL +
          "  simpa [realThr, %sCellG] using this" % pre + NL + NL)
    return s
t += real_block('seg', 'SegM', NS, SMs, NSC, 'true', '0')
t += ("def segGeomCell (i : ℕ) : Bool :=" + NL + "  decide ((segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0)" + NL + NL +
      "def segChainCell (i : ℕ) : Bool :=" + NL + "  decide (%d ≤ i + 1 ∨ (segCellG (i + 1)).1 ≤ (segCellG i).2.1)" % NSC + NL + NL)
t += per_module('seg', NS, None)
t += ("theorem seg_ends : 50 * (segCellG 0).1 ≤ -7 * 2 ^ 40 ∧ 0 ≤ (segCellG %d).2.1 := by" % (NSC - 1) + NL + "  decide +kernel" + NL + NL +
      "lemma seg_geom' (i : ℕ) (hi : i < %d) : (segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0 := by" % NSC + NL +
      "  have h := List.all_eq_true.mp (seg_geom (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simpa [segGeomCell] using h" + NL + NL +
      "lemma seg_chain' (i : ℕ) (hi : i + 1 < %d) : (segCellG (i + 1)).1 ≤ (segCellG i).2.1 := by" % NSC + NL +
      "  have h := List.all_eq_true.mp (seg_chain (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simp only [segChainCell, decide_eq_true_eq] at h" + NL +
      "  rcases h with h | h" + NL + "  · omega" + NL + "  · exact h" + NL + NL)
t += ("def fSeg (i : ℕ) : ℤ :=" + NL + "  ((segCellG i).2.1 - (segCellG i).1) *" + NL +
      "    (if (segCellG i).2.2 * %d ≤ %d * 2 ^ 32 then (segCellG i).2.2 * %d - %d * 2 ^ 32 else 0)" % (MPd, MPn, MPd, MPn) + NL + NL +
      "def sacc : ℕ → ℤ" + NL + "  | 0 => 0" + NL + "  | n + 1 => sacc n + fSeg n" + NL + NL +
      "theorem sacc_add (a n : ℕ) : sacc (a + n) = sacc a + ((List.range n).map (fun i => fSeg (a + i))).sum := by" + NL +
      "  induction n with" + NL + "  | zero => simp" + NL +
      "  | succ n ih =>" + NL + "    rw [show a + (n + 1) = (a + n) + 1 from rfl, sacc, ih, List.range_succ, List.map_append, List.sum_append]" + NL +
      "    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]" + NL + "    ring" + NL + NL +
      "def segSum (k : ℕ) : ℤ := ((List.range %d).map (fun i => fSeg (%d * k + i))).sum" % (CPM, CPM) + NL + NL)
for k in range(NS):
    t += "theorem segSum_%d : segSum %d = (%d : ℤ) := by decide +kernel" % (k, k, V[k]) + NL + NL
t += ("def segV : ℕ → ℤ" + NL + "".join("  | %d => (%d : ℤ)" % (k, V[k]) + NL for k in range(NS)) + "  | _ => 0" + NL + NL +
      "theorem segSum_eq : ∀ k < %d, segSum k = segV k := by" % NS + NL + "  intro k hk" + NL + "  interval_cases k" + NL +
      "  exacts [%s]" % ", ".join("segSum_%d" % k for k in range(NS)) + NL + NL +
      "def cumSeg : ℕ → ℤ" + NL + "  | 0 => 0" + NL + "  | k + 1 => cumSeg k + segV k" + NL + NL +
      "theorem sacc_chunks : ∀ k, k ≤ %d → sacc (%d * k) = cumSeg k := by" % (NS, CPM) + NL +
      "  intro k" + NL + "  induction k with" + NL + "  | zero => intro _; simp [sacc, cumSeg]" + NL +
      "  | succ k ih =>" + NL + "    intro hk" + NL +
      "    rw [show %d * (k + 1) = %d * k + %d by ring, sacc_add, ih (by omega), cumSeg]" % (CPM, CPM, CPM) + NL +
      "    have := segSum_eq k (by omega)" + NL + "    unfold segSum at this" + NL + "    rw [this]" + NL + NL +
      "def SVAL : ℤ := %d" % SVAL + NL + NL +
      "theorem sacc_val : sacc %d = SVAL := by" % NSC + NL +
      "  have h := sacc_chunks %d le_rfl" % NS + NL +
      "  rw [show %d = %d * %d by norm_num] at *" % (NSC, CPM, NS) + NL +
      "  rw [h]" + NL + "  decide +kernel" + NL + NL)
# lines
t += real_block('line', 'LineM', NLN, LMs, NLC, 'false', 'GMINS')
t += ("def lineGeomCell (i : ℕ) : Bool :=" + NL + "  decide (0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40)" + NL + NL +
      "def lineChainCell (i : ℕ) : Bool :=" + NL + "  decide (%d ≤ i + 1 ∨ (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1)" % NLC + NL + NL)
t += per_module('line', NLN, None)
t += ("theorem line_ends : (lineCellG 0).1 ≤ 0 ∧ 2 ^ 40 ≤ (lineCellG %d).2.1 := by" % (NLC - 1) + NL + "  decide +kernel" + NL + NL +
      "lemma line_geom' (i : ℕ) (hi : i < %d) : 0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40 := by" % NLC + NL +
      "  have h := List.all_eq_true.mp (line_geom (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simpa [lineGeomCell] using h" + NL + NL +
      "lemma line_chain' (i : ℕ) (hi : i + 1 < %d) : (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1 := by" % NLC + NL +
      "  have h := List.all_eq_true.mp (line_chain (i / %d) (by omega)) (i %% %d) (List.mem_range.mpr (by omega))" % (CPM, CPM) + NL +
      "  have e : %d * (i / %d) + i %% %d = i := by omega" % (CPM, CPM, CPM) + NL +
      "  rw [e] at h" + NL + "  simp only [lineChainCell, decide_eq_true_eq] at h" + NL +
      "  rcases h with h | h" + NL + "  · omega" + NL + "  · exact h" + NL + NL + "end CatalanCore.Cert.SigmaHybS" + NL)
w('SegLineGlue', t)
print('ray modules', NR, 'seg', NS, 'line', NLN, 'SVAL', SVAL, 'Sbase', float(F(SVAL, MPd * 2 ** 72)))
json.dump(dict(SVAL=str(SVAL), Sbase=str(F(SVAL, MPd * 2 ** 72))), open(os.path.join(HERE, 'cfg_S.json'), 'w'))
