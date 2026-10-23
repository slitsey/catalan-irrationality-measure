module

public import CatalanCore.Cert.SigmaHybS.SegM0
public import CatalanCore.Cert.SigmaHybS.SegM1
public import CatalanCore.Cert.SigmaHybS.SegM2
public import CatalanCore.Cert.SigmaHybS.SegM3
public import CatalanCore.Cert.SigmaHybS.SegM4
public import CatalanCore.Cert.SigmaHybS.SegM5
public import CatalanCore.Cert.SigmaHybS.LineM0
public import CatalanCore.Cert.SigmaHybS.LineM1
public import CatalanCore.Cert.SigmaHybS.LineM2
public import CatalanCore.Cert.SigmaHybS.LineM3
public import CatalanCore.Cert.SigmaHybS.LineM4
public import CatalanCore.Cert.SigmaHybS.LineM5
public import CatalanCore.Cert.SigmaHybS.LineM6
public import CatalanCore.Cert.SigmaHybS.Bridge

@[expose] public section

/-!
# Glue for the real-axis cells: global indexing, chain/cover checks, the sum `S_cert`
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 1000000

/-- cover lemma for a chain of closed intervals. -/
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

def segM : ℕ → ℕ
  | 0 => 32
  | 1 => 32
  | 2 => 32
  | 3 => 32
  | 4 => 16
  | 5 => 32
  | _ => 1

def segP : ℕ → ℕ
  | 0 => SegMM0P
  | 1 => SegMM1P
  | 2 => SegMM2P
  | 3 => SegMM3P
  | 4 => SegMM4P
  | 5 => SegMM5P
  | _ => 0

theorem segAll_ok : ∀ m < 6, ∀ j < 1024 / segM m, realMacroOKH sigH true 0 (segM m) (segP m) j = true := by
  intro m hm
  interval_cases m
  exacts [SegMM0_ok, SegMM1_ok, SegMM2_ok, SegMM3_ok, SegMM4_ok, SegMM5_ok]

theorem segM_pos (m : ℕ) : 0 < segM m := by
  unfold segM; split <;> norm_num

theorem segM_dvd (m : ℕ) (hm : m < 6) : segM m ∣ 1024 := by
  interval_cases m <;> decide

def segCellG (i : ℕ) : ℤ × ℤ × ℤ :=
  realCell (segM (i / 1024)) (segP (i / 1024)) ((i % 1024) / segM (i / 1024)) (i % segM (i / 1024))

theorem seg_sound (i : ℕ) (hi : i < 6144) (x : ℝ) (h1 : ((segCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40) :
    ((((segCellG i).2.2 : ℚ) / 2 ^ 32 : ℚ) : ℝ) ≤ gHR sigH x 0 := by
  have := realMacroH_sound sigH true 0 (segM (i / 1024)) (segP (i / 1024)) ((i % 1024) / segM (i / 1024))
    (segAll_ok (i / 1024) (by omega) _ (Nat.div_lt_div_of_lt_of_dvd (segM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))))
    (i % segM (i / 1024)) (Nat.mod_lt _ (segM_pos _)) x h1 h2
  simpa [realThr, segCellG] using this

def segGeomCell (i : ℕ) : Bool :=
  decide ((segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0)

def segChainCell (i : ℕ) : Bool :=
  decide (6144 ≤ i + 1 ∨ (segCellG (i + 1)).1 ≤ (segCellG i).2.1)

theorem seg_geom_0 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 0 + i))) = true := by
  decide +kernel

theorem seg_geom_1 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 1 + i))) = true := by
  decide +kernel

theorem seg_geom_2 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 2 + i))) = true := by
  decide +kernel

theorem seg_geom_3 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 3 + i))) = true := by
  decide +kernel

theorem seg_geom_4 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 4 + i))) = true := by
  decide +kernel

theorem seg_geom_5 : (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * 5 + i))) = true := by
  decide +kernel

theorem seg_chain_0 : (List.range 1024).all (fun i => segChainCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem seg_chain_1 : (List.range 1024).all (fun i => segChainCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem seg_chain_2 : (List.range 1024).all (fun i => segChainCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem seg_chain_3 : (List.range 1024).all (fun i => segChainCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem seg_chain_4 : (List.range 1024).all (fun i => segChainCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem seg_chain_5 : (List.range 1024).all (fun i => segChainCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem seg_geom : ∀ m < 6, (List.range 1024).all (fun i => segGeomCell (segCellG (1024 * m + i))) = true := by
  intro m hm
  interval_cases m
  exacts [seg_geom_0, seg_geom_1, seg_geom_2, seg_geom_3, seg_geom_4, seg_geom_5]

theorem seg_chain : ∀ m < 6, (List.range 1024).all (fun i => segChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [seg_chain_0, seg_chain_1, seg_chain_2, seg_chain_3, seg_chain_4, seg_chain_5]

theorem seg_ends : 50 * (segCellG 0).1 ≤ -7 * 2 ^ 40 ∧ 0 ≤ (segCellG 6143).2.1 := by
  decide +kernel

lemma seg_geom' (i : ℕ) (hi : i < 6144) : (segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0 := by
  have h := List.all_eq_true.mp (seg_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [segGeomCell] using h

lemma seg_chain' (i : ℕ) (hi : i + 1 < 6144) : (segCellG (i + 1)).1 ≤ (segCellG i).2.1 := by
  have h := List.all_eq_true.mp (seg_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [segChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

def fSeg (i : ℕ) : ℤ :=
  ((segCellG i).2.1 - (segCellG i).1) *
    (if (segCellG i).2.2 * 100000 ≤ 217116 * 2 ^ 32 then (segCellG i).2.2 * 100000 - 217116 * 2 ^ 32 else 0)

def sacc : ℕ → ℤ
  | 0 => 0
  | n + 1 => sacc n + fSeg n

theorem sacc_add (a n : ℕ) : sacc (a + n) = sacc a + ((List.range n).map (fun i => fSeg (a + i))).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from rfl, sacc, ih, List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring

def segSum (k : ℕ) : ℤ := ((List.range 1024).map (fun i => fSeg (1024 * k + i))).sum

theorem segSum_0 : segSum 0 = (-579829604708470025851968 : ℤ) := by decide +kernel

theorem segSum_1 : segSum 1 = (-2049048228296071080557536 : ℤ) := by decide +kernel

theorem segSum_2 : segSum 2 = (-3771577746654489162495872 : ℤ) := by decide +kernel

theorem segSum_3 : segSum 3 = (-5761841592483553117657536 : ℤ) := by decide +kernel

theorem segSum_4 : segSum 4 = (-8124040089959922971557536 : ℤ) := by decide +kernel

theorem segSum_5 : segSum 5 = (-9399202563135215688426688 : ℤ) := by decide +kernel

def segV : ℕ → ℤ
  | 0 => (-579829604708470025851968 : ℤ)
  | 1 => (-2049048228296071080557536 : ℤ)
  | 2 => (-3771577746654489162495872 : ℤ)
  | 3 => (-5761841592483553117657536 : ℤ)
  | 4 => (-8124040089959922971557536 : ℤ)
  | 5 => (-9399202563135215688426688 : ℤ)
  | _ => 0

theorem segSum_eq : ∀ k < 6, segSum k = segV k := by
  intro k hk
  interval_cases k
  exacts [segSum_0, segSum_1, segSum_2, segSum_3, segSum_4, segSum_5]

def cumSeg : ℕ → ℤ
  | 0 => 0
  | k + 1 => cumSeg k + segV k

theorem sacc_chunks : ∀ k, k ≤ 6 → sacc (1024 * k) = cumSeg k := by
  intro k
  induction k with
  | zero => intro _; simp [sacc, cumSeg]
  | succ k ih =>
    intro hk
    rw [show 1024 * (k + 1) = 1024 * k + 1024 by ring, sacc_add, ih (by omega), cumSeg]
    have := segSum_eq k (by omega)
    unfold segSum at this
    rw [this]

def SVAL : ℤ := -29685539825237722046547136

theorem sacc_val : sacc 6144 = SVAL := by
  have h := sacc_chunks 6 le_rfl
  rw [show 6144 = 1024 * 6 by norm_num] at *
  rw [h]
  decide +kernel

def lineM : ℕ → ℕ
  | 0 => 32
  | 1 => 32
  | 2 => 32
  | 3 => 32
  | 4 => 32
  | 5 => 32
  | 6 => 32
  | _ => 1

def lineP : ℕ → ℕ
  | 0 => LineMM0P
  | 1 => LineMM1P
  | 2 => LineMM2P
  | 3 => LineMM3P
  | 4 => LineMM4P
  | 5 => LineMM5P
  | 6 => LineMM6P
  | _ => 0

theorem lineAll_ok : ∀ m < 7, ∀ j < 1024 / lineM m, realMacroOKH sigH false GMINS (lineM m) (lineP m) j = true := by
  intro m hm
  interval_cases m
  exacts [LineMM0_ok, LineMM1_ok, LineMM2_ok, LineMM3_ok, LineMM4_ok, LineMM5_ok, LineMM6_ok]

theorem lineM_pos (m : ℕ) : 0 < lineM m := by
  unfold lineM; split <;> norm_num

theorem lineM_dvd (m : ℕ) (hm : m < 7) : lineM m ∣ 1024 := by
  interval_cases m <;> decide

def lineCellG (i : ℕ) : ℤ × ℤ × ℤ :=
  realCell (lineM (i / 1024)) (lineP (i / 1024)) ((i % 1024) / lineM (i / 1024)) (i % lineM (i / 1024))

theorem line_sound (i : ℕ) (hi : i < 7168) (x : ℝ) (h1 : ((lineCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((lineCellG i).2.1 : ℝ) / 2 ^ 40) :
    ((GMINS : ℚ) : ℝ) ≤ gHR sigH x 0 := by
  have := realMacroH_sound sigH false GMINS (lineM (i / 1024)) (lineP (i / 1024)) ((i % 1024) / lineM (i / 1024))
    (lineAll_ok (i / 1024) (by omega) _ (Nat.div_lt_div_of_lt_of_dvd (lineM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))))
    (i % lineM (i / 1024)) (Nat.mod_lt _ (lineM_pos _)) x h1 h2
  simpa [realThr, lineCellG] using this

def lineGeomCell (i : ℕ) : Bool :=
  decide (0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40)

def lineChainCell (i : ℕ) : Bool :=
  decide (7168 ≤ i + 1 ∨ (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1)

theorem line_geom_0 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 0 + i))) = true := by
  decide +kernel

theorem line_geom_1 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 1 + i))) = true := by
  decide +kernel

theorem line_geom_2 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 2 + i))) = true := by
  decide +kernel

theorem line_geom_3 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 3 + i))) = true := by
  decide +kernel

theorem line_geom_4 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 4 + i))) = true := by
  decide +kernel

theorem line_geom_5 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 5 + i))) = true := by
  decide +kernel

theorem line_geom_6 : (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * 6 + i))) = true := by
  decide +kernel

theorem line_chain_0 : (List.range 1024).all (fun i => lineChainCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem line_chain_1 : (List.range 1024).all (fun i => lineChainCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem line_chain_2 : (List.range 1024).all (fun i => lineChainCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem line_chain_3 : (List.range 1024).all (fun i => lineChainCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem line_chain_4 : (List.range 1024).all (fun i => lineChainCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem line_chain_5 : (List.range 1024).all (fun i => lineChainCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem line_chain_6 : (List.range 1024).all (fun i => lineChainCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem line_geom : ∀ m < 7, (List.range 1024).all (fun i => lineGeomCell (lineCellG (1024 * m + i))) = true := by
  intro m hm
  interval_cases m
  exacts [line_geom_0, line_geom_1, line_geom_2, line_geom_3, line_geom_4, line_geom_5, line_geom_6]

theorem line_chain : ∀ m < 7, (List.range 1024).all (fun i => lineChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [line_chain_0, line_chain_1, line_chain_2, line_chain_3, line_chain_4, line_chain_5, line_chain_6]

theorem line_ends : (lineCellG 0).1 ≤ 0 ∧ 2 ^ 40 ≤ (lineCellG 7167).2.1 := by
  decide +kernel

lemma line_geom' (i : ℕ) (hi : i < 7168) : 0 ≤ (lineCellG i).1 ∧ (lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40 := by
  have h := List.all_eq_true.mp (line_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [lineGeomCell] using h

lemma line_chain' (i : ℕ) (hi : i + 1 < 7168) : (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1 := by
  have h := List.all_eq_true.mp (line_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [lineChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanCore.Cert.SigmaHybS
