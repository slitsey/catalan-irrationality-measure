module

public import CatalanCore.Cert.SigmaP6.SegA
public import CatalanCore.Cert.SigmaP6.SegB
public import CatalanCore.Cert.SigmaP6.LineM
public import CatalanCore.Cert.SigmaP6.Bridge
public import CatalanCore.Cert.SigmaP6.Bridge

@[expose] public section

/-!
# Glue for the real-axis cells: global indexing, chain/cover checks, the sum `S_cert`
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

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

/-! ### segment cells (2048 = 88 macros of 32) -/

def segCellG (i : ℕ) : ℤ × ℤ × ℤ :=
  if i < 1024 then realCell 32 SegAP (i / 32) (i % 32) else realCell 32 SegBP (i / 32 - 32) (i % 32)

theorem seg_sound (i : ℕ) (hi : i < 2048) (x : ℝ) (h1 : ((segCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40) :
    ((((segCellG i).2.2 : ℚ) / 2 ^ 32 : ℚ) : ℝ) ≤ gfun sigD x 0 := by
  unfold segCellG at *
  by_cases h : i < 1024
  · simp only [h, if_true] at h1 h2 ⊢
    have := realMacro_sound true 0 32 SegAP (i / 32) (SegA_ok (i / 32) (by omega)) (i % 32) (by omega) x h1 h2
    simpa [realThr] using this
  · simp only [h, if_false] at h1 h2 ⊢
    have := realMacro_sound true 0 32 SegBP (i / 32 - 32) (SegB_ok (i / 32 - 32) (by omega)) (i % 32) (by omega) x h1 h2
    simpa [realThr] using this

def segGeomCell (i : ℕ) : Bool :=
  decide ((segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0)

def segChainCell (i : ℕ) : Bool :=
  decide (2048 ≤ i + 1 ∨ (segCellG (i + 1)).1 ≤ (segCellG i).2.1)

theorem seg_geom : ∀ m < 4, (List.range 512).all (fun i => segGeomCell (512 * m + i)) = true := by
  decide +kernel

theorem seg_chain : ∀ m < 4, (List.range 512).all (fun i => segChainCell (512 * m + i)) = true := by
  decide +kernel

theorem seg_ends : 10 * (segCellG 0).1 ≤ -1 * 2 ^ 40 ∧ 0 ≤ (segCellG 2047).2.1 := by
  decide +kernel

lemma seg_geom' (i : ℕ) (hi : i < 2048) : (segCellG i).1 ≤ (segCellG i).2.1 ∧ (segCellG i).2.1 ≤ 0 := by
  have h := List.all_eq_true.mp (seg_geom (i / 512) (by omega)) (i % 512) (List.mem_range.mpr (by omega))
  have e : 512 * (i / 512) + i % 512 = i := by omega
  rw [e] at h
  simpa [segGeomCell] using h

lemma seg_chain' (i : ℕ) (hi : i + 1 < 2048) : (segCellG (i + 1)).1 ≤ (segCellG i).2.1 := by
  have h := List.all_eq_true.mp (seg_chain (i / 512) (by omega)) (i % 512) (List.mem_range.mpr (by omega))
  have e : 512 * (i / 512) + i % 512 = i := by omega
  rw [e] at h
  simp only [segChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

def fSeg (i : ℕ) : ℤ :=
  ((segCellG i).2.1 - (segCellG i).1) *
    (if (segCellG i).2.2 * 1000000 ≤ 1883395 * 2 ^ 32 then (segCellG i).2.2 * 1000000 - 1883395 * 2 ^ 32 else 0)

def sacc : ℕ → ℤ
  | 0 => 0
  | n + 1 => sacc n + fSeg n

def SVAL : ℤ := -105020544668693660879077760

theorem sacc_val : sacc 2048 = SVAL := by decide +kernel

end CatalanCore.Cert.SigmaP6
