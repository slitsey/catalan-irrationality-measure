module

public import CatalanFrames.HybGen.D1Prefix
public import CatalanFrames.HybGen.FamilySum

@[expose] public section

/-!
# Fixed eighth-window compatibility instance of generic family summation

`class_sum_of_tables`: for a list `ll` of pieces chained from `1/68`, covered for every admissible
`(r, m)` (window `r ≤ 8m ≤ r + 9`), the class sum of `WGm` up to `⌊lastEnd * r⌋` is at most
`r² ((9/4 · (1/68) + listInt ll)/φ(M) + ε)` eventually, uniformly in `m`.  The prefix `p ≤ r/68`
uses the trivial `D1` bound `X ≤ 2(r+m)`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.HybGen

variable {Fr : Frame}

lemma XGm_D1 (I : HybInst Fr) (r m p : ℕ) : XGm I r m p ≤ 2 * (r + m) := by
  have h := trop_D1 (lev := I.lev) p r m
  have : (XGm I r m p : ℚ) ≤ ((2 * (r + m) : ℕ) : ℚ) := by push_cast; exact h
  exact_mod_cast this

theorem class_sum_of_tables {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c) (I : HybInst Fr)
    (ll : List Piece) (hl : Chain (1 / 68) ll)
    (hcov : ∀ r m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 → 400 ≤ r → ∀ P ∈ ll, Covers c (WGm I r m) r P)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      clsSum M c (WGm I r m) 0 ⌊lastEnd (1 / 68) ll * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((9 / 4 * (1 / 68) + listInt ll) / (M.totient : ℝ) + ε) := by
  have hwin : ∀ r m : ℕ, (r ≤ 8*m ∧ 8*m ≤ r+9) →
      (m : ℝ) ≤ (1/8 : ℝ)*r+9/8 := by
    intro r m hm
    have hh : (8*m : ℝ) ≤ r+9 := by exact_mod_cast hm.2
    push_cast at hh
    linarith
  have hcovers : ∀ᶠ r : ℕ in atTop, ∀ m, (r ≤ 8*m ∧ 8*m ≤ r+9) →
      ∀ P ∈ ll, Covers c (WGm I r m) r P := by
    filter_upwards [eventually_ge_atTop 400] with r hr
    intro m hm
    exact hcov r m hm.1 hm.2 hr
  have h := class_sum_of_affine_window hc I (fun r m => r ≤ 8*m ∧ 8*m ≤ r+9)
    (1/8) (9/8) (1/68) (by norm_num) (by norm_num) hwin ll hl hcovers hε
  filter_upwards [h] with r hr
  intro m hm1 hm2
  convert hr m ⟨hm1,hm2⟩ using 1 <;> norm_num

end CatalanFrames.HybGen

#print axioms CatalanFrames.HybGen.class_sum_of_tables
