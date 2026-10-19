module

public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Crude size of the border cost (MEM2C)

For every prime `p`: `topW ≤ cOf + 2 · ⌊log_p E⌋` and `topC ≤ 2 cOf + 4 ⌊log_p E⌋ + 1`, hence
`topC · log p ≤ 2 cOf · log p + 4 log E + log p`.
-/

open Finset CatalanCore.Arith.Hybrid

namespace CatalanCore.Arith.Hybrid

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ)

lemma levels_top_le {p : ℕ} (hp : 1 < p) {a : ℕ} (ha : a ≤ r + 2 * m) :
    levels I.lev p (Elev I r m) a (r + 2 * m) ≤ 2 * Nat.log p (Elev I r m) := by
  set E := Elev I r m with hE
  set K := Nat.log p E with hK
  have hKE : K ≤ E := Nat.log_le_self p E
  unfold levels
  have hsub : Icc 1 K ⊆ Icc 1 E := Icc_subset_Icc le_rfl hKE
  rw [← Finset.sum_subset hsub]
  · calc ∑ e ∈ Icc 1 K, wt I.lev (p ^ e) a (r + 2 * m)
        ≤ ∑ e ∈ Icc 1 K, 2 := Finset.sum_le_sum fun e _ => wt_le_two _ _ _ _
      _ = 2 * K := by simp [mul_comm]
  · intro e he hne
    have h1 := Finset.mem_Icc.1 he
    have h2 : K < e := by
      by_contra h
      exact hne (Finset.mem_Icc.2 ⟨h1.1, by omega⟩)
    have h3 : E < p ^ e := Nat.lt_pow_of_log_lt hp h2
    exact wt_eq_zero_of_Ebd I (N := r + 2 * m) h3 ha le_rfl

lemma topW_le {p : ℕ} (hp : 1 < p) :
    topW I r m p ≤ cOf I p + 2 * Nat.log p (Elev I r m) := by
  unfold topW
  refine Nat.add_le_add_left (Finset.sup_le fun a ha => ?_) _
  exact levels_top_le I r m hp (by have := Finset.mem_range.1 ha; omega)

lemma topC_le {p : ℕ} (hp : 1 < p) :
    topC I r m p ≤ 2 * cOf I p + 4 * Nat.log p (Elev I r m) + 1 := by
  have := topW_le I r m hp
  unfold topC; omega

lemma topC_log_le {p : ℕ} (hp : 1 < p) :
    (topC I r m p : ℝ) * Real.log p ≤
      2 * ((cOf I p : ℝ) * Real.log p) + 4 * Real.log (Elev I r m) + Real.log p := by
  have h1 : (topC I r m p : ℝ) ≤ 2 * cOf I p + 4 * Nat.log p (Elev I r m) + 1 := by
    exact_mod_cast topC_le I r m hp
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  have h2 : (Nat.log p (Elev I r m) : ℝ) * Real.log p ≤ Real.log (Elev I r m) := by
    by_cases hE : Elev I r m = 0
    · simp [hE]
    have hpow : p ^ Nat.log p (Elev I r m) ≤ Elev I r m := Nat.pow_log_le_self p hE
    have hpos : (0 : ℝ) < (p : ℝ) ^ Nat.log p (Elev I r m) := by positivity
    have hc : (p : ℝ) ^ Nat.log p (Elev I r m) ≤ (Elev I r m : ℝ) := by exact_mod_cast hpow
    have := Real.log_le_log hpos hc
    rwa [Real.log_pow] at this
  calc (topC I r m p : ℝ) * Real.log p
      ≤ (2 * cOf I p + 4 * Nat.log p (Elev I r m) + 1) * Real.log p :=
        mul_le_mul_of_nonneg_right h1 hlp.le
    _ = 2 * ((cOf I p : ℝ) * Real.log p) + 4 * ((Nat.log p (Elev I r m) : ℝ) * Real.log p)
          + Real.log p := by ring
    _ ≤ _ := by linarith

end CatalanCore.Arith.Hybrid
