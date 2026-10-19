module

public import CatalanCore.Bordered.Z1.GA1
public import CatalanCore.Bordered.Z1.RootCount

/-!
# Z1.5: nonvanishing facts about entries of `X`, `X′` at `θ = -c` over `ℝ`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

lemma qc_real_ne (x : ℚ) (hx : x ≠ 0) : (qc x : ℝ) ≠ 0 := by
  simpa [qc] using hx

lemma Xup_ne_real (s m k : ℕ) (c : ℝ) (hk : k + 1 < s) (h1 : (k : ℝ) + 1 ≠ c)
    (h2 : (k : ℝ) + 1 + ((s + m : ℕ) : ℝ) ≠ c) : Xup s m (-c) k ≠ 0 := by
  have hs : ((k : ℝ) + 1) < s := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold Xup
  refine mul_ne_zero (neg_ne_zero.2 ?_) (qc_real_ne _ (pj_ne s m k hk))
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) ?_) ?_) ?_
  · intro h; apply h1; linarith
  · intro h; apply h2; linarith
  · intro h; linarith

lemma Xlow_ne_real (s m k : ℕ) (c : ℝ) (hk : k + 1 < s) (h1 : (k : ℝ) + 1 ≠ c)
    (h2 : (k : ℝ) + 1 + ((s + m : ℕ) : ℝ) ≠ c) : Xlow s m (-c) k ≠ 0 := by
  have hs : ((k : ℝ) + 1) < s := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold Xlow
  refine mul_ne_zero (neg_ne_zero.2 ?_) (qc_real_ne _ (one_div_ne_zero (pj_ne s m k hk)))
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) ?_) ?_) ?_
  · intro h; apply h1; linarith
  · intro h; linarith
  · intro h; apply h2; push_cast at h ⊢; linarith

/-- Products of the off-diagonal pairs of `X` and `X′` agree. -/
lemma Xmat_prod_eq (s m k : ℕ) (θ : ℝ) (hk : k + 1 < s) :
    lq θ ((k : ℝ) + 2) * rq s m θ ((k : ℝ) + 1) = Xup s m θ k * Xlow s m θ k := by
  have := Xp_up_mul_low s m k θ hk
  unfold Xup Xlow
  rw [this]
  unfold lq rq
  ring

end CatalanCore.Bordered.Z1
