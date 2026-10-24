module

public import CatalanFrames.P6.NV.Mid
public import CatalanFrames.LambdaHybrid.NV.Mod3

/-!
# P6 hybrid: the three-level `ModData3` instance

For `ℓ = 6t+1` prime: `K = 2t+1` (low), `T = 3t+1` (mid `[K,T)`, top `[T,ℓ)`).
Constants (Lean convention, `Mn = -M`): cross `t = 1/6`, mid diagonal `d = 1/2`, mid harmonic scale
`κ = -1/18`, `h = cc/2`, top harmonic weight `τ₀ = 1/36`; `A = (Gw - δ·cc)/36`.
The entry facts are `P6/NV/Entries.lean` and `Mid.lean`; the harmonic identity is the reflection
`n = ℓ - y` of the two windows of `Gw`.
-/

@[expose] public section

open Finset CatalanCore CatalanFrames.LambdaHybrid.NV CatalanFrames.P6 CatalanFrames.P6.NV

namespace CatalanFrames.P6Hybrid

variable {ℓ t : ℕ} [Fact ℓ.Prime]

lemma sum_Ico_refl {M : Type*} [AddCommMonoid M] (F : ℕ → M) (lo cnt : ℕ) :
    ∑ n ∈ Ico lo (lo + cnt), F n = ∑ j ∈ range cnt, F (lo + cnt - 1 - j) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left,
    ← Finset.sum_range_reflect (fun k => F (lo + k)) cnt]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  congr 1; omega

/-- `n = ℓ - c`-reflection: `(n : 𝔽_ℓ) = -(c)` when `n + c = ℓ`. -/
lemma cast_ref {n c : ℕ} (h : n + c = ℓ) : ((n : ℕ) : ZMod ℓ) = -(c : ZMod ℓ) := by
  have := congrArg (Nat.cast : ℕ → ZMod ℓ) h
  push_cast at this
  rw [ZMod.natCast_self] at this
  linear_combination this

lemma top_sum (hl : ℓ = 6 * t + 1) (a b : ℕ) :
    ∑ n ∈ Ico (3 * t + 1) ℓ, (1 / ((a : ZMod ℓ) - n)) * (1 / ((b : ZMod ℓ) - n)) =
      ∑ j ∈ range (3 * t), finv ℓ (a + 1 + j) * finv ℓ (b + 1 + j) := by
  have e : Ico (3 * t + 1) ℓ = Ico (3 * t + 1) (3 * t + 1 + 3 * t) := by
    congr 1; omega
  rw [e, sum_Ico_refl]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have hc := cast_ref (ℓ := ℓ) (n := 3 * t + 1 + 3 * t - 1 - j) (c := j + 1) (by omega)
  simp only [finv]
  rw [hc]
  push_cast
  ring

lemma mid_sum (hl : ℓ = 6 * t + 1) (a b : ℕ) :
    ∑ n ∈ Ico (2 * t + 1) (3 * t + 1), (1 / ((a : ZMod ℓ) - n)) * (1 / ((b : ZMod ℓ) - n)) =
      ∑ j ∈ range t, finv ℓ (a + 3 * t + 1 + j) * finv ℓ (b + 3 * t + 1 + j) := by
  have e : Ico (2 * t + 1) (3 * t + 1) = Ico (2 * t + 1) (2 * t + 1 + t) := by
    congr 1; omega
  rw [e, sum_Ico_refl]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.1 hj
  have hc := cast_ref (ℓ := ℓ) (n := 2 * t + 1 + t - 1 - j) (c := 3 * t + 1 + j) (by omega)
  simp only [finv]
  rw [hc]
  push_cast
  ring

lemma inv_swap (x y : ZMod ℓ) : 1 / (6 * (y - x)) = -(1 / 6 * (1 / (x - y))) := by
  have : y - x = -(x - y) := by ring
  rw [this]
  simp only [mul_neg, one_div, inv_neg, mul_inv]

variable (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
include hl ht

lemma eighteen_ne : (18 : ZMod ℓ) ≠ 0 := by
  have := mul_ne_zero (six_ne hl ht) (three_ne hl ht)
  rwa [show (6 : ZMod ℓ) * 3 = 18 by norm_num] at this

lemma Dq_low {p : ℕ} (hp : p < 2 * t + 1) : Dq ℓ (2 * t + 1) p = 1 := by simp [Dq, hp]
lemma Dq_high {p : ℕ} (hp : 2 * t + 1 ≤ p) : Dq ℓ (2 * t + 1) p = ℓ := by
  simp [Dq, not_lt.2 hp]

/-- **The P6 three-level data.** -/
noncomputable def p6Data3 : ModData3 p6Frame ℓ (2 * t + 1) (3 * t + 1) where
  t := 1 / 6
  d := 1 / 2
  κ := -1 / 18
  h := cc ℓ t / 2
  τ₀ := 1 / 36
  A := Matrix.of fun a b => (Gw ℓ t a b - if (a : ℕ) = b then cc ℓ t else 0) / 36
  ht := one_div_ne_zero (six_ne hl ht)
  hd := one_div_ne_zero (two_ne hl ht)
  hκ := div_ne_zero (neg_ne_zero.2 one_ne_zero) (eighteen_ne hl ht)
  hτ := one_div_ne_zero (n36_ne hl ht)
  htk := by
    have h2 := two_ne hl ht
    have h6 := six_ne hl ht
    have h18 := eighteen_ne hl ht
    field_simp
    norm_num
  low := by
    intro a a' e eb he
    have ha : (a : ℕ) ≤ 2 * t := by have := a.2; omega
    have ha' : (a' : ℕ) ≤ 2 * t := by have := a'.2; omega
    have g := he.add (low_good hl ht ha ha')
    rw [Dq_low hl ht a.2, Dq_low hl ht a'.2, one_mul, one_mul]
    simpa using g
  lh := by
    intro p q hp hKq hqT
    have g := lowmid_good hl ht (a := p) (b := q) (by omega) hKq (by omega)
    rw [Dq_low hl ht hp, Dq_high hl ht hKq, one_mul, zero_add]
    refine (g.congr' (by ring)).congr ?_
    exact inv_swap _ _
  hl := by
    intro p q hKp hpT hq
    have g := lowmid_good hl ht (a := q) (b := p) (by omega) hKp (by omega)
    rw [Dq_low hl ht hq, Dq_high hl ht hKp, mul_one, zero_add]
    rw [Mn_comm]
    refine (g.congr' (by ring)).congr ?_
    exact inv_swap _ _
  hhOff := by
    intro p q hKp hpT hKq hqT hne
    rw [Dq_high hl ht hKp, Dq_high hl ht hKq, zero_add]
    have key : ∀ a b : ℕ, 2 * t + 1 ≤ a → a < b → b ≤ 3 * t →
        Good ℓ ((ℓ : ℚ) * (ℓ : ℚ) * p6Frame.Mn a b) 0 := fun a b h1 h2 h3 =>
      (midmid_off_good hl ht h1 h2 h3).congr' (by ring)
    rcases lt_or_gt_of_ne hne with h | h
    · exact key p q hKp h (by omega)
    · rw [Mn_comm]; exact key q p hKq h (by omega)
  hhDiag := by
    intro p hKp hpT e eb he
    rw [Dq_high hl ht hKp]
    have g := (he.ell_mul.ell_mul).add (midmid_diag_good hl ht (a := p) hKp (by omega))
    refine (g.congr' (by ring)).congr ?_
    simp
  harm := by
    intro a a'
    have ha : (a : ℕ) ≤ 2 * t := by have := a.2; omega
    have h2 := two_ne hl ht
    have h18 := eighteen_ne hl ht
    have h36 := n36_ne hl ht
    rw [mid_sum hl a a', top_sum hl a a']
    simp only [Matrix.of_apply, Gw]
    by_cases h : a = a'
    · subst h; simp; field_simp; ring
    · have : (a : ℕ) ≠ a' := fun h' => h (Fin.ext h')
      simp [h, this]
      field_simp
      ring

end CatalanFrames.P6Hybrid
