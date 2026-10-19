module

public import CatalanCore.Arith.Hybrid.LemmaE.Gauss
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

/-!
# Congruence modulo `p` for polynomials over `ℚ`, through the Gauss norm

`Int1 f`  : `f` is `p`-integral (all coefficients in `ℤ_(p)`), i.e. `gn p f ≤ 1`.
`Cng f f'` : `f ≡ f' (mod p)`, i.e. `gn p (f - f') < 1`.

No residue field and no `ZMod p[X]` are used: congruence of determinants and adjugates of
integral polynomial matrices follows from the ultrametric inequality and `gn_mul`.
-/

open Polynomial Finset

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime]

def Int1 (f : ℚ[X]) : Prop := gn p f ≤ 1

def Cng (f f' : ℚ[X]) : Prop := gn p (f - f') < 1

variable {p}

lemma gn_add_le (f g : ℚ[X]) : gn p (f + g) ≤ max (gn p f) (gn p g) :=
  Polynomial.isNonarchimedean_gaussNorm (v := Rat.AbsoluteValue.padic p) (padic_isNonarch p)
    zero_le_one f g

lemma gn_neg (f : ℚ[X]) : gn p (-f) = gn p f := by
  have : -f = C (-1 : ℚ) * f := by simp
  rw [this, gn_mul, gn_C]; simp

lemma gn_sub_le (f g : ℚ[X]) : gn p (f - g) ≤ max (gn p f) (gn p g) := by
  rw [sub_eq_add_neg]
  have := gn_add_le (p := p) f (-g)
  rwa [gn_neg] at this

lemma gn_zero : gn p (0 : ℚ[X]) = 0 := by simp [gn]

namespace Int1

lemma add {f g : ℚ[X]} (hf : Int1 p f) (hg : Int1 p g) : Int1 p (f + g) :=
  (gn_add_le f g).trans (max_le hf hg)

lemma neg {f : ℚ[X]} (hf : Int1 p f) : Int1 p (-f) := by unfold Int1; rwa [gn_neg]

lemma sub {f g : ℚ[X]} (hf : Int1 p f) (hg : Int1 p g) : Int1 p (f - g) :=
  (gn_sub_le f g).trans (max_le hf hg)

lemma mul {f g : ℚ[X]} (hf : Int1 p f) (hg : Int1 p g) : Int1 p (f * g) := by
  unfold Int1 at *
  rw [gn_mul]
  calc gn p f * gn p g ≤ 1 * 1 := mul_le_mul hf hg (gn_nonneg p g) zero_le_one
    _ = 1 := one_mul 1

lemma zero : Int1 p (0 : ℚ[X]) := by unfold Int1; rw [gn_zero]; exact zero_le_one

lemma one : Int1 p (1 : ℚ[X]) := by unfold Int1; rw [gn_one]

lemma sum {ι : Type*} {s : Finset ι} {f : ι → ℚ[X]} (h : ∀ i ∈ s, Int1 p (f i)) :
    Int1 p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero (p := p)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma prod {ι : Type*} {s : Finset ι} {f : ι → ℚ[X]} (h : ∀ i ∈ s, Int1 p (f i)) :
    Int1 p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Int1

namespace Cng

lemma refl (f : ℚ[X]) : Cng p f f := by unfold Cng; rw [sub_self, gn_zero]; exact one_pos

lemma symm {f g : ℚ[X]} (h : Cng p f g) : Cng p g f := by
  unfold Cng at *; rwa [← neg_sub, gn_neg]

lemma trans {f g h : ℚ[X]} (h1 : Cng p f g) (h2 : Cng p g h) : Cng p f h := by
  unfold Cng at *
  have : f - h = (f - g) + (g - h) := by ring
  rw [this]
  exact lt_of_le_of_lt (gn_add_le _ _) (max_lt h1 h2)

lemma add {f f' g g' : ℚ[X]} (h1 : Cng p f f') (h2 : Cng p g g') : Cng p (f + g) (f' + g') := by
  unfold Cng at *
  have : f + g - (f' + g') = (f - f') + (g - g') := by ring
  rw [this]
  exact lt_of_le_of_lt (gn_add_le _ _) (max_lt h1 h2)

lemma neg {f f' : ℚ[X]} (h : Cng p f f') : Cng p (-f) (-f') := by
  unfold Cng at *
  have : -f - -f' = -(f - f') := by ring
  rwa [this, gn_neg]

lemma sub {f f' g g' : ℚ[X]} (h1 : Cng p f f') (h2 : Cng p g g') : Cng p (f - g) (f' - g') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h1.add h2.neg

/-- Multiplication of congruences (the factors `f'`, `g` must be integral). -/
lemma mul {f f' g g' : ℚ[X]} (hf' : Int1 p f') (hg : Int1 p g) (h1 : Cng p f f')
    (h2 : Cng p g g') : Cng p (f * g) (f' * g') := by
  unfold Cng at *
  have : f * g - f' * g' = (f - f') * g + f' * (g - g') := by ring
  rw [this]
  refine lt_of_le_of_lt (gn_add_le _ _) (max_lt ?_ ?_)
  · rw [gn_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (gn_nonneg p _) hg) h1
  · rw [gn_mul]
    calc gn p f' * gn p (g - g') ≤ 1 * gn p (g - g') :=
          mul_le_mul_of_nonneg_right hf' (gn_nonneg p _)
      _ < 1 := by rw [one_mul]; exact h2

lemma sum {ι : Type*} {s : Finset ι} {f f' : ι → ℚ[X]} (h : ∀ i ∈ s, Cng p (f i) (f' i)) :
    Cng p (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using refl (p := p) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma prod {ι : Type*} {s : Finset ι} {f f' : ι → ℚ[X]} (hi : ∀ i ∈ s, Int1 p (f i))
    (hi' : ∀ i ∈ s, Int1 p (f' i)) (h : ∀ i ∈ s, Cng p (f i) (f' i)) :
    Cng p (∏ i ∈ s, f i) (∏ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using refl (p := p) 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact Cng.mul ((hi' a (Finset.mem_insert_self _ _)))
      (Int1.prod fun i hi_ => hi i (Finset.mem_insert_of_mem hi_))
      (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi_ => hi i (Finset.mem_insert_of_mem hi_))
        (fun i hi_ => hi' i (Finset.mem_insert_of_mem hi_))
        (fun i hi_ => h i (Finset.mem_insert_of_mem hi_)))

/-- A polynomial congruent to a primitive one is primitive (given integrality). -/
lemma gn_eq_one {f f' : ℚ[X]} (h : Cng p f f') (hf' : gn p f' = 1) : gn p f = 1 := by
  unfold Cng at h
  have h2 : gn p (f' - f) < 1 := by rwa [← neg_sub, gn_neg]
  have h1 : gn p f' ≤ max (gn p f) (gn p (f' - f)) := by
    have : f' = f + (f' - f) := by ring
    conv_lhs => rw [this]
    exact gn_add_le _ _
  have h4 : gn p f ≤ max (gn p f') (gn p (f - f')) := by
    have : f = f' + (f - f') := by ring
    conv_lhs => rw [this]
    exact gn_add_le _ _
  rw [hf'] at h1 h4
  have u : gn p f ≤ 1 := h4.trans (max_le le_rfl h.le)
  have l : 1 ≤ gn p f := by
    rcases le_max_iff.mp h1 with h3 | h3
    · exact h3
    · linarith
  exact le_antisymm u l

end Cng

end CatalanCore.Arith.Hybrid.LemmaE
