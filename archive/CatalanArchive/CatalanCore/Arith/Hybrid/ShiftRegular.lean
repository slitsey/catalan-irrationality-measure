module
public import CatalanCore.Arith.Hybrid.ShiftZero
public import CatalanCore.Arith.Hybrid.CyclicCauchy
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid

/-! # The regular term: the short-arc Gram kernel

`regular_gram`: for two long residues `z, y` (outside the short arc `S` of `h`), the difference of
the periodic regular prefix `cyclicPrefix (x ↦ x⁻¹ - (x-h)⁻¹)` is `ε (y - z) ∑_{c ∈ S} ((c-z)(c-y))⁻¹`,
`ε = 1` if `2h < p` (`S = [0,h)`) and `ε = -1` otherwise (`S = [h,p)`, complementary potential). -/

variable {p : ℕ} [Fact p.Prime]

lemma sum_inv_shift_zero (a : ZMod p) (hp : 5 ≤ p) : ∑ c : ZMod p, (c - a)⁻¹ = 0 := by
  have h1 : ∑ c : ZMod p, (c - a)⁻¹ = ∑ c : ZMod p, c⁻¹ :=
    Equiv.sum_comp (Equiv.subRight a) (fun x : ZMod p => x⁻¹)
  have h2 : ∑ c : ZMod p, c⁻¹ = - ∑ c : ZMod p, c⁻¹ := by
    calc ∑ c : ZMod p, c⁻¹ = ∑ c : ZMod p, (-c)⁻¹ :=
          (Equiv.sum_comp (Equiv.neg (ZMod p)) (fun x : ZMod p => x⁻¹)).symm
      _ = - ∑ c : ZMod p, c⁻¹ := by simp [inv_neg, Finset.sum_neg_distrib]
  have h3 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rw [h1]
  have : (2 : ZMod p) * ∑ c : ZMod p, c⁻¹ = 0 := by
    rw [two_mul]; nth_rewrite 1 [h2]; ring
  exact (mul_eq_zero.1 this).resolve_left h3

/-- The interval potential as a sum over the residues of value `< h`. -/
lemma potential_eq_filter {h : ℕ} (hh : h < p) (a : ZMod p) :
    intervalCauchyPotential h a = ∑ c ∈ (Finset.univ.filter fun c : ZMod p => c.val < h), (c - a)⁻¹ := by
  classical
  have himg : (Finset.univ.filter fun c : ZMod p => c.val < h) =
      (range h).image (fun k : ℕ => (k : ZMod p)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hc; exact ⟨c.val, hc, ZMod.natCast_zmod_val c⟩
    · rintro ⟨k, hk, rfl⟩; rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]; exact hk
  rw [himg, Finset.sum_image]
  · rfl
  · intro k hk l hl hkl
    have := congrArg ZMod.val hkl
    simp only [ZMod.val_natCast] at this
    rw [Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hk; omega),
      Nat.mod_eq_of_lt (by have := Finset.mem_range.1 hl; omega)] at this
    exact this

/-- **Regular contraction.** -/
theorem regular_gram (hp : 5 ≤ p) {h : ℕ} (hh : h < p) (z y : ℕ)
    (hz : ((z : ℕ) : ZMod p) ∉ shortArc p h) (hy : ((y : ℕ) : ZMod p) ∉ shortArc p h) :
    cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (h : ZMod p))⁻¹) z -
        cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (h : ZMod p))⁻¹) y =
      (if 2 * h < p then (1 : ZMod p) else -1) * (((y : ℕ) : ZMod p) - ((z : ℕ) : ZMod p)) *
        ∑ c ∈ shortArc p h, ((c - ((z : ℕ) : ZMod p)) * (c - ((y : ℕ) : ZMod p)))⁻¹ := by
  classical
  rw [cyclicPrefix_cauchy_potential, cyclicPrefix_cauchy_potential]
  simp only [potential_eq_filter hh]
  have hS : ∀ c ∈ shortArc p h, c ≠ ((z : ℕ) : ZMod p) := fun c hc hcz => hz (hcz ▸ hc)
  have hS' : ∀ c ∈ shortArc p h, c ≠ ((y : ℕ) : ZMod p) := fun c hc hcy => hy (hcy ▸ hc)
  by_cases h2 : 2 * h < p
  · have hsa : shortArc p h = Finset.univ.filter fun c : ZMod p => c.val < h := by
      ext c; simp [shortArc, h2]
    rw [if_pos h2, hsa]
    have := cauchyPotential_difference (Finset.univ.filter fun c : ZMod p => c.val < h)
      (fun c : ZMod p => c) ((z : ℕ) : ZMod p) ((y : ℕ) : ZMod p)
      (fun c hc => hS c (hsa ▸ hc)) (fun c hc => hS' c (hsa ▸ hc))
    rw [one_mul]
    linear_combination this
  · have hsa : shortArc p h = Finset.univ.filter fun c : ZMod p => ¬ c.val < h := by
      ext c; simp [shortArc, h2]
    rw [if_neg h2]
    have hfull : ∀ a : ZMod p,
        ∑ c ∈ (Finset.univ.filter fun c : ZMod p => c.val < h), (c - a)⁻¹ =
          - ∑ c ∈ shortArc p h, (c - a)⁻¹ := by
      intro a
      have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (ZMod p))
        (fun c : ZMod p => c.val < h) (fun c => (c - a)⁻¹)
      rw [sum_inv_shift_zero a hp, ← hsa] at hsplit
      linear_combination hsplit
    simp only [hfull]
    have := cauchyPotential_difference (shortArc p h) (fun c : ZMod p => c)
      ((z : ℕ) : ZMod p) ((y : ℕ) : ZMod p) hS hS'
    linear_combination (-1 : ZMod p) * this

end CatalanCore.Arith.Hybrid
#print axioms CatalanCore.Arith.Hybrid.regular_gram
