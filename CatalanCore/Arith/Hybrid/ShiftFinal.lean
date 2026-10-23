module
public import CatalanCore.Arith.Hybrid.ShiftAssemble
public import CatalanCore.Arith.Hybrid.ShiftRegular
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # Final assembly of the one-node formula -/

section Alg
variable {p o : ℕ} [Fact p.Prime]

/-- `Φ(z) - Φ(y)` as a difference of Cauchy potentials over the short arc. -/
lemma regular_diff (hp : 5 ≤ p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    (z y : ℕ) (hz : ((z : ℕ) : ZMod p) ∉ shortArc p h) (hy : ((y : ℕ) : ZMod p) ∉ shortArc p h) :
    cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) z -
        cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) y =
      (if 2 * h < p then (1 : ZMod p) else -1) *
        ((∑ c ∈ shortArc p h, (c - ((y : ℕ) : ZMod p))⁻¹) -
          ∑ c ∈ shortArc p h, (c - ((z : ℕ) : ZMod p))⁻¹) := by
  have h4 := four_ne_zmod p hp
  have hq : (h : ZMod p) = (4 : ZMod p)⁻¹ * (o : ZMod p) := by
    rw [← hroot]; field_simp
  have H := regular_gram hp hh z y hz hy
  rw [hq] at H
  rw [H]
  have hS : ∀ c ∈ shortArc p h, c ≠ ((z : ℕ) : ZMod p) := fun c hc hcz => hz (hcz ▸ hc)
  have hS' : ∀ c ∈ shortArc p h, c ≠ ((y : ℕ) : ZMod p) := fun c hc hcy => hy (hcy ▸ hc)
  have := cauchyPotential_difference (shortArc p h) (fun c : ZMod p => c)
    ((z : ℕ) : ZMod p) ((y : ℕ) : ZMod p) hS hS'
  rw [mul_assoc, ← this]

end Alg

section NodeAlg
variable {p o : ℕ} [Fact p.Prime]

/-- **Pure algebra of the node formula.** -/
theorem node_formula_alg (hp : 5 ≤ p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    (n n0 : ℕ) (hn : ((n : ℕ) : ZMod p) ∉ shortArc p h) (hn0 : ((n0 : ℕ) : ZMod p) ∉ shortArc p h)
    (G1 G2 hb gb B Cc : RatFunc (ZMod p)) (R : ZMod p → RatFunc (ZMod p)) (hhb : hb ≠ 0)
    (hG : hb ^ 2 * (G1 - G2) = gb * (-hb ^ 2 * gb * B ^ 2 *
        rfC p (cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) n0 -
          cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) n) -
        hb ^ 2 * gb * ∑ c : ZMod p, (rfC p ((16 * (c - ((n : ℕ) : ZMod p)))⁻¹) -
            rfC p ((16 * (c - ((n0 : ℕ) : ZMod p)))⁻¹)) * R c)) :
    G1 - G2 = gb * rfC p 16 * ∑ c : ZMod p,
      ((gb * (rfC p 16)⁻¹ * (rfC p 16)⁻¹) * (Cc - R c) +
        (-(gb * B ^ 2 * rfC p (if 2 * h < p then (1 : ZMod p) else -1) * (rfC p 16)⁻¹)) *
          (open Classical in if c ∈ shortArc p h then 1 else 0)) *
        (rfC p ((c - ((n : ℕ) : ZMod p))⁻¹) - rfC p ((c - ((n0 : ℕ) : ZMod p))⁻¹)) := by
  classical
  have h16 : (16 : ZMod p) ≠ 0 := by
    have h4 := four_ne_zmod p hp
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have hr16 : rfC p 16 ≠ 0 := (map_ne_zero (rfCHom p)).2 h16
  set u := (rfC p 16)⁻¹ with hu
  have hu1 : rfC p 16 * u = 1 := mul_inv_cancel₀ hr16
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : ZMod p → RatFunc (ZMod p), ∀ c, Δ c =
      rfC p ((c - ((n : ℕ) : ZMod p))⁻¹) - rfC p ((c - ((n0 : ℕ) : ZMod p))⁻¹) := ⟨_, fun _ => rfl⟩
  have F0 : ∀ x : ZMod p, rfC p ((16 * x)⁻¹) = u * rfC p (x⁻¹) := by
    intro x
    have : ((16 * x)⁻¹ : ZMod p) = (16 : ZMod p)⁻¹ * x⁻¹ := by rw [mul_inv]
    rw [this]
    have := (map_mul (rfCHom p) ((16 : ZMod p)⁻¹) (x⁻¹))
    simp only [rfCHom_apply] at this
    rw [this]
    congr 1
    have := map_inv₀ (rfCHom p) (16 : ZMod p)
    simp only [rfCHom_apply] at this
    exact this
  have F1 : ∑ c : ZMod p, Δ c = 0 := by
    simp only [hΔ, Finset.sum_sub_distrib]
    have e1 : ∑ c : ZMod p, rfC p ((c - ((n : ℕ) : ZMod p))⁻¹) =
        rfC p (∑ c : ZMod p, (c - ((n : ℕ) : ZMod p))⁻¹) := by
      simp only [← rfCHom_apply, map_sum]
    have e2 : ∑ c : ZMod p, rfC p ((c - ((n0 : ℕ) : ZMod p))⁻¹) =
        rfC p (∑ c : ZMod p, (c - ((n0 : ℕ) : ZMod p))⁻¹) := by
      simp only [← rfCHom_apply, map_sum]
    rw [e1, e2, sum_inv_shift_zero _ hp, sum_inv_shift_zero _ hp]
    simp
  have F2 : rfC p (cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) n0 -
        cyclicPrefix (fun x : ZMod p => x⁻¹ - (x - (4 : ZMod p)⁻¹ * (o : ZMod p))⁻¹) n) =
      rfC p (if 2 * h < p then (1 : ZMod p) else -1) * ∑ c ∈ shortArc p h, Δ c := by
    rw [regular_diff hp hh hroot n0 n hn0 hn]
    simp only [← rfCHom_apply, map_mul, map_sub, map_sum, hΔ, Finset.sum_sub_distrib]
  have F3 : ∑ c : ZMod p, ((open Classical in if c ∈ shortArc p h then (1 : RatFunc (ZMod p)) else 0) *
      Δ c) = ∑ c ∈ shortArc p h, Δ c := by
    simp [ite_mul, Finset.sum_ite_mem]
  have F4 : ∑ c : ZMod p, (rfC p ((16 * (c - ((n : ℕ) : ZMod p)))⁻¹) -
        rfC p ((16 * (c - ((n0 : ℕ) : ZMod p)))⁻¹)) * R c = u * ∑ c : ZMod p, Δ c * R c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [F0, F0, hΔ]; ring
  have hb2 : hb ^ 2 ≠ 0 := pow_ne_zero 2 hhb
  apply mul_left_cancel₀ hb2
  simp only [← hΔ]
  rw [hG, F2, F4]
  -- expand the target
  have T : ∑ c : ZMod p, ((gb * u * u) * (Cc - R c) +
        (-(gb * B ^ 2 * rfC p (if 2 * h < p then (1 : ZMod p) else -1) * u)) *
          (open Classical in if c ∈ shortArc p h then 1 else 0)) * Δ c =
      (gb * u * u) * (Cc * ∑ c : ZMod p, Δ c - ∑ c : ZMod p, Δ c * R c) +
        (-(gb * B ^ 2 * rfC p (if 2 * h < p then (1 : ZMod p) else -1) * u)) *
          ∑ c ∈ shortArc p h, Δ c := by
    rw [← F3]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [T, F1]
  linear_combination (hb ^ 2 * gb ^ 2 * u * ∑ c : ZMod p, Δ c * R c +
    hb ^ 2 * gb ^ 2 * B ^ 2 * rfC p (if 2 * h < p then (1 : ZMod p) else -1) *
      ∑ c ∈ shortArc p h, Δ c) * hu1

end NodeAlg

#print axioms CatalanCore.Arith.Hybrid.node_formula_alg
end CatalanCore.Arith.Hybrid
