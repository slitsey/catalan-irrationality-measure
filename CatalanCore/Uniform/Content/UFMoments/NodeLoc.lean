module

public import CatalanCore.Uniform.Content.UFMoments.Phi2
public import CatalanCore.Uniform.Content.UFMoments.Bridge

@[expose] public section

/-!
# UF moments: one border node of the scaled lift in the Gauss DVR

Abstract core block `Q` over `ℤ_(p)[X]` (with the Loewner commutator relation off the diagonal and
a primitive determinant) and one node `t` with border vector `σ` (commutator relation against the
core).  In `GaussLoc p`, with `u = norm`, `ℓ_a = (pF(c_a))/u`, `ℓ_t = pF(t)/u`:

* `adj_moment`: `det Q · t₀ - Σ_i σ_i Σ_k adj(Q)_{ik} Y_k = det Q · (t₀ - σ·Q⁻¹Y)` (moments in
  inverse form; `adj_moment_col` for columns, using `Qᵀ = Q`);
* `core_split`, `node_split`: `Q = D + π E` with `D` the colour-block part and `E` Loewner modulo `p`;
  `σ = s + π s'` likewise;
* `node_phi2`: the reduced second-order expansion of `(ℓ_t - σ·Q⁻¹ℓ) - d (1 - σ·Q⁻¹1)` (the
  `Φ`-numerator) from `phi2_expansion`, and `node_alpha_res`: `res(1 - σ·Q⁻¹1) = res(1 - Σ g)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

section Generic

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem adjugate_eq_smul_inv (Q : Matrix ι ι R) (hQ : IsUnit Q.det) :
    Q.adjugate = Q.det • Q⁻¹ := by
  rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hQ, one_smul]

/-- Row moments in inverse form. -/
theorem adj_moment (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (σ Y : ι → R) (t0 : R) :
    Q.det * t0 - ∑ i, σ i * ∑ k, Q.adjugate i k * Y k = Q.det * (t0 - σ ⬝ᵥ (Q⁻¹ *ᵥ Y)) := by
  rw [adjugate_eq_smul_inv Q hQ, mul_sub, dotProduct, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- Column moments in inverse form, for a symmetric core block. -/
theorem adj_moment_col (Q : Matrix ι ι R) (hQ : IsUnit Q.det) (hsym : Qᵀ = Q)
    (σ Y : ι → R) (t0 : R) :
    Q.det * t0 - ∑ j, (∑ k, Y k * Q.adjugate k j) * σ j =
      Q.det * (t0 - σ ⬝ᵥ (Q⁻¹ *ᵥ Y)) := by
  have hadj : ∀ k j, Q.adjugate k j = Q.adjugate j k := by
    intro k j
    have := congrFun (congrFun (Matrix.adjugate_transpose Q) j) k
    rw [hsym] at this
    simpa [Matrix.transpose_apply] using this
  rw [← adj_moment Q hQ σ Y t0]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hadj, mul_comm]

end Generic

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- In `GaussLoc p`, an element with nonzero residue is a unit. -/
theorem isUnit_of_res_ne (x : GaussLoc p) (hx : res p x ≠ 0) : IsUnit x := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (gaussIdeal p).primeCompl x
  dsimp only at hx ⊢
  have ha : phiP p a ≠ 0 := by
    intro h0
    apply hx
    exact (IsLocalization.lift_mk'_spec (M := (gaussIdeal p).primeCompl) (S := GaussLoc p)
      _ _ _ _).2 (by rw [h0, mul_zero])
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  refine (isUnit_of_phiP_ne p ha).mul (IsUnit.of_mul_eq_one
    (algebraMap (LocRing p)[X] (GaussLoc p) s) ?_)
  rw [IsLocalization.mk'_spec, map_one]

/-- Residue of a ring inverse of a unit. -/
theorem res_inverse (x : GaussLoc p) (hx : IsUnit x) : res p (Ring.inverse x) = (res p x)⁻¹ := by
  have h := congrArg (res p) (Ring.mul_inverse_cancel x hx)
  rw [map_mul, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

/-- The image of a node difference in `GaussLoc p`. -/
noncomputable abbrev ndL (p : ℕ) [Fact p.Prime] (a : ℕ) : GaussLoc p :=
  algebraMap (LocRing p)[X] (GaussLoc p) (nd p a)

theorem res_ndL_sub (a b : ℕ) :
    res p (ndL p a - ndL p b) = rfH p ((a : ZMod p)) - rfH p ((b : ZMod p)) := by
  rw [ndL, ndL, ← map_sub (algebraMap (LocRing p)[X] (GaussLoc p)), res_algebraMap,
    phiP_natCast_sub, map_sub]

theorem isUnit_ndL_sub {a b : ℕ} (h : (a : ZMod p) ≠ (b : ZMod p)) :
    IsUnit (ndL p a - ndL p b) := by
  refine isUnit_of_res_ne _ ?_
  rw [res_ndL_sub, ← map_sub]
  exact fun h0 => (sub_ne_zero.2 h) (rfH_injective (by rw [h0, map_zero]))

/-- The lifted norm is a unit of `GaussLoc p`. -/
theorem isUnit_nL (D : PoleData Fr p N) :
    IsUnit (algebraMap (LocRing p)[X] (GaussLoc p) (nL p Fr)) := by
  refine isUnit_of_res_ne _ ?_
  rw [res_algebraMap, phiP_nL D]
  exact fun h0 => D.norm_ne (rfH_injective (by rw [h0, map_zero]))

/-- **A Loewner entry across residues is `π` times a Loewner quotient.** -/
theorem loewner_split (D : PoleData Fr p N) {a b : ℕ} (ha : a < N) (hb : b < N)
    (hab : (a : ZMod p) ≠ (b : ZMod p)) (q : (LocRing p)[X])
    (hq : nL p Fr * (nd p b - nd p a) * q = PF p Fr b - PF p Fr a) :
    algebraMap (LocRing p)[X] (GaussLoc p) q = piL p *
      ((algebraMap _ (GaussLoc p) (PF1 p Fr b) *
          Ring.inverse (algebraMap _ (GaussLoc p) (nL p Fr)) -
        algebraMap _ (GaussLoc p) (PF1 p Fr a) * Ring.inverse (algebraMap _ (GaussLoc p) (nL p Fr))) *
        Ring.inverse (ndL p b - ndL p a)) := by
  set f := algebraMap (LocRing p)[X] (GaussLoc p)
  have hu := isUnit_nL D
  have hw := isUnit_ndL_sub (p := p) (Ne.symm hab)
  have h := congrArg f hq
  rw [PF_eq D hb, PF_eq D ha, map_mul, map_mul, map_sub, map_sub, map_mul, map_mul] at h
  have hu' := Ring.mul_inverse_cancel _ hu
  have hw' := Ring.mul_inverse_cancel _ hw
  change f (nL p Fr) * (ndL p b - ndL p a) * f q = piL p * f (PF1 p Fr b) - piL p * f (PF1 p Fr a)
    at h
  set u := f (nL p Fr)
  set w := ndL p b - ndL p a
  have e : f q = (Ring.inverse u * Ring.inverse w) * (u * w * f q) := by
    rw [show (Ring.inverse u * Ring.inverse w) * (u * w * f q) =
      (u * Ring.inverse u) * (w * Ring.inverse w) * f q by ring, hu', hw', one_mul, one_mul]
  rw [e, h]
  ring

end CatalanCore.Uniform.Content.UFMoments
