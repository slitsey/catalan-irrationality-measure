module

public import CatalanCore.Uniform.Content.UFMoments.AltPrice

@[expose] public section

/-!
# `B₀ ≠ 0` always holds in the scaled gauge

For any border node `t₀` and its Loewner row `σ₀`, `B₀ = res(1 - σ₀ Q⁻¹ 1) ≠ 0`: by the matrix
determinant lemma `det Q̄ · (1 - σ̄ Q̄⁻¹ 1) = det(Q̄ - 1 σ̄ᵀ)`, and `Q̄ - 1 σ̄ᵀ = X·I + const` is again a
characteristic matrix, with monic determinant.  So the hypothesis `hB0` of `s7_twoTerm` /
`altSmithJKDatum_S7` is discharged (`hB0_auto`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

section Generic

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_border_field (A : Matrix ι ι K) (hA : A.det ≠ 0) (v : ι → K) :
    (A + replicateCol Unit (-1 : ι → K) * replicateRow Unit v).det =
      A.det * (1 - v ⬝ᵥ (A⁻¹ *ᵥ 1)) := by
  rw [det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.2 hA), Matrix.det_unique (n := Unit)]
  congr 1
  simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, Pi.neg_apply, Pi.one_apply, mul_neg, mul_one, Finset.sum_neg_distrib,
    dotProduct, mulVec]
  rw [sub_eq_add_neg]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]

end Generic

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem loewRow_rel (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (t0 : ℕ) (ht0 : t0 < N) :
    ∀ a, nL p Fr * (nd p (c a) - nd p t0) * loewRow p Fr c t0 a = PF p Fr (c a) - PF p Fr t0 := by
  intro a
  have h := const_commutator D ht0 (hc a) (D.square_mem hN ht0 (hc a))
  have e : loewRow p Fr c t0 a = Polynomial.C ⟨(p : ℚ) ^ 2 * Fr.Mn t0 (c a),
      D.square_mem hN ht0 (hc a)⟩ :=
    congrArg Polynomial.C (Subtype.ext (Hybrid.liftQ_val (D.square_mem hN ht0 (hc a))))
  rw [e]; exact h

/-- **`B₀ ≠ 0`** for any border node of the scaled lift. -/
theorem hB0_auto (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (t0 : ℕ) (ht0 : t0 < N) :
    res p (1 - ∑ j, (sOwn c t0 (loewRow p Fr c t0) ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁)⁻¹) j) ≠ 0 := by
  set Q := (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  set σ0 := loewRow p Fr c t0
  have hQ := sLift_core_rel D hN c xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)
  rw [← node_alpha_res D c hc Q hQ hdet t0 ht0 σ0 (loewRow_rel D hN c hc t0 ht0)]
  set fL := algebraMap (LocRing p)[X] (GaussLoc p)
  have hQu := isUnit_map_det Q hdet
  set Qb : Matrix ι ι (RatFunc (ZMod p)) := Q.map (phiP p)
  have hQb : (Q.map fL).map (res p) = Qb := by
    ext a b; simp only [Matrix.map_apply, Qb, fL, res_algebraMap]
  have hres : res p (1 - (fun a => fL (σ0 a)) ⬝ᵥ ((Q.map fL)⁻¹ *ᵥ 1)) =
      1 - (fun a => phiP p (σ0 a)) ⬝ᵥ (Qb⁻¹ *ᵥ 1) := by
    rw [map_sub, map_one, RingHom.map_dotProduct]
    congr 2
    · funext a; simp only [Function.comp, fL, res_algebraMap]
    · funext a
      simp only [Function.comp]
      rw [RingHom.map_mulVec, ← map_inv_of_unit (res p) _ hQu, hQb]
      congr 1
      funext b; simp
  rw [hres]
  intro h0
  have hdetb : Qb.det ≠ 0 := by
    have : Qb.det = phiP p Q.det := by
      show (Q.map (phiP p)).det = _
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [this]; exact hdet
  have hd := det_border_field Qb hdetb (fun a => phiP p (σ0 a))
  rw [h0, mul_zero] at hd
  -- the bordered matrix is a characteristic matrix
  set K0 : Matrix ι ι (ZMod p) := Matrix.of fun a b =>
    redQ p (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t0 (c b))) -
      redQ p (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c b)))
  have hchar : Qb + replicateCol Unit (-1 : ι → RatFunc (ZMod p)) *
      replicateRow Unit (fun a => phiP p (σ0 a)) =
      (charmatrix K0).map (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := by
    ext a b
    simp only [Qb, Matrix.add_apply, Matrix.map_apply, Matrix.mul_apply, Matrix.replicateCol_apply,
      Matrix.replicateRow_apply, Pi.neg_apply, Pi.one_apply, Finset.univ_unique,
      Finset.sum_singleton, neg_one_mul, charmatrix_apply, K0, Matrix.of_apply, σ0, loewRow]
    have hQe : Q a b = Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c b))) +
        (if a = b then (X : (LocRing p)[X]) else 0) := sLift_core_entry D hN c xs ys hc hx hy a b
    rw [hQe]
    by_cases hab : a = b
    · subst hab
      simp [phiP_C, phiP_X, rfC, rfX, Matrix.diagonal_apply_eq]
      ring
    · simp [phiP_C, rfC, Matrix.diagonal_apply_ne _ hab, hab]
      ring
  rw [hchar] at hd
  have : ((charmatrix K0).map (algebraMap (ZMod p)[X] (RatFunc (ZMod p)))).det =
      algebraMap (ZMod p)[X] (RatFunc (ZMod p)) K0.charpoly := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
  rw [this, map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))] at hd
  exact (Matrix.charpoly_monic K0).ne_zero hd

end CatalanCore.Uniform.Content.UFMoments
