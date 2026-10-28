module

public import CatalanCore.Uniform.Content.UFMember.Lift

@[expose] public section

/-!
# UF member package, obligation O3: the border Schur complement is divisible by `p`

For the scaled-gauge lift `sLift` of the hybrid matrix, suppose

* (`hfib`) a Loewner value between nodes in DIFFERENT residue classes has at most one `p` in its
  denominator, so its `p²`-value vanishes modulo `p`;
* (`hdist`) no border row node is congruent to a border column node modulo `p`.

Then modulo `p` the core block `Q` is block diagonal over residue classes, hence so is its
adjugate (`adjugate_eq_zero_of_color`), the border block `T'` vanishes, and every term of
`S' adj(Q) R'` links a border row to a border column through one residue class, which is
impossible.  So `det Q · T' - S' adj Q R' = p · W` exactly (`sLift_schur_eq`), with
`W = schurW` (O3).
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanCore.Uniform.Content.UFMember

section Color

variable {K : Type*} [Field K] {n α : Type*} [Fintype n] [DecidableEq n] [DecidableEq α]

/-- The inverse of a matrix that is block diagonal for a colouring is block diagonal. -/
theorem inv_eq_zero_of_color (M : Matrix n n K) (col : n → α)
    (hM : ∀ a b, col a ≠ col b → M a b = 0) (hdet : M.det ≠ 0) :
    ∀ a b, col a ≠ col b → M⁻¹ a b = 0 := by
  intro a b hab
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  let D : Matrix n n K := Matrix.diagonal fun x => if col x = col a then 1 else 0
  have hDM : D * M = M * D := by
    ext x y
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hxy : col x = col y
    · simp [hxy]
    · rw [hM x y hxy]; simp
  have hcomm : M⁻¹ * D = D * M⁻¹ := by
    calc M⁻¹ * D = M⁻¹ * D * (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
      _ = M⁻¹ * (D * M) * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = M⁻¹ * (M * D) * M⁻¹ := by rw [hDM]
      _ = (M⁻¹ * M) * D * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = D * M⁻¹ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h := congrFun (congrFun hcomm a) b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rw [if_neg (Ne.symm hab), mul_zero, if_pos rfl, one_mul] at h
  exact h.symm

/-- The adjugate of a block-diagonal matrix is block diagonal. -/
theorem adjugate_eq_zero_of_color (M : Matrix n n K) (col : n → α)
    (hM : ∀ a b, col a ≠ col b → M a b = 0) (hdet : M.det ≠ 0) :
    ∀ a b, col a ≠ col b → M.adjugate a b = 0 := by
  intro a b hab
  have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hdet
  have e : M.adjugate = M.det • M⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.mul_inverse_cancel _ hu, one_smul]
  rw [e, Matrix.smul_apply, inv_eq_zero_of_color M col hM hdet a b hab, smul_zero]

end Color

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- A rational with `p · x` integral has `p² x` integral with zero reduction. -/
lemma redQ_sq_eq_zero {x : ℚ} (h : (p : ℚ) * x ∈ LocRing p) (h2 : (p : ℚ) ^ 2 * x ∈ LocRing p) :
    redQ p ⟨(p : ℚ) ^ 2 * x, h2⟩ = 0 := by
  have e : (⟨(p : ℚ) ^ 2 * x, h2⟩ : LocRing p) = ((p : ℕ) : LocRing p) * ⟨(p : ℚ) * x, h⟩ := by
    apply Subtype.ext
    simp only [Subring.coe_mul, Subring.coe_natCast]
    ring
  rw [e, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- **O3.** The scaled border Schur complement of the lift vanishes modulo `p`. -/
theorem sLift_schur_dvd (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p)
    (hfib : ∀ i j, ((rowNode c xs i : ℕ) : ZMod p) ≠ ((colNode c ys j : ℕ) : ZMod p) →
      (p : ℚ) * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (i j : κ) :
    Polynomial.C ((p : ℕ) : LocRing p) ∣
      ((sLift c xs ys hint).toBlocks₁₁.det • (sLift c xs ys hint).toBlocks₂₂ -
        (sLift c xs ys hint).toBlocks₂₁ * (sLift c xs ys hint).toBlocks₁₁.adjugate *
          (sLift c xs ys hint).toBlocks₁₂) i j := by
  classical
  set A := sLift c xs ys hint
  set Q := A.toBlocks₁₁
  rw [← phiP_eq_zero_iff]
  -- reductions of the constant entries
  have hz : ∀ u v, ((rowNode c xs u : ℕ) : ZMod p) ≠ ((colNode c ys v : ℕ) : ZMod p) →
      phiP p (Polynomial.C (sConst c xs ys hint u v)) = 0 := by
    intro u v huv
    rw [phiP_C]
    simp only [sConst, Matrix.of_apply]
    rw [redQ_sq_eq_zero (hfib u v huv) (hint u v)]
    exact rfC_zero p
  have hQ0 : ∀ a b, ((c a : ℕ) : ZMod p) ≠ ((c b : ℕ) : ZMod p) → (Q.map (phiP p)) a b = 0 := by
    intro a b hab
    have hne : a ≠ b := fun h => hab (by rw [h])
    simp only [Matrix.map_apply, Q, A, sLift, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.add_apply,
      Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.smul_apply, Matrix.one_apply_ne hne,
      smul_zero, add_zero]
    exact hz (Sum.inl a) (Sum.inl b) hab
  have hdetQ : (Q.map (phiP p)).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact sLift_core_det c xs ys hint
  have hadj : ∀ a b, ((c a : ℕ) : ZMod p) ≠ ((c b : ℕ) : ZMod p) →
      phiP p (Q.adjugate a b) = 0 := by
    intro a b hab
    have h := adjugate_eq_zero_of_color (Q.map (phiP p)) (fun a => ((c a : ℕ) : ZMod p))
      hQ0 hdetQ a b hab
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate] at h
    exact h
  have hT : phiP p (A.toBlocks₂₂ i j) = 0 := by
    simp only [A, sLift, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, add_zero]
    exact hz (Sum.inr i) (Sum.inr j) (by simpa [rowNode, colNode] using hdist i j)
  have hS : ∀ a, ((xs i : ℕ) : ZMod p) ≠ ((c a : ℕ) : ZMod p) →
      phiP p (A.toBlocks₂₁ i a) = 0 := by
    intro a ha
    simp only [A, sLift, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply,
      Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, add_zero]
    exact hz (Sum.inr i) (Sum.inl a) (by simpa [rowNode, colNode] using ha)
  have hR : ∀ b, ((c b : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p) →
      phiP p (A.toBlocks₁₂ b j) = 0 := by
    intro b hb
    simp only [A, sLift, Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply,
      Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, add_zero]
    exact hz (Sum.inl b) (Sum.inr j) (by simpa [rowNode, colNode] using hb)
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, hT, mul_zero, zero_sub,
    neg_eq_zero, Matrix.mul_apply, map_sum]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [map_mul, map_mul]
  by_cases h1 : ((xs i : ℕ) : ZMod p) = ((c a : ℕ) : ZMod p)
  · by_cases h2 : ((c a : ℕ) : ZMod p) = ((c b : ℕ) : ZMod p)
    · have h3 : ((c b : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p) := by
        rw [← h2, ← h1]; exact hdist i j
      rw [hR b h3, mul_zero]
    · rw [hadj a b h2, mul_zero, zero_mul]
  · rw [hS a h1, zero_mul, zero_mul]

/-- The divided border Schur complement `W = Sch / p`. -/
noncomputable def schurW (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p) :
    Matrix κ κ (LocRing p)[X] :=
  Matrix.of fun i j => quotP p
    (((sLift c xs ys hint).toBlocks₁₁.det • (sLift c xs ys hint).toBlocks₂₂ -
      (sLift c xs ys hint).toBlocks₂₁ * (sLift c xs ys hint).toBlocks₁₁.adjugate *
        (sLift c xs ys hint).toBlocks₁₂) i j)

/-- **O3, exact form** `det Q · T' - S' adj Q R' = p · W`. -/
theorem sLift_schur_eq (c : ι → ℕ) (xs ys : κ → ℕ)
    (hint : ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p)
    (hfib : ∀ i j, ((rowNode c xs i : ℕ) : ZMod p) ≠ ((colNode c ys j : ℕ) : ZMod p) →
      (p : ℚ) * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) :
    (sLift c xs ys hint).toBlocks₁₁.det • (sLift c xs ys hint).toBlocks₂₂ -
        (sLift c xs ys hint).toBlocks₂₁ * (sLift c xs ys hint).toBlocks₁₁.adjugate *
          (sLift c xs ys hint).toBlocks₁₂ =
      Polynomial.C ((p : ℕ) : LocRing p) • schurW c xs ys hint := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul, schurW, Matrix.of_apply,
    quotP_spec p (sLift_schur_dvd c xs ys hint hfib hdist i j)]

end CatalanCore.Uniform.Content.UFMember
