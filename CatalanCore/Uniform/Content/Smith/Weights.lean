module

public import CatalanCore.Uniform.Content.Smith.Derived

@[expose] public section

/-!
# Vanishing of the derived-frame weights: transport and top extension

The weight of the residue `c` in the derived frame is
`v(c) = B² (w(c) - w_J) + γ_J - γ(c)`, where `γ(c) = u_cᵀ Q_c⁻¹ u_c` is the quadratic form of the
core chain at `c` (`Q_c` the leading core block, `u_c` the source vector) and `w` is the cyclic
step of the regular prefix.  Two identities make `v` vanish:

* `weight_transport` — if the chain of `c` is the *transport* of the chain of `J` (an index
  bijection carrying `Q_J, u_J` to `Q_c, u_c`) and `w(c) = w_J`, then `v(c) = 0`
  (`gamma_reindex`: `γ` is invariant under relabelling);
* `weight_topext` — if the chain of `c` is the chain of `J` plus one top node, and the new source
  entry equals `b ⬝ Q_J⁻¹ u_J` (the identity `bᵀ Q⁻¹ u = A - B L_J`), then `Q_c⁻¹ u_c = (Q_J⁻¹ u_J, 0)`
  and `γ(c) = γ_J` (`gamma_topExt`), so `v(c) = 0` for equal `w`, for any diagonal entry.
-/

open Finset Matrix

namespace CatalanCore.Uniform.Content.Smith

section Gamma

variable {K : Type*} [Field K] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The quadratic form `γ(Q,u) = uᵀ Q⁻¹ u` of a core chain. -/
noncomputable def gamma (Q : Matrix n n K) (u : n → K) : K := u ⬝ᵥ (Q⁻¹ *ᵥ u)

/-- **Transport identity.** `γ` is invariant under relabelling the chain. -/
theorem gamma_reindex (e : m ≃ n) (Q : Matrix n n K) (u : n → K) :
    gamma (Q.submatrix e e) (u ∘ e) = gamma Q u := by
  unfold gamma
  rw [Matrix.inv_submatrix_equiv]
  have h : (Q⁻¹.submatrix e e *ᵥ (u ∘ e)) = (Q⁻¹ *ᵥ u) ∘ e := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Function.comp_apply]
    exact Fintype.sum_equiv e _ _ (fun j => rfl)
  rw [h]
  simp only [dotProduct, Function.comp_apply]
  exact Fintype.sum_equiv e _ _ (fun j => rfl)

/-- **Top-extension identity.** Adding one top node `none` to a chain whose new source entry is
`b ⬝ Q⁻¹ u` (`b` the new row) leaves `γ` unchanged, for any diagonal entry `Q⁺ none none`. -/
theorem gamma_topExt (Qp : Matrix (Option n) (Option n) K) (up : Option n → K)
    (hQ : (Qp.submatrix some some).det ≠ 0) (hQp : Qp.det ≠ 0)
    (htop : (fun j => Qp none (some j)) ⬝ᵥ ((Qp.submatrix some some)⁻¹ *ᵥ (up ∘ some)) =
      up none) :
    gamma Qp up = gamma (Qp.submatrix some some) (up ∘ some) := by
  set Q := Qp.submatrix some some with hQdef
  set y : n → K := Q⁻¹ *ᵥ (up ∘ some) with hy
  let x : Option n → K := fun o => o.elim 0 y
  have hQy : Q *ᵥ y = up ∘ some := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hQ),
      Matrix.one_mulVec]
  have hx : Qp *ᵥ x = up := by
    ext o
    cases o with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, x, Option.elim_none,
        Option.elim_some, mul_zero, zero_add]
      exact htop
    | some i =>
      have := congrFun hQy i
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, x, Option.elim_none,
        Option.elim_some, mul_zero, zero_add, Function.comp_apply] at this ⊢
      simpa [hQdef, Matrix.submatrix_apply] using this
  have hinv : Qp⁻¹ *ᵥ up = x := by
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hQp),
      Matrix.one_mulVec]
  unfold gamma
  rw [hinv, ← hy]
  simp [dotProduct, Fintype.sum_option, x]

end Gamma

section Weight

variable {K : Type*} [Field K]

/-- The derived-frame weight `v(c) = B²(w(c) - w_J) + γ_J - γ(c)`. -/
def weight (B wJ γJ wc γc : K) : K := B ^ 2 * (wc - wJ) + γJ - γc

/-- The weight vanishes when the chain of `c` is the transport of the chain of `J` and `w(c) = w_J`. -/
theorem weight_transport {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (B wJ wc : K) (e : m ≃ n) (QJ : Matrix n n K) (uJ : n → K) (Qc : Matrix m m K) (uc : m → K)
    (hQ : Qc = QJ.submatrix e e) (hu : uc = uJ ∘ e) (hw : wc = wJ) :
    weight B wJ (gamma QJ uJ) wc (gamma Qc uc) = 0 := by
  rw [hQ, hu, gamma_reindex, hw]; unfold weight; ring

/-- The weight vanishes on top extensions of the chain of `J` (same `w`). -/
theorem weight_topext {n : Type*} [Fintype n] [DecidableEq n] (B wJ wc : K)
    (Qp : Matrix (Option n) (Option n) K) (up : Option n → K)
    (hQ : (Qp.submatrix some some).det ≠ 0) (hQp : Qp.det ≠ 0)
    (htop : (fun j => Qp none (some j)) ⬝ᵥ ((Qp.submatrix some some)⁻¹ *ᵥ (up ∘ some)) =
      up none) (hw : wc = wJ) :
    weight B wJ (gamma (Qp.submatrix some some) (up ∘ some)) wc (gamma Qp up) = 0 := by
  rw [gamma_topExt Qp up hQ hQp htop, hw]; unfold weight; ring

end Weight

end CatalanCore.Uniform.Content.Smith
