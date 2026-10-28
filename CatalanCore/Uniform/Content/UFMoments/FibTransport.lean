module

public import CatalanCore.Uniform.Content.UFMoments.TwoTermStep

@[expose] public section

/-!
# UF moments: the derived weight vanishes on the joint type (transport modulo `p`)

* `fibMom_fiber`: the fiber moment `m(τ)` is computed inside the colour block;
* `fibMom_transport`: along a chain equivalence with blocks equal modulo `π` and `y` equal modulo
  `π`, `m(τ) = m(τ₀)`;
* `wT_arc`: the cyclic step is constant across a window without pole residues.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

section Generic

variable {R : Type*} [CommRing R] {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem map_inv_of_unit (f : R →+* k) {o : Type*} [Fintype o] [DecidableEq o]
    (M : Matrix o o R) (hM : IsUnit M.det) : (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hM, Matrix.map_one _ f.map_zero f.map_one]

/-- The fiber moment inside the colour block. -/
theorem fiber_moment (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ : ZMod p) (y : ι → R) (f : R →+* k) :
    ∑ a ∈ univ.filter (fun a => col a = τ), f ((D⁻¹ *ᵥ y) a) * f (y a) =
      ∑ i : {a // col a = τ}, f (((blk D col τ)⁻¹ *ᵥ fun j => y j.1) i) * f (y i.1) := by
  have hinv := inv_colour_zero D col hD hb
  rw [Finset.sum_subtype (univ.filter (fun a => col a = τ)) (p := fun a => col a = τ)
    (fun a => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [(inv_restrict D col hD hb τ).2]
  simp only [mulVec, dotProduct, blk, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun a => col a = τ)]
  have h0 : ∑ j : {a // ¬ col a = τ}, D⁻¹ i.1 j.1 * y j.1 = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [hinv i.1 j.1 (by rw [i.2]; exact Ne.symm j.2), zero_mul]
  rw [h0, add_zero]

/-- **Transport of the fiber moment modulo `π`.** -/
theorem fiber_moment_transport (D : Matrix ι ι R) (col : ι → ZMod p) (hD : IsUnit D.det)
    (hb : ∀ a b, col a ≠ col b → D a b = 0) (τ τ0 : ZMod p)
    (e : {a // col a = τ} ≃ {a // col a = τ0}) (y : ι → R) (f : R →+* k)
    (hDD : ∀ i j : {a // col a = τ0}, f (D (e.symm i).1 (e.symm j).1) = f (D i.1 j.1))
    (hy : ∀ i : {a // col a = τ0}, f (y (e.symm i).1) = f (y i.1)) :
    ∑ a ∈ univ.filter (fun a => col a = τ), f ((D⁻¹ *ᵥ y) a) * f (y a) =
      ∑ a ∈ univ.filter (fun a => col a = τ0), f ((D⁻¹ *ᵥ y) a) * f (y a) := by
  rw [fiber_moment D col hD hb τ y f, fiber_moment D col hD hb τ0 y f,
    ← Equiv.sum_comp e.symm]
  have hU := (inv_restrict D col hD hb τ).1
  have hU0 := (inv_restrict D col hD hb τ0).1
  have hUs : IsUnit ((blk D col τ).submatrix e.symm e.symm).det := by
    rw [Matrix.det_submatrix_equiv_self]; exact hU
  have hmap : ((blk D col τ).submatrix e.symm e.symm).map f = (blk D col τ0).map f := by
    ext i j; simp only [Matrix.map_apply, Matrix.submatrix_apply, blk]; exact hDD i j
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hy j]
  congr 1
  have e1 : ((blk D col τ)⁻¹ *ᵥ fun i => y i.1) (e.symm j) =
      (((blk D col τ).submatrix e.symm e.symm)⁻¹ *ᵥ fun i => y (e.symm i).1) j := by
    rw [Matrix.inv_submatrix_equiv]
    simp only [mulVec, dotProduct, Matrix.submatrix_apply]
    exact (Equiv.sum_comp e.symm (fun i => (blk D col τ)⁻¹ (e.symm j) i * y i.1)).symm
  rw [e1, RingHom.map_mulVec, RingHom.map_mulVec, ← map_inv_of_unit f _ hUs,
    ← map_inv_of_unit f _ hU0, hmap]
  congr 1
  funext i
  simp only [Function.comp]
  exact hy i

end Generic

end CatalanCore.Uniform.Content.UFMoments
