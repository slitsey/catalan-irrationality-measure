module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Abstract linear algebra for the nondegeneracy `hD2`

`perp_of_range`: if `Xᵀ` is injective, `N` is injective with `card ι = r`, and `Xᵀ` maps a spanning
family of `F^r` into `range N`, then `ker X ⊆ ker Nᵀ`.
-/

@[expose] public section

open Matrix Module

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- `ker X ⊆ ker Nᵀ` when `range Xᵀ = range N` (obtained by a dimension count). -/
theorem perp_of_range {r q : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (X : Matrix (Fin r) (Fin q) F) (N : Matrix (Fin q) ι F) (C : Matrix (Fin r) κ F)
    (hcard : Fintype.card ι = r)
    (hXi : ∀ v, Xᵀ *ᵥ v = 0 → v = 0) (hNi : ∀ a, N *ᵥ a = 0 → a = 0)
    (hCs : Submodule.span F (Set.range fun j : κ => fun i => C i j) = ⊤)
    (hcol : ∀ j : κ, Xᵀ *ᵥ (fun i => C i j) ∈ LinearMap.range (Matrix.mulVecLin N))
    (y : Fin q → F) (hy : X *ᵥ y = 0) : Nᵀ *ᵥ y = 0 := by
  set T : (Fin r → F) →ₗ[F] (Fin q → F) := Matrix.mulVecLin Xᵀ with hT
  set Nl : (ι → F) →ₗ[F] (Fin q → F) := Matrix.mulVecLin N with hNl
  have hTinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv; exact hXi v hv
  have hNinj : Function.Injective Nl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv; exact hNi v hv
  have hle : LinearMap.range T ≤ LinearMap.range Nl := by
    rintro w ⟨v, rfl⟩
    have hv : v ∈ Submodule.span F (Set.range fun j : κ => fun i => C i j) := by rw [hCs]; trivial
    have : T v ∈ Submodule.map T (Submodule.span F (Set.range fun j : κ => fun i => C i j)) :=
      Submodule.mem_map_of_mem hv
    refine (Submodule.map_span_le T _ (LinearMap.range Nl)).2 ?_ this
    rintro _ ⟨j, rfl⟩
    exact hcol j
  have h1 : finrank F (LinearMap.range T) = r := by
    rw [LinearMap.finrank_range_of_inj hTinj]; simp
  have h2 : finrank F (LinearMap.range Nl) = r := by
    rw [LinearMap.finrank_range_of_inj hNinj]; simp [hcard]
  have heq : LinearMap.range T = LinearMap.range Nl :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h1, h2])
  funext j
  have hmem : Nl (Pi.single j 1) ∈ LinearMap.range T := by rw [heq]; exact ⟨_, rfl⟩
  obtain ⟨v, hv⟩ := hmem
  have hcolj : Nl (Pi.single j 1) = fun i => N i j := by
    simp only [hNl, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]; rfl
  have e1 : (fun i => N i j) = Xᵀ *ᵥ v := by rw [← hcolj, ← hv]; rfl
  have e2 : (Nᵀ *ᵥ y) j = (fun i => N i j) ⬝ᵥ y := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [e2, e1, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hy, dotProduct_zero]
  rfl

end CatalanCore.Star.Leonard
