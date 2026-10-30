module
public import CatalanMeasure.GenD.Uniform.Prefix.PhysicalCoordinates
public import CatalanMeasure.GenD.Uniform.Prefix.RowSupport
public import CatalanMeasure.GenD.Uniform.W.Core
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
@[expose] public section
set_option Elab.async false

/-!
# Atoms of the physical tiling give physical rows injectively

The full physical tiling is the linear equivalence
`Prefix.physicalTilingEquiv b h p : TilingCoordinates b h ≃ₗ (Fin (b*p+1) → K)` (centres and
both members of every noncentral pair of every block, including both outer centres).  The actual
rows are the interval `[lo, lo+n)` of the enlarged index (`Prefix.intervalRows`).

A W-construction is a subspace `S` of tiling coordinates whose image is supported on the actual
interval; `physicalAtoms` is then an injective linear map `S → (Fin n → K)` (the injection
direction of the prefix theorem is all Theorem W needs).  `atomRows` is the generic version: a
linearly independent finite family of row vectors.
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {K : Type*} [Field K]

/-- Rows of a subspace of a tiling supported on the actual row interval. -/
def supportedRows {X : Type*} [AddCommGroup X] [Module K X] {total : ℕ}
    (T : X →ₗ[K] (Fin total → K)) (lo n : ℕ) (hlen : lo + n ≤ total) (S : Submodule K X)
    (hS : ∀ x ∈ S, T x ∈ intervalRows (K := K) lo n total) : S →ₗ[K] (Fin n → K) :=
  (intervalRowsEquiv (K := K) lo n total hlen).symm.toLinearMap.comp
    ((T.comp S.subtype).codRestrict _ (fun x => hS x.1 x.2))

theorem supportedRows_apply {X : Type*} [AddCommGroup X] [Module K X] {total : ℕ}
    (T : X →ₗ[K] (Fin total → K)) (lo n : ℕ) (hlen : lo + n ≤ total) (S : Submodule K X)
    (hS : ∀ x ∈ S, T x ∈ intervalRows (K := K) lo n total) (x : S) (j : Fin n) :
    supportedRows T lo n hlen S hS x j = T x.1 ⟨lo + j.val, by omega⟩ := rfl

theorem supportedRows_injective {X : Type*} [AddCommGroup X] [Module K X] {total : ℕ}
    (T : X →ₗ[K] (Fin total → K)) (hT : Function.Injective T) (lo n : ℕ)
    (hlen : lo + n ≤ total) (S : Submodule K X)
    (hS : ∀ x ∈ S, T x ∈ intervalRows (K := K) lo n total) :
    Function.Injective (supportedRows T lo n hlen S hS) := by
  intro a b hab
  have h1 := (intervalRowsEquiv (K := K) lo n total hlen).symm.injective hab
  have h2 : T a.1 = T b.1 := congrArg Subtype.val h1
  exact Subtype.ext (hT h2)

/-- **Atoms of the full physical tiling.**  A subspace of tiling coordinates supported on the
actual rows `[lo, lo+n)` maps injectively to the physical row space. -/
def physicalAtoms (b h p : ℕ) (hp : p = 2 * h + 1) (h2 : (2 : K) ≠ 0) (lo n : ℕ)
    (hlen : lo + n ≤ b * p + 1) (S : Submodule K (TilingCoordinates (K := K) b h))
    (hS : ∀ x ∈ S, physicalTilingEquiv b h p hp h2 x ∈ intervalRows (K := K) lo n (b * p + 1)) :
    S →ₗ[K] (Fin n → K) :=
  supportedRows (physicalTilingEquiv b h p hp h2).toLinearMap lo n hlen S hS

theorem physicalAtoms_injective (b h p : ℕ) (hp : p = 2 * h + 1) (h2 : (2 : K) ≠ 0) (lo n : ℕ)
    (hlen : lo + n ≤ b * p + 1) (S : Submodule K (TilingCoordinates (K := K) b h))
    (hS : ∀ x ∈ S, physicalTilingEquiv b h p hp h2 x ∈ intervalRows (K := K) lo n (b * p + 1)) :
    Function.Injective (physicalAtoms b h p hp h2 lo n hlen S hS) :=
  supportedRows_injective _ (physicalTilingEquiv b h p hp h2).injective lo n hlen S hS

/-- A finite family of atom rows: `x ↦ Σ_a x_a • row_a`. -/
def atomRows {α : Type*} [Fintype α] {n : ℕ} (row : α → (Fin n → K)) :
    (α → K) →ₗ[K] (Fin n → K) :=
  Fintype.linearCombination K row

theorem atomRows_apply {α : Type*} [Fintype α] {n : ℕ} (row : α → (Fin n → K)) (x : α → K) :
    atomRows row x = ∑ a, x a • row a := rfl

theorem atomRows_injective {α : Type*} [Fintype α] {n : ℕ} {row : α → (Fin n → K)}
    (h : LinearIndependent K row) : Function.Injective (atomRows row) :=
  (linearIndependent_iff_injective_fintypeLinearCombination).mp h

/-- Composing an injective atom map with an injective coordinate map (a polynomial slot space,
a profile tensor, a section) keeps it injective. -/
theorem atoms_comp_injective {A B : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B]
    [Module K B] {n : ℕ} (ι : B →ₗ[K] (Fin n → K)) (g : A →ₗ[K] B)
    (hι : Function.Injective ι) (hg : Function.Injective g) :
    Function.Injective (ι.comp g) := hι.comp hg

end
end CatalanMeasure.GenD.Uniform.W
