module

public import CatalanCore.Linalg.PrincipalDeletion
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! # Selecting a basis of coordinate evaluations

An injective map from a finite-dimensional space to a finite coordinate space
admits a bijective restriction to exactly its dimension many coordinates.
-/

namespace CatalanCore.Linalg.PrincipalDeletion

open Module Submodule

variable {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]
  [FiniteDimensional F P] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restrict a coordinate map to a finite selected coordinate set. -/
def restrictCoords (E : P →ₗ[F] (ι → F)) (s : Finset ι) : P →ₗ[F] (s → F) :=
  LinearMap.pi fun i => (LinearMap.proj i.val).comp E

/-- Exactly `finrank P` coordinates suffice, and the restricted map is bijective. -/
theorem exists_bijective_restrictCoords (E : P →ₗ[F] (ι → F)) (hE : Function.Injective E) :
    ∃ s : Finset ι, s.card = Module.finrank F P ∧ Function.Bijective (restrictCoords E s) := by
  classical
  let f : ι → Module.Dual F P := fun i => (LinearMap.proj i).comp E
  have hspan : Submodule.span F (Set.range f) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro p hp
    have hEp : E p ≠ 0 := fun h => hp (hE (by simpa using h))
    have hex : ∃ i, E p i ≠ 0 := by
      by_contra h
      push Not at h
      exact hEp (funext h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨f i, ⟨i, rfl⟩, hi⟩
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' F f
  letI : Fintype κ := Fintype.ofInjective a ha
  letI : DecidableEq κ := Classical.decEq _
  have hspan' : Submodule.span F (Set.range (f ∘ a)) = ⊤ := hsp.trans hspan
  let b : Basis κ F (Module.Dual F P) := Basis.mk hli (by rw [hspan'])
  have hdim : Module.finrank F P = Fintype.card κ := by
    rw [← Subspace.dual_finrank_eq]
    exact Module.finrank_eq_card_basis b
  let Eκ : P →ₗ[F] (κ → F) := LinearMap.pi fun j => f (a j)
  have hEi : Function.Injective Eκ := by
    intro p q hpq
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff F (p - q)).mp
    intro φ
    have hφ : φ ∈ Submodule.span F (Set.range (f ∘ a)) := by rw [hspan']; trivial
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨j, rfl⟩ := hφ
      have h := congrFun hpq j
      simpa [Eκ, f, map_sub, sub_eq_zero] using h
    | zero => simp
    | add φ ψ hφ hψ ihφ ihψ => simp [ihφ, ihψ]
    | smul c φ hφ ih => simp [ih]
  have hEs : Function.Surjective Eκ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simpa using hdim)).mp hEi
  let s : Finset ι := Finset.univ.image a
  have has : ∀ j, a j ∈ s := fun j => Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa [s, Finset.card_image_of_injective, ha] using hdim.symm
  · intro p q hpq
    apply hEi
    ext j
    exact congrFun hpq ⟨a j, has j⟩
  · intro target
    obtain ⟨p, hp⟩ := hEs (fun j => target ⟨a j, has j⟩)
    refine ⟨p, ?_⟩
    ext i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp i.2
    have hh := congrFun hp j
    simpa [restrictCoords, Eκ, f, hj] using hh

end CatalanCore.Linalg.PrincipalDeletion

#print axioms CatalanCore.Linalg.PrincipalDeletion.exists_bijective_restrictCoords
