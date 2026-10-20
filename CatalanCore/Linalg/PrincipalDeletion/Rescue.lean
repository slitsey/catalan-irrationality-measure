module

public import CatalanCore.Linalg.PrincipalDeletion.Coordinates

@[expose] public section

namespace CatalanCore.Linalg.PrincipalDeletion

open Matrix

variable {F : Type*} [Field F] {P : Type*} [AddCommGroup P] [Module F P]
  [FiniteDimensional F P] {ι L : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

/-- Select a simultaneous left/right kernel coordinate basis among distinguished
indices, and delete only those principal coordinates. -/
theorem exists_principal_compl_ne_zero (M : Matrix ι ι F) (c : L → ι)
    (hc : Function.Injective c) (R Q : P →ₗ[F] (ι → F))
    (E : P →ₗ[F] (L → F)) (a b : L → F)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hR : ∀ v : ι → F, M *ᵥ v = 0 → ∃ p, R p = v)
    (hQ : ∀ p, M.transpose *ᵥ Q p = 0)
    (hRc : ∀ p i, R p (c i) = a i * E p i)
    (hQc : ∀ p i, Q p (c i) = b i * E p i)
    (hE : Function.Injective E) :
    ∃ s : Finset L, s.card = Module.finrank F P ∧
      (M.submatrix (Subtype.val : {i // i ∉ s.image c} → ι) Subtype.val).det ≠ 0 := by
  classical
  obtain ⟨s, hs, hEs⟩ := exists_bijective_restrictCoords E hE
  refine ⟨s, hs, det_principal_compl_ne_zero M (s.image c) ?_ ?_⟩
  · intro v hv hvi
    obtain ⟨p, hp⟩ := hR v hv
    have hEp : restrictCoords E s p = 0 := by
      ext i
      have h := hvi (c i) (Finset.mem_image.mpr ⟨i, i.2, rfl⟩)
      rw [← hp, hRc] at h
      exact (mul_eq_zero.mp h).resolve_left (ha i)
    have hp0 : p = 0 := hEs.1 (by simpa using hEp)
    rw [← hp, hp0, map_zero]
  · intro target
    have him : ∀ i : s, c i ∈ s.image c := fun i =>
      Finset.mem_image.mpr ⟨i, i.2, rfl⟩
    obtain ⟨p, hp⟩ := hEs.2 (fun i => target ⟨c i, him i⟩ / b i)
    refine ⟨Q p, hQ p, ?_⟩
    intro j
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp j.2
    have he := congrFun hp ⟨i, hi⟩
    have hpi : E p i = target ⟨c i, him ⟨i, hi⟩⟩ / b i := he
    have hq := hQc p i
    rw [hpi] at hq
    have hmul : b i * (target ⟨c i, him ⟨i, hi⟩⟩ / b i) =
        target ⟨c i, him ⟨i, hi⟩⟩ := by field_simp [hb i]
    rw [hmul] at hq
    simpa [hij] using hq

end CatalanCore.Linalg.PrincipalDeletion

#print axioms CatalanCore.Linalg.PrincipalDeletion.exists_principal_compl_ne_zero
