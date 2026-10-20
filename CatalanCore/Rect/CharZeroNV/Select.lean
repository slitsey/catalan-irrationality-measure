module

public import CatalanCore.Rect.CharZeroNV.KernelCoordinates
public import CatalanCore.Linalg.PrincipalDeletion.Rescue

@[expose] public section

/-! # Characteristic-zero common-node deletion nonvanishing

The characteristic-zero interpolation space supplies the common coordinates
to the existing principal-deletion selector. No prime window, cross-border
inverse, spectral theorem, or separate adjugate proof is used.
-/

open Polynomial Finset Matrix Module
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
  {D A : K[X]} {r m : ℕ}

theorem exists_common_deletion (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (hpole : IsolatedIntegerPole D A)
    (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1) (hr : 1 ≤ r)
    (f tau : K → K) (hf : ∀ i : ℕ, f (i : K) = data.f i)
    (ht : ∀ i : ℕ, tau (i : K) = data.tau i) :
    ∃ s : Finset (Fin r), s.card ≤ 1 ∧
      ((loewnerMatrix G f tau).submatrix
        (Subtype.val : {i // i ∉ s.image G.common} → G.rows) Subtype.val).det ≠ 0 := by
  let P := pairSpace data (r + 2 * m) r (r + m - 1)
  have hE : Function.Injective (commonEval data r m) :=
    commonEval_injective data hpole hD hA r m hr
  letI : FiniteDimensional K P := FiniteDimensional.of_injective (commonEval data r m) hE
  have hdim : finrank K P ≤ 1 := by
    by_cases hn : 2 ≤ r + m
    · exact pairSpace_finrank_le_one data hpole hD hA r m hr hn
    · have hr1 : r = 1 := by omega
      have hh := (commonEval data r m).finrank_le_finrank_of_injective hE
      simpa [hr1] using hh
  obtain ⟨s, hs, hdet⟩ := CatalanCore.Linalg.PrincipalDeletion.exists_principal_compl_ne_zero
    (loewnerMatrix G f tau) G.common G.common_injective
    (rightCoords G data) (leftCoords G data) (commonEval data r m)
    (fun i => ((punctured G.cols (i.val : K)).eval (i.val : K))⁻¹)
    (fun i => ((punctured G.rows (i.val : K)).eval (i.val : K))⁻¹)
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.cols (i.val : K)))
    (fun i => inv_ne_zero (punctured_eval_ne_zero G.rows (i.val : K)))
    (rightCoords_onto_kernel G data f tau hf ht)
    (leftCoords_in_kernel G data f tau hf ht hr)
    (rightCoords_common G data) (leftCoords_common G data) hE
  exact ⟨s, hs ▸ hdim, hdet⟩

end CatalanCore.Rect.CharZeroNV
