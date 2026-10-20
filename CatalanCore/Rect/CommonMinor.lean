module

public import CatalanCore.Rect.PairFam

@[expose] public section

/-!
# A hybrid family with bounded common-node deletions

The degree budget is the original `r`, even when a member omits common nodes.
This is an upper bound on polynomial degree, as required by the content interface.
-/

open Finset Polynomial Matrix

namespace CatalanCore.Rect

/-- A rectangular hybrid with only the indicated common nodes retained. -/
noncomputable def commonMinorPoly (Fr : Frame) (r m : ℕ) (s : Finset (Fin r)) : ℚ[X] :=
  (FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det

theorem aeval_commonMinorPoly (Fr : Frame) (r m : ℕ) (s : Finset (Fin r)) (x : ℝ) :
    Polynomial.aeval x (commonMinorPoly Fr r m s) =
      (FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det := by
  unfold commonMinorPoly
  have h2 : (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)
      (FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det =
      ((FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).map
        (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)).det :=
    map_det' (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom _
  rw [h2, map_fullN]

theorem natDegree_commonMinorPoly_le (Fr : Frame) (r m : ℕ) (s : Finset (Fin r)) :
    (commonMinorPoly Fr r m s).natDegree ≤ r := by
  have h := natDegree_fullN_le Fr (fun a : s => (a.1 : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
  have hs : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hp : (commonMinorPoly Fr r m s).natDegree ≤ s.card := by
    simpa [commonMinorPoly] using h
  exact hp.trans hs

/-- Indices carry the original size, border size, and retained common nodes. -/
abbrev CommonMinorIndex := (r : ℕ) × (ℕ × Finset (Fin r))

/-- A single generic family; `d` bounds how many common nodes may be omitted. -/
noncomputable def commonMinorFam (Fr : Frame) (A : ℕ → ℕ → Prop) (d : ℕ) : PolyFamily where
  const := Fr.const
  ι := CommonMinorIndex
  deg := fun i => i.1
  Adm := fun i => A i.1 i.2.1 ∧ i.1 - i.2.2.card ≤ d
  Q := fun i => commonMinorPoly Fr i.1 i.2.1 i.2.2

theorem commonMinorFam_degree (Fr : Frame) (A : ℕ → ℕ → Prop) (d : ℕ)
    (i : (commonMinorFam Fr A d).ι) :
    ((commonMinorFam Fr A d).Q i).natDegree ≤ (commonMinorFam Fr A d).deg i :=
  natDegree_commonMinorPoly_le Fr i.1 i.2.1 i.2.2

end CatalanCore.Rect
