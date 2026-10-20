module
public import CatalanCore.Rect.CommonMinor
@[expose] public section
open Polynomial Matrix Finset
namespace CatalanCore.Rect

theorem eval_commonMinorPoly (Fr : Frame) (r m : ℕ) (s : Finset (Fin r)) (x : ℚ) :
    (commonMinorPoly Fr r m s).eval x =
      (FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det := by
  have h := (Polynomial.evalRingHom x).map_det
    (FullN Fr (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X]))
  rw [fullN_map_eval] at h
  exact h
theorem FullN_submatrix_common (Fr : Frame) {R : Type*} [CommRing R] [Algebra ℚ R]
    {I J B : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype B] [DecidableEq B] (f : J → I) (hf : Function.Injective f)
    (c : I → ℕ) (xs ys : B → ℕ) (x : R) :
    (FullN Fr c xs ys x).submatrix (Sum.map f id) (Sum.map f id) =
      FullN Fr (c ∘ f) xs ys x := by
  ext (a | i) (b | j) <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.submatrix, Matrix.one_apply, hf.eq_iff]

/-- Any injective retained common-node family is a member of the minor family. -/
theorem exists_commonMinor_of_fullN (Fr : Frame) (r m d : ℕ)
    {I : Type} [Fintype I] [DecidableEq I] (c : I → Fin r)
    (hc : Function.Injective c) (hcard : r - Fintype.card I ≤ d) (x : ℚ)
    (hdet : (FullN Fr (fun i => (c i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det ≠ 0) :
    ∃ s : Finset (Fin r), r - s.card ≤ d ∧ (commonMinorPoly Fr r m s).eval x ≠ 0 := by
  let s : Finset (Fin r) := univ.image c
  let e : I ≃ s := Equiv.ofBijective (fun i => ⟨c i, mem_image.mpr ⟨i, mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hc (congrArg Subtype.val h), by
      rintro ⟨a, ha⟩
      obtain ⟨i, _, hi⟩ := mem_image.mp ha
      exact ⟨i, Subtype.ext hi⟩⟩
  have hs : s.card = Fintype.card I := by
    exact (Finset.card_image_of_injective univ hc).trans (Finset.card_univ)
  refine ⟨s, by rwa [hs], ?_⟩
  rw [eval_commonMinorPoly]
  have he := det_fullN_reindex Fr (fun i : I => (c i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
    (fun a : s => (a.1 : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) e.symm (Equiv.refl _)
    (fun a => by have h := congrArg (fun t : s => (t.val : ℕ)) (e.apply_symm_apply a); exact h)
    (fun _ => rfl) (fun _ => rfl) x
  rwa [he]
end CatalanCore.Rect
