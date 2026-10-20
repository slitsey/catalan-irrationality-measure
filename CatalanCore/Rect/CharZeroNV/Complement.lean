module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Tactic

@[expose] public section

/-! # Reindex a selected principal complement by retained common and border nodes -/

open Finset Matrix

namespace CatalanCore.Rect.CharZeroNV

variable {I J L : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L]

noncomputable def commonComplementEquiv (e : (I ⊕ J) ≃ L) (s : Finset I) :
    ({i // i ∉ s} ⊕ J) ≃ {a // a ∉ s.image (fun i => e (.inl i))} := by
  classical
  let keep : ({i // i ∉ s} ⊕ J) → L := fun k => e (Sum.map Subtype.val id k)
  have hkeep : ∀ k, keep k ∉ s.image (fun i => e (.inl i)) := by
    intro k hk
    obtain ⟨i, hi, he⟩ := mem_image.mp hk
    have hh := e.injective he
    cases k with
    | inl j => exact j.property ((Sum.inl.inj hh) ▸ hi)
    | inr j => cases hh
  refine Equiv.ofBijective (fun k => ⟨keep k, hkeep k⟩) ⟨?_, ?_⟩
  · intro a b hab
    have hh := e.injective (congrArg Subtype.val hab)
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hh))
      | inr b => cases hh
    | inr a =>
      cases b with
      | inl b => cases hh
      | inr b => exact congrArg Sum.inr (Sum.inr.inj hh)
  · intro a
    obtain ⟨k, hk⟩ := e.surjective a.val
    cases k with
    | inl i =>
      have hi : i ∉ s := by
        intro hi
        exact a.property (mem_image.mpr ⟨i, hi, hk⟩)
      exact ⟨.inl ⟨i, hi⟩, Subtype.ext hk⟩
    | inr j => exact ⟨.inr j, Subtype.ext hk⟩

@[simp] lemma commonComplementEquiv_val (e : (I ⊕ J) ≃ L) (s : Finset I)
    (k : {i // i ∉ s} ⊕ J) :
    (commonComplementEquiv e s k).val = e (Sum.map Subtype.val id k) := rfl

theorem det_common_complement {R : Type*} [CommRing R]
    (M : Matrix L L R) (e : (I ⊕ J) ≃ L) (s : Finset I) :
    (M.submatrix (Subtype.val : {a // a ∉ s.image (fun i => e (.inl i))} → L) Subtype.val).det =
      (M.submatrix (fun k : {i // i ∉ s} ⊕ J => e (Sum.map Subtype.val id k))
        (fun k : {i // i ∉ s} ⊕ J => e (Sum.map Subtype.val id k))).det := by
  have he := Matrix.det_submatrix_equiv_self (commonComplementEquiv e s)
    (M.submatrix (Subtype.val : {a // a ∉ s.image (fun i => e (.inl i))} → L) Subtype.val)
  simpa only [Matrix.submatrix_submatrix, Function.comp_def, commonComplementEquiv_val] using he.symm

end CatalanCore.Rect.CharZeroNV
