module

public import CatalanFrames.P6Hybrid.CharZeroInstance
public import CatalanCore.Rect.CharZeroNV.Select
public import CatalanCore.Rect.CharZeroNV.Complement
public import CatalanCore.Rect.CharZeroNV.Family
public import CatalanCore.Rect.CommonMinor.Low

@[expose] public section

/-! # Universal rational-input nonvanishing by one common-node deletion

This thin instance connects the shared characteristic-zero interpolation
selector to the existing frozen P6 common-minor family, at every border ratio.
-/

open Polynomial Finset Matrix CatalanCore.Rect CatalanCore.Rect.CharZeroNV CatalanFrames.P6

namespace CatalanFrames.P6Hybrid.CharZeroNV

lemma fullN_restrict (U : ℚ) (r m : ℕ) (s : Finset (Fin r)) :
    FullN p6Frame (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (FullN p6Frame (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).submatrix
          (Sum.map Subtype.val id) (Sum.map Subtype.val id) :=
  FrameAdapter.fullN_restrict p6Frame U r m s

theorem exists_common_deletion_fullN (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), s.card ≤ 1 ∧
      (FullN p6Frame (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 :=
  CharZeroInstance.exists_common_deletion_fullN U r m hr

/-- At every rational input and every border ratio, some member obtained by
deleting at most one common node is nonzero. -/
theorem exists_commonMinor (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), r - s.card ≤ 1 ∧
      (commonMinorPoly p6Frame r m s).eval U ≠ 0 :=
  CharZeroInstance.exists_commonMinor U r m hr

/-- The existing pinned measure interface now allows every unbounded choice
of border ratio, with only one common-node deletion. -/
theorem commonMinor_hasNVPinC (Adm : ℕ → ℕ → Prop)
    (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam p6Frame Adm 1) Cls Bad α β :=
  CharZeroInstance.commonMinor_hasNVPinC Adm hAdm Cls Bad α β

#print axioms exists_common_deletion_fullN
#print axioms exists_commonMinor
#print axioms commonMinor_hasNVPinC

end CatalanFrames.P6Hybrid.CharZeroNV
