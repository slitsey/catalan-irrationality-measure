module

public import CatalanCore.Rect.CharZeroNV.Select
public import CatalanCore.Rect.CharZeroNV.Complement
public import CatalanCore.Rect.CharZeroNV.Family
public import CatalanCore.Rect.CharZeroNV.After
public import CatalanCore.Rect.CommonMinor.Low
public import CatalanCore.Rect.Full
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! # Characteristic-zero nonvanishing for an arbitrary frame with a rational increment

Generic adapter.  A frame `Fr` is given together with polynomials `D`, `A` over `ℚ`
such that `D(i) * (Delta (i+1) / norm) = A(i)` and the jet identity
`D'(i) * (Delta (i+1) / norm) - D(i) * (Dsq (i+1) / norm) = A'(i)` hold at every
natural `i`, `D` has degree at most 3, `A` degree at most 1, and `D` has an
isolated integer pole (in the sense of `IsolatedIntegerPole`).  Then, at every
rational input and every border ratio, one common-node deletion makes the hybrid
determinant nonzero, and `commonMinorFam Fr Adm 1` has `HasNVPinC` for any
`Adm` with `∀ r ≥ 1, ∃ m, Adm r m`.

Nothing here depends on the particular frame: the P6 instance
(`CatalanFrames.P6Hybrid.CharZeroNV`) is the case `D = 216 (X+1)(X+1/3)(X+1/2)`,
`A = 1 - X`, `norm = 36`.
-/

open Polynomial Finset Matrix CatalanCore CatalanCore.Rect CatalanCore.Rect.CharZeroNV

namespace CatalanCore.Rect.CharZeroNV.FrameAdapter

/-- Increment data of a frame: the cleared value and jet identities, degree bounds and
an isolated integer pole. -/
structure FrameIncrement (Fr : Frame) (D A : ℚ[X]) : Prop where
  pole : IsolatedIntegerPole D A
  deg_D : D.natDegree ≤ 3
  deg_A : A.natDegree ≤ 1
  value : ∀ i : ℕ, D.eval (i : ℚ) * (Fr.Delta (i + 1) / Fr.norm) = A.eval (i : ℚ)
  jet : ∀ i : ℕ, D.derivative.eval (i : ℚ) * (Fr.Delta (i + 1) / Fr.norm) -
    D.eval (i : ℚ) * (Fr.Dsq (i + 1) / Fr.norm) = A.derivative.eval (i : ℚ)

variable {Fr : Frame} {D A : ℚ[X]}

noncomputable def frameData (_h : FrameIncrement Fr D A) (U : ℚ) : IncrementData D A where
  f i := (∑ k ∈ Icc 1 i, Fr.Delta k) / Fr.norm
  tau i := U - (∑ k ∈ Icc 1 i, Fr.Dsq k) / Fr.norm
  value_step i := by
    have hv := _h.value i
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
    simp only [add_div, add_sub_cancel_left]
    exact hv
  jet_step i := by
    have hj := _h.jet i
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ i + 1)]
    simp only [add_div, add_sub_cancel_left, sub_sub_sub_cancel_left]
    linear_combination hj

lemma prefix_sub (g : ℕ → ℚ) {a b : ℕ} (hab : a ≤ b) :
    (∑ k ∈ Icc 1 b, g k) - (∑ k ∈ Icc 1 a, g k) = ∑ k ∈ Ioc a b, g k := by
  have hs : Icc 1 a ⊆ Icc 1 b := by intro k hk; simp only [mem_Icc] at *; omega
  have he : Icc 1 b \ Icc 1 a = Ioc a b := by
    ext k
    simp only [mem_sdiff, mem_Icc, mem_Ioc]
    omega
  have hsum := Finset.sum_sdiff hs (f := g)
  rw [he] at hsum
  linear_combination -hsum

/-- Extend a natural-node datum to the ambient field. -/
noncomputable def onNaturals (g : ℕ → ℚ) : ℚ → ℚ :=
  Function.extend (Nat.cast : ℕ → ℚ) g (fun _ => 0)

@[simp] lemma onNaturals_nat (g : ℕ → ℚ) (i : ℕ) : onNaturals g (i : ℚ) = g i :=
  Nat.cast_injective.extend_apply g _ i

lemma mn_offdiag (h : FrameIncrement Fr D A) (U : ℚ) (a b : ℕ) (hab : a ≠ b) :
    Fr.Mn a b = ((frameData h U).f a - (frameData h U).f b) / ((a : ℚ) - b) := by
  unfold CatalanCore.Frame.Mn
  rw [if_neg hab]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · rw [Nat.max_eq_right (by omega), Nat.min_eq_left (by omega)]
    have hs := prefix_sub Fr.Delta (Nat.le_of_lt hlt)
    dsimp [frameData]
    rw [← hs]
    rw [show (a : ℚ) - b = -((b : ℚ) - a) by ring, div_neg]
    simp only [div_eq_mul_inv]
    ring
  · rw [Nat.max_eq_left (by omega), Nat.min_eq_right (by omega)]
    have hs := prefix_sub Fr.Delta (Nat.le_of_lt hgt)
    dsimp [frameData]
    rw [← hs]
    ring

lemma loewnerEntry_nat (h : FrameIncrement Fr D A) (U : ℚ) (a b : ℕ) :
    loewnerEntry (onNaturals (frameData h U).f) (onNaturals (frameData h U).tau)
      (a : ℚ) (b : ℚ) = (if a = b then U else 0) + Fr.Mn a b := by
  by_cases hab : a = b
  · subst b
    simp [loewnerEntry, frameData, CatalanCore.Frame.Mn]
    ring
  · have hcast : (a : ℚ) ≠ b := by exact_mod_cast hab
    simp only [loewnerEntry, if_neg hcast, onNaturals_nat, if_neg hab, zero_add]
    exact (mn_offdiag h U a b hab).symm

/-- The abstract matrix is precisely the frozen hybrid matrix after reindexing. -/
theorem fullN_eq_loewner (h : FrameIncrement Fr D A) (U : ℚ) (r m : ℕ) :
    CatalanCore.Rect.FullN Fr (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (loewnerMatrix (after r m) (onNaturals (frameData h U).f)
        (onNaturals (frameData h U).tau)).submatrix (afterRowEquiv r m) (afterRowEquiv r m) := by
  ext i j
  simp only [Matrix.submatrix_apply, loewnerMatrix, after_equiv_row,
    afterRowEquiv_val, afterColEquiv_val]
  rw [loewnerEntry_nat]
  rcases i with i | i <;> rcases j with j | j
  · simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkA,
      afterNodeNat, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> ring
  · have h : i.val ≠ r + 2 * j.val + 1 := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkB,
      afterNodeNat, h]
  · have h : r + 2 * i.val ≠ j.val := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkC,
      afterNodeNat, h]
  · have h : r + 2 * i.val ≠ r + 2 * j.val + 1 := by omega
    simp [CatalanCore.Rect.FullN, CatalanCore.Rect.Blk, CatalanCore.Rect.blkD,
      afterNodeNat, h]

lemma fullN_restrict (Fr : Frame) (U : ℚ) (r m : ℕ) (s : Finset (Fin r)) :
    FullN Fr (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (FullN Fr (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).submatrix
          (Sum.map Subtype.val id) (Sum.map Subtype.val id) := by
  exact (FullN_submatrix_common Fr Subtype.val Subtype.val_injective
    (fun i : Fin r => i.val) (fun i : Fin m => r + 2 * i.val)
    (fun i : Fin m => r + 2 * i.val + 1) U).symm

theorem exists_common_deletion_fullN (h : FrameIncrement Fr D A) (U : ℚ) (r m : ℕ)
    (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), s.card ≤ 1 ∧
      (FullN Fr (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 := by
  classical
  obtain ⟨s, hs, hd⟩ := exists_common_deletion (after (K := ℚ) r m) (frameData h U)
    h.pole h.deg_D h.deg_A hr
    (onNaturals (frameData h U).f) (onNaturals (frameData h U).tau)
    (onNaturals_nat _) (onNaturals_nat _)
  refine ⟨s, hs, ?_⟩
  have hc : (after (K := ℚ) r m).common = fun i => afterRowEquiv r m (Sum.inl i) := by
    funext i
    exact (afterRowEquiv_common r m i).symm
  rw [hc, det_common_complement] at hd
  rw [fullN_restrict, fullN_eq_loewner h]
  simpa only [Matrix.submatrix_submatrix, Function.comp_def] using hd

theorem exists_commonMinor (h : FrameIncrement Fr D A) (U : ℚ) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), r - s.card ≤ 1 ∧
      (commonMinorPoly Fr r m s).eval U ≠ 0 := by
  classical
  obtain ⟨s, hs, hd⟩ := exists_common_deletion_fullN h U r m hr
  apply exists_commonMinor_of_fullN Fr r m 1
    (fun i : {i // i ∉ s} => i.val) Subtype.val_injective ?_ U hd
  have hc : Fintype.card {i : Fin r // i ∉ s} = r - s.card := by
    simpa using Fintype.card_subtype_compl (fun i : Fin r => i ∈ s)
  rw [hc]
  omega

theorem commonMinor_hasNVPinC (h : FrameIncrement Fr D A) (Adm : ℕ → ℕ → Prop)
    (hAdm : ∀ r, 1 ≤ r → ∃ m, Adm r m)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    CatalanCore.HasNVPinC (commonMinorFam Fr Adm 1) Cls Bad α β := by
  apply CatalanCore.Rect.CharZeroNV.commonMinor_hasNVPinC Fr Adm 1 hAdm
  intro r hr m U
  exact exists_commonMinor h U r m hr

#print axioms exists_common_deletion_fullN
#print axioms exists_commonMinor
#print axioms commonMinor_hasNVPinC

end CatalanCore.Rect.CharZeroNV.FrameAdapter
