module

public import CatalanFrames.P6Hybrid.CharZeroNV

@[expose] public section

/-! # The frozen P6 selector over any characteristic-zero field -/

open Polynomial Finset Matrix CatalanCore.Rect CatalanCore.Rect.CharZeroNV CatalanFrames.P6

namespace CatalanFrames.P6Hybrid.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K] [DecidableEq K]

lemma incrementDen_eval_map (i : ℕ) :
    (incrementDen : K[X]).eval (i : K) =
      algebraMap ℚ K ((incrementDen : ℚ[X]).eval (i : ℚ)) := by
  simp [incrementDen]

lemma incrementDen_jet_map (i : ℕ) :
    (incrementDen : K[X]).derivative.eval (i : K) =
      algebraMap ℚ K ((incrementDen : ℚ[X]).derivative.eval (i : ℚ)) := by
  simp [incrementDen, derivative_mul, derivative_add]

noncomputable def fieldData (U : K) : IncrementData (incrementDen : K[X]) (1 - X) where
  f i := algebraMap ℚ K ((frameData 0).f i)
  tau i := U + algebraMap ℚ K ((frameData 0).tau i)
  value_step i := by
    rw [incrementDen_eval_map, ← map_sub, ← map_mul, (frameData 0).value_step]
    simp
  jet_step i := by
    rw [incrementDen_eval_map, incrementDen_jet_map, add_sub_add_left_eq_sub,
      ← map_sub, ← map_sub, ← map_mul, ← map_mul, ← map_add, (frameData 0).jet_step]
    simp

noncomputable def onNaturalsK (g : ℕ → K) : K → K :=
  Function.extend (Nat.cast : ℕ → K) g (fun _ => 0)

@[simp] lemma onNaturalsK_nat (g : ℕ → K) (i : ℕ) :
    onNaturalsK g (i : K) = g i :=
  Nat.cast_injective.extend_apply g _ i

lemma loewnerEntry_field_nat (U : K) (a b : ℕ) :
    loewnerEntry (onNaturalsK (fieldData U).f) (onNaturalsK (fieldData U).tau)
      (a : K) (b : K) = (if a = b then U else 0) + algebraMap ℚ K (p6Frame.Mn a b) := by
  by_cases hab : a = b
  · subst b
    simp [loewnerEntry, fieldData, frameData, CatalanCore.Frame.Mn, p6Frame]
    ring
  · have hcast : (a : K) ≠ b := by exact_mod_cast hab
    simp only [loewnerEntry, ite_eq_right hcast, onNaturalsK_nat,
      ite_eq_right hab, zero_add, fieldData]
    rw [mn_offdiag 0 a b hab]
    simp

theorem fullN_eq_loewner_field (U : K) (r m : ℕ) :
    FullN p6Frame (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (loewnerMatrix (after r m) (onNaturalsK (fieldData U).f)
        (onNaturalsK (fieldData U).tau)).submatrix (afterRowEquiv r m) (afterRowEquiv r m) := by
  classical
  ext i j
  simp only [Matrix.submatrix_apply, loewnerMatrix, after_equiv_row,
    afterRowEquiv_val, afterColEquiv_val]
  rw [loewnerEntry_field_nat]
  rcases i with i | i <;> rcases j with j | j
  · simp [FullN, Blk, blkA, afterNodeNat, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> ring
  · have h : i.val ≠ r + 2 * j.val + 1 := by omega
    simp [FullN, Blk, blkB, afterNodeNat, h]
  · have h : r + 2 * i.val ≠ j.val := by omega
    simp [FullN, Blk, blkC, afterNodeNat, h]
  · have h : r + 2 * i.val ≠ r + 2 * j.val + 1 := by omega
    simp [FullN, Blk, blkD, afterNodeNat, h]

/-- The actual frozen hybrid matrix over any characteristic-zero field is
nonsingular after deleting at most one common node. -/
theorem exists_common_deletion_field (U : K) (r m : ℕ) (hr : 1 ≤ r) :
    ∃ s : Finset (Fin r), s.card ≤ 1 ∧
      (FullN p6Frame (fun i : {i // i ∉ s} => i.val.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).det ≠ 0 := by
  classical
  obtain ⟨s, hs, hd⟩ := exists_common_deletion (after (K := K) r m) (fieldData U)
    isolatedPole den_degree (by compute_degree) hr
    (onNaturalsK (fieldData U).f) (onNaturalsK (fieldData U).tau)
    (onNaturalsK_nat _) (onNaturalsK_nat _)
  refine ⟨s, hs, ?_⟩
  have hc : (after (K := K) r m).common = fun i => afterRowEquiv r m (Sum.inl i) := by
    funext i
    exact (afterRowEquiv_common r m i).symm
  rw [hc, det_common_complement] at hd
  have he : FullN p6Frame (fun i : {i // i ∉ s} => i.val.val)
      (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U =
      (FullN p6Frame (fun i : Fin r => i.val)
        (fun i : Fin m => r + 2 * i.val) (fun i : Fin m => r + 2 * i.val + 1) U).submatrix
          (Sum.map Subtype.val id) (Sum.map Subtype.val id) :=
    (FullN_submatrix_common p6Frame Subtype.val Subtype.val_injective
      (fun i : Fin r => i.val) (fun i : Fin m => r + 2 * i.val)
      (fun i : Fin m => r + 2 * i.val + 1) U).symm
  rw [he, fullN_eq_loewner_field]
  simpa only [Matrix.submatrix_submatrix, Function.comp_def] using hd

#print axioms exists_common_deletion_field

end CatalanFrames.P6Hybrid.CharZeroNV
