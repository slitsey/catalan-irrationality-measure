module
public import CatalanCore.Uniform.Frame.NVEntry
@[expose] public section

namespace CatalanCore.Uniform.NVAdapter
open Finset Matrix Polynomial

private theorem restrict_fullN (Fr : Frame) (U : ℚ) (G : Rect.Geometry) (D : Finset G.C) :
    (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).submatrix
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id) =
    Rect.FullN Fr (fun a : {i : G.C // i ∉ D} => ((a.val : G.C) : ℕ)) G.xs G.ys U := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst b
      simp [Rect.FullN,Rect.Blk,Rect.blkA]
    · have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [Rect.FullN,Rect.Blk,Rect.blkA,Matrix.one_apply,hab,hne]
  · rfl
  · rfl
  · rfl
private noncomputable def retainedEquiv {I : Type} [Fintype I] [DecidableEq I]
    (D : Finset I) : {i // i ∉ D} ≃ ((univ : Finset I) \ D : Finset I) where
  toFun a := ⟨a.val,by simp [a.property]⟩
  invFun a := ⟨a.val,(Finset.mem_sdiff.mp a.property).2⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

private theorem det_fullN_reindex (Fr : Frame)
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (e : I ≃ J) (common : J → ℕ)
    (rows cols : K → ℕ) (U : ℚ) :
    (Rect.FullN Fr (common ∘ e) rows cols U).det =
      (Rect.FullN Fr common rows cols U).det := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl K))]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Rect.FullN,Rect.Blk,Rect.blkA,Rect.blkB,Rect.blkC,Rect.blkD,
      Matrix.fromBlocks,Matrix.one_apply,Function.comp_def]

/-- Transport the N theorem's actual same-index complement to the exact
retained-common-node polynomial family. No principal-minor inference is made
from corank alone: the premise is the nonzero complement proved by N. -/
theorem retained_of_model_deletion (Fr : Frame) (U : ℚ) (G : Rect.Geometry)
    (s : Finset ((model G).rows ∩ (model G).cols : Finset ℚ))
    (hnonzero : (((model G).matrix (NV.onNaturals (NV.framePrefix Fr))
        (NV.onNaturals (NV.frameJet Fr U))).submatrix
      (Subtype.val : {i // i ∉ s.image (model G).common} → (model G).rows)
      Subtype.val).det ≠ 0) :
    ∃ S : Finset G.C, G.C.card - S.card = s.card ∧
      (Rect.FullN Fr (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  classical
  let D : Finset G.C := s.image (commonField G).symm
  let S : Finset G.C := univ \ D
  have hDcard : D.card = s.card := Finset.card_image_of_injective _ (commonField G).symm.injective
  have hdel : s.image (model G).common = D.image (fun a => rowField G (.inl a)) := by
    dsimp [D]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a ha
    simpa only [Equiv.apply_symm_apply,Function.comp_def] using common_compat G ((commonField G).symm a)
  rw [hdel] at hnonzero
  have hc := Rect.CharZeroNV.det_common_complement
    ((model G).matrix (NV.onNaturals (NV.framePrefix Fr))
      (NV.onNaturals (NV.frameJet Fr U))) (rowField G) D
  rw [hc] at hnonzero
  have hm := (fullN_eq_model Fr U G).symm
  have hr := congrArg (fun M : Matrix (Index G) (Index G) ℚ =>
    M.submatrix (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)) hm
  rw [Matrix.submatrix_submatrix, restrict_fullN] at hr
  have hkeep : (Rect.FullN Fr (fun a : {i : G.C // i ∉ D} => ((a.1 : G.C) : ℕ))
      G.xs G.ys U).det ≠ 0 := by
    rw [← hr]
    exact hnonzero
  let e := retainedEquiv D
  change (Rect.FullN Fr ((fun a : S => ((a.1 : G.C) : ℕ)) ∘ e) G.xs G.ys U).det ≠ 0 at hkeep
  rw [det_fullN_reindex] at hkeep
  refine ⟨S,?_,hkeep⟩
  have hle : D.card ≤ G.C.card := by simpa using Finset.card_le_univ D
  have hS : S.card = G.C.card - D.card := by
    simp only [S, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ,Fintype.card_coe]
  omega

private theorem corank_submatrix {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (M : Matrix I I ℚ) (e : J ≃ I) :
    Module.finrank ℚ (LinearMap.ker (M.submatrix e e).mulVecLin) =
      Module.finrank ℚ (LinearMap.ker M.mulVecLin) := by
  have hM := M.mulVecLin.finrank_range_add_finrank_ker
  have hN := (M.submatrix e e).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hM hN
  change M.rank + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = Fintype.card I at hM
  change (M.submatrix e e).rank + Module.finrank ℚ
    (LinearMap.ker (M.submatrix e e).mulVecLin) = Fintype.card J at hN
  have hr := Matrix.rank_submatrix M e e
  have hc := Fintype.card_congr e
  omega

/-- The field-node model and actual FullN have exactly the same corank. -/
theorem corank_model (Fr : Frame) (U : ℚ) (G : Rect.Geometry) :
    Module.finrank ℚ (LinearMap.ker ((model G).matrix
      (NV.onNaturals (NV.framePrefix Fr)) (NV.onNaturals (NV.frameJet Fr U))).mulVecLin) =
    Module.finrank ℚ (LinearMap.ker
      (Rect.FullN Fr (fun a : G.C => (a : ℕ)) G.xs G.ys U).mulVecLin) := by
  rw [fullN_eq_model]
  exact (corank_submatrix _ (rowField G)).symm

end CatalanCore.Uniform.NVAdapter




