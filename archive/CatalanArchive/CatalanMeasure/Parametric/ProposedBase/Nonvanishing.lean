module
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.CaseChecks
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.EntryBridge
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.EntriesChecks
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.InverseZero
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.InversePlus
public import CatalanArchive.CatalanMeasure.Parametric.ProposedBase.InverseMinus
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open OAI.InternalCatalan Matrix
set_option maxRecDepth 6000
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem baseFilteredContraction_literal (r : Fin 97) (k : Fin 96) :
    baseFilteredContraction proposed 1009 r.val k=(literalEntry r k:ZMod 1009) := by
  have hh := congrArg (fun z:ℤ =>(z:ZMod 1009)) (contractionInt_checked r k)
  have hc : ((contractionInt r k%1009:ℤ):ZMod 1009)=(contractionInt r k:ZMod 1009) := by
    simpa only [Nat.cast_ofNat] using ZMod.intCast_mod (contractionInt r k) 1009
  rw [hc] at hh
  exact (baseFilteredContraction_int r k).trans hh

theorem baseResidueCase_literal (sigma : ℤ) :
    baseB0Residue proposed 1009+(sigma:ZMod 1009) • baseB1Residue proposed 1009 =
      Matrix.of (fun r k =>(literalCaseInt sigma r k:ZMod 1009)) := by
  change (Matrix.of (fun r k : Fin 96 =>baseFilteredContraction proposed 1009 r.val k)) +
    (sigma:ZMod 1009) • (Matrix.of (fun r k : Fin 96 =>
      baseFilteredContraction proposed 1009 (r.val+1) k)) = _
  ext r k
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,literalCaseInt,
    Int.cast_add,Int.cast_mul]
  change baseFilteredContraction proposed 1009 r.castSucc.val k +
    (sigma:ZMod 1009)*baseFilteredContraction proposed 1009 r.succ.val k =
    ((literalEntry r.castSucc k:ZMod 1009)+(sigma:ZMod 1009)*(literalEntry r.succ k:ZMod 1009))
  rw [baseFilteredContraction_literal r.castSucc k,baseFilteredContraction_literal r.succ k]

theorem modulusCast_literal {A B : Matrix (Fin 96) (Fin 96) ℤ}
    (h : ∀ r k,A r k%1009=B r k) :
    Matrix.of (fun r k =>(A r k:ZMod 1009))=Matrix.of (fun r k =>(B r k:ZMod 1009)) := by
  ext r k
  have hh := congrArg (fun z:ℤ =>(z:ZMod 1009)) (h r k)
  have hc : ((A r k%1009:ℤ):ZMod 1009)=(A r k:ZMod 1009) := by
    simpa only [Nat.cast_ofNat] using ZMod.intCast_mod (A r k) 1009
  rw [hc] at hh
  exact hh

theorem proposed_base_residue_dets :
    (baseB0Residue proposed 1009).det≠0 ∧
      (baseB0Residue proposed 1009+baseB1Residue proposed 1009).det≠0 ∧
      (baseB0Residue proposed 1009-baseB1Residue proposed 1009).det≠0 := by
  have h0 := baseResidueCase_literal 0
  have hp := baseResidueCase_literal 1
  have hm := baseResidueCase_literal (-1)
  rw [modulusCast_literal literalCase_zero_checked] at h0
  rw [modulusCast_literal literalCase_plus_checked] at hp
  rw [modulusCast_literal literalCase_minus_checked] at hm
  have h0' : baseB0Residue proposed 1009=baseZeroMod := by
    ext r k
    have hh := congrArg (fun A : Matrix (Fin proposed.n0) (Fin proposed.n0) (ZMod 1009) =>A r k) h0
    simpa only [Int.cast_zero,zero_smul,add_zero,Matrix.of_apply,baseZeroMod] using hh
  have hp' : baseB0Residue proposed 1009+baseB1Residue proposed 1009=basePlusMod := by
    ext r k
    have hh := congrArg (fun A : Matrix (Fin proposed.n0) (Fin proposed.n0) (ZMod 1009) =>A r k) hp
    simpa only [Int.cast_one,one_smul,Matrix.of_apply,basePlusMod] using hh
  have hm' : baseB0Residue proposed 1009-baseB1Residue proposed 1009=baseMinusMod := by
    ext r k
    have hh := congrArg (fun A : Matrix (Fin proposed.n0) (Fin proposed.n0) (ZMod 1009) =>A r k) hm
    simpa only [Int.cast_neg,Int.cast_one,neg_one_smul,Matrix.of_apply,baseMinusMod,sub_eq_add_neg] using hh
  constructor
  · rw [h0'];exact baseZero_det_ne_zero
  constructor
  · rw [hp'];exact basePlus_det_ne_zero
  · rw [hm'];exact baseMinus_det_ne_zero

theorem baseMatrixRat_det_ne_zero_of_1009 (sigma : ℤ)
    (h : (baseB0Residue proposed 1009+(sigma:ZMod 1009) • baseB1Residue proposed 1009).det≠0) :
    (baseMatrixRat proposed sigma).det≠0 := by
  have hh := baseMatrix_det_residue (P := proposed) (p := 1009) (by decide)
    (by norm_num [proposed_H]) sigma
  intro hz
  rw [hz] at hh
  apply h
  rw [← hh]
  simp [palindromicRatResidue]

theorem proposed_base_rational_dets :
    (baseMatrixRat proposed 0).det≠0 ∧ (baseMatrixRat proposed 1).det≠0 ∧
      (baseMatrixRat proposed (-1)).det≠0 := by
  have hs := proposed_base_residue_dets
  refine ⟨baseMatrixRat_det_ne_zero_of_1009 0 ?_,baseMatrixRat_det_ne_zero_of_1009 1 ?_,
    baseMatrixRat_det_ne_zero_of_1009 (-1) ?_⟩
  · simpa using hs.1
  · simpa using hs.2.1
  · simpa [sub_eq_add_neg] using hs.2.2

theorem proposed_prime_nonvanishing {p : ℕ} [Fact p.Prime]
    (hp : finitePrimeCutoff proposed<p) (z : ℚ) (hz : (((p:ℚ)*z).den:ZMod p)≠0) :
    determinantRat proposed z p≠0 :=
  determinantRat_prime_ne_zero proposed proposed_admissible hp proposed_base_rational_dets.1
    proposed_base_rational_dets.2.1 proposed_base_rational_dets.2.2 z hz

end
end CatalanMeasure.Parametric.ProposedBase
