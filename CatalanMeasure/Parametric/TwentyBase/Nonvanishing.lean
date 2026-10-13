module
public import CatalanMeasure.Parametric.TwentyBase.Entries
public import CatalanMeasure.Parametric.TwentyBase.InverseZero
public import CatalanMeasure.Parametric.TwentyBase.InversePlus
public import CatalanMeasure.Parametric.TwentyBase.InverseMinus
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyBase
open OAI.InternalCatalan Matrix
noncomputable section

theorem baseResidueCase_literal (sigma : ℤ) :
    baseB0Residue twenty 1009+(sigma:ZMod 1009) • baseB1Residue twenty 1009 =
      literalCaseMatrix sigma :=by
  change (Matrix.of (fun r k : Fin 20 =>baseFilteredContraction twenty 1009 r.val k)) +
    (sigma:ZMod 1009) • (Matrix.of (fun r k : Fin 20 =>
      baseFilteredContraction twenty 1009 (r.val+1) k)) = _
  ext r k
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply,literalCaseMatrix]
  change baseFilteredContraction twenty 1009 r.castSucc.val k +
    (sigma:ZMod 1009)*baseFilteredContraction twenty 1009 r.succ.val k = _
  rw [actual_base_entries r.castSucc k,actual_base_entries r.succ k]

theorem literalCase_det_ne_zero {sigma : ℤ} {B : Matrix (Fin 20) (Fin 20) (ZMod 1009)}
    (h : literalCaseMatrix sigma*B=1) : (literalCaseMatrix sigma).det≠0 :=by
  have hh :=congrArg Matrix.det h
  rw [Matrix.det_mul,Matrix.det_one] at hh
  exact left_ne_zero_of_mul_eq_one hh

theorem twenty_base_residue_dets :
    (baseB0Residue twenty 1009).det≠0 ∧
      (baseB0Residue twenty 1009+baseB1Residue twenty 1009).det≠0 ∧
      (baseB0Residue twenty 1009-baseB1Residue twenty 1009).det≠0 :=by
  have h0 :=baseResidueCase_literal 0
  have hp :=baseResidueCase_literal 1
  have hm :=baseResidueCase_literal (-1)
  simp only [Int.cast_zero,zero_smul,add_zero] at h0
  simp only [Int.cast_one,one_smul] at hp
  simp only [Int.cast_neg,Int.cast_one,neg_one_smul,← sub_eq_add_neg] at hm
  constructor
  · change (baseB0Residue twenty 1009 : Matrix (Fin 20) (Fin 20) (ZMod 1009)).det≠0
    rw [h0]
    exact literalCase_det_ne_zero inverseZero_checked
  constructor
  · change (baseB0Residue twenty 1009+baseB1Residue twenty 1009 :
      Matrix (Fin 20) (Fin 20) (ZMod 1009)).det≠0
    rw [hp]
    exact literalCase_det_ne_zero inversePlus_checked
  · change (baseB0Residue twenty 1009-baseB1Residue twenty 1009 :
      Matrix (Fin 20) (Fin 20) (ZMod 1009)).det≠0
    rw [hm]
    exact literalCase_det_ne_zero inverseMinus_checked

theorem twenty_baseMatrixRat_det_ne_zero (sigma : ℤ)
    (h : (baseB0Residue twenty 1009+(sigma:ZMod 1009) • baseB1Residue twenty 1009).det≠0) :
    (baseMatrixRat twenty sigma).det≠0 :=by
  have hh :=baseMatrix_det_residue (P := twenty) (p := 1009) (by decide)
    (by norm_num [twenty_H]) sigma
  intro hz
  rw [hz] at hh
  apply h
  rw [← hh]
  simp [palindromicRatResidue]

theorem twenty_base_rational_dets :
    (baseMatrixRat twenty 0).det≠0 ∧ (baseMatrixRat twenty 1).det≠0 ∧
      (baseMatrixRat twenty (-1)).det≠0 :=by
  have hs :=twenty_base_residue_dets
  refine ⟨twenty_baseMatrixRat_det_ne_zero 0 ?_,twenty_baseMatrixRat_det_ne_zero 1 ?_,
    twenty_baseMatrixRat_det_ne_zero (-1) ?_⟩
  · simpa using hs.1
  · simpa using hs.2.1
  · simpa [sub_eq_add_neg] using hs.2.2

theorem twenty_prime_nonvanishing {p : ℕ} [Fact p.Prime]
    (hp : finitePrimeCutoff twenty<p) (z : ℚ) (hz : (((p:ℚ)*z).den:ZMod p)≠0) :
    determinantRat twenty z p≠0 :=
  determinantRat_prime_ne_zero twenty twenty_admissible hp twenty_base_rational_dets.1
    twenty_base_rational_dets.2.1 twenty_base_rational_dets.2.2 z hz

end
end CatalanMeasure.Parametric.TwentyBase
