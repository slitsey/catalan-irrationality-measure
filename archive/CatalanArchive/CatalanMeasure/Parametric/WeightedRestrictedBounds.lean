module
public import CatalanMeasure.Parametric.CommonFactorCoordinate
public import CatalanArchive.CatalanMeasure.ResidualFixed0Certificate
public import CatalanArchive.CatalanMeasure.ResidualFixed1Certificate
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

theorem proposed_commonFactor_pow (N : ℕ) :
    rowCommonFactor proposed N=(rowCommonFactor proposed 1)^N := by
  unfold rowCommonFactor
  rw [proposed_A N,proposed_A 1]
  change (X^(36*N)*(1-X)^(5*N):ℝ[X])=(X^36*(1-X)^5)^N
  rw [mul_pow,pow_mul,pow_mul]

theorem proposed_commonFactor_log_scale (N : ℕ) (t : ℝ) :
    Real.log |(rowCommonFactor proposed N).eval t| =
      (N:ℝ)*Real.log |(rowCommonFactor proposed 1).eval t| := by
  rw [proposed_commonFactor_pow,eval_pow,abs_pow,Real.log_pow]

theorem weighted_restrictedWeight_le (N k : ℕ) (a : Fin (89*N)) {x W S : ℝ}
    (hx : x<0) (hcoord : realCoordinateInv x=CatalanMeasure.chebNode (89*N) a)
    (hfield : 96*W-Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)|≤S) :
    Real.exp (96*N*W)*|restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a| ≤
      260000*N*Real.exp ((150+S)*N) := by
  set c := |(rowCommonFactor proposed N).eval (CatalanMeasure.chebNode (89*N) a)| with hc
  have hcpos : 0<c := abs_pos.mpr (rowCommonFactor_eval_ne_zero proposed N
    (CatalanMeasure.chebNode_mem a).2)
  have hlog : Real.log c=(N:ℝ)*Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)| := by
    rw [hc,proposed_commonFactor_log_scale,← hcoord]
  have hr : Real.exp (96*N*W)/c =
      Real.exp ((96*W-Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)|)*N) := by
    rw [← Real.exp_log hcpos,← Real.exp_sub,hlog]
    congr 1
    ring
  have hratio : Real.exp (96*N*W)/c≤Real.exp (S*N) := by
    rw [hr]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hfield (Nat.cast_nonneg N)
  have hweight := proposed_restrictedWeight_joint_le N k a
  change c*|restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a|≤
    260000*N*(residualCircleK:ℝ)^N at hweight
  have hK0 : (0:ℝ)≤residualCircleK := by norm_num [residualCircleK]
  have hK : (residualCircleK:ℝ)^N≤Real.exp (150*N) := by
    calc _ ≤ Real.exp 150 ^N := pow_le_pow_left₀ hK0 residualCircleK_le_exp N
      _ = Real.exp (150*N) := by rw [← Real.exp_nat_mul];congr 1;ring
  calc
    _ = (Real.exp (96*N*W)/c)*
        (c*|restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a|) := by
          field_simp
    _ ≤ Real.exp (S*N)*(260000*N*(residualCircleK:ℝ)^N) :=
      mul_le_mul hratio hweight (by positivity) (Real.exp_pos _).le
    _ ≤ Real.exp (S*N)*(260000*N*Real.exp (150*N)) := by gcongr
    _ = 260000*N*Real.exp ((150+S)*N) := by
      have he : Real.exp (S*N)*Real.exp (150*N)=Real.exp ((150+S)*N) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (260000*(N:ℝ))*(Real.exp (S*N)*Real.exp (150*N)) := by ring
        _ = _ := by rw [he]

theorem weighted_restricted_one (N k : ℕ) (a : Fin (89*N)) {x : ℝ} (hx : x<0)
    (hcoord : realCoordinateInv x=CatalanMeasure.chebNode (89*N) a) :
    Real.exp (96*N*proposedFixedFieldOne (proposedCaseOneLambda:ℝ) x)*
      |restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a| ≤
      260000*N*Real.exp (158*N) := by
  have hf : 96*proposedFixedFieldOne (proposedCaseOneLambda:ℝ) x-
      Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)|≤8 := by
    convert proposedFixedFieldOne_after_common_le_eight hx using 1 <;> ring
  have hh := weighted_restrictedWeight_le N k a hx hcoord hf
  convert hh using 1 <;> norm_num

theorem weighted_restricted_two (N k : ℕ) (a : Fin (89*N)) {x : ℝ}
    (hx0 : -1≤x) (hx : x<0) (hcoord : realCoordinateInv x=CatalanMeasure.chebNode (89*N) a)
    {cs : List ℤ} {tail : List CatalanMeasure.Cert.TailQ}
    (hcap : ∀ y ∈ Set.Icc (-1:ℝ) 0,CatalanMeasure.Cert.residualTwoField cs tail y≤-(1/8:ℝ)) :
    Real.exp (96*N*proposedFixedFieldTwo (barrierTrialT (CatalanMeasure.Cert.trialSeq cs tail)) x)*
      |restrictedWeight proposed N k (CatalanMeasure.chebNode (89*N)) a| ≤
      260000*N*Real.exp (138*N) := by
  have hf : 96*proposedFixedFieldTwo (barrierTrialT (CatalanMeasure.Cert.trialSeq cs tail)) x-
      Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)|≤(-12:ℝ) := by
    calc
      _ = 96*(proposedFixedFieldTwo (barrierTrialT (CatalanMeasure.Cert.trialSeq cs tail)) x-
          Real.log |(rowCommonFactor proposed 1).eval (realCoordinateInv x)|/96) := by ring
      _ = 96*CatalanMeasure.Cert.residualTwoField cs tail x := by
        rw [proposedFixedFieldTwo_sub_common hx]
        rfl
      _ ≤ -12 := by have hh := hcap x ⟨hx0,hx.le⟩;linarith
  have hh := weighted_restrictedWeight_le N k a hx hcoord hf
  convert hh using 1 <;> norm_num

end
end CatalanMeasure.Parametric
