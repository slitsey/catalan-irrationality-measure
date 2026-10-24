module
public import CatalanMeasure.Parametric.PopulationPhysicalValue
public import CatalanMeasure.Parametric.TwentyParameters
public import CatalanMeasure.Cert.ShiftedFields
@[expose] public section
namespace OAI.InternalCatalan
noncomputable section

theorem population_trialT_mul (c : ℝ) (u : ℕ → ℝ) (x : ℝ) :
    barrierTrialT (fun j =>c*u j) x=c*barrierTrialT u x :=by
  unfold barrierTrialT
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

theorem population_trialNormSq_mul (c : ℝ) (u : ℕ → ℝ) :
    barrierTrialNormSq (fun j =>c*u j)=c^2*barrierTrialNormSq u :=by
  unfold barrierTrialNormSq
  rw [← tsum_mul_left]
  congr 1
  funext j
  ring

end
end OAI.InternalCatalan
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan CatalanMeasure.Cert
noncomputable section

def twentyRowWeights (kappa lambda : ℚ) : RowWeights :=
  ⟨2/5,1/10,7/20+kappa/2,lambda,1/5⟩

def twentyColumnWeights (a : ℚ) : ColumnWeights :=⟨3/20,1/20,a⟩

theorem twenty_populationRowField {N : ℕ} (hN : 0<N) (k x : ℝ) :
    paramPopulationRowField twenty N k x=
      (2/5:ℝ)*Real.log |x|+(1/10:ℝ)*Real.log (1-x)-
      (7/20+k/2)*Real.log (1+x^2) :=by
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  unfold paramPopulationRowField
  rw [twenty_A,twenty_H]
  change (8*N:ℕ)/(20*N:ℕ)*Real.log |x|+2*(1*N:ℕ)/(20*N:ℕ)*Real.log (1-x)-
    ((27*N:ℕ)/(20*N:ℕ)+(k-2)/2)*Real.log (1+x^2)=_
  push_cast
  field_simp
  ring

theorem twenty_caseField {N : ℕ} (hN : 0<N) (x : ℝ) :
    paramCaseField twenty N x=(1/5:ℝ)-2*x^2/(1+x^2) :=by
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  unfold paramCaseField
  change 2*(2*N:ℕ)/(20*N:ℕ)-2*x^2/(1+x^2)=_
  push_cast
  field_simp
  ring

/-- The rational certificate field is the actual normalized row field. -/
theorem twenty_shiftedRowField {N : ℕ} (hN : 0<N) (kappa lambda : ℚ)
    (Pc Vc : List ℤ) (P V : List TailQ) (x : ℝ) :
    shiftedRowField (twentyRowWeights kappa lambda) Pc Vc P V x=
      paramPopulationRowField twenty N (kappa:ℝ) x+(lambda:ℝ)*paramCaseField twenty N x-
      4*barrierTrialT (trialSeq Pc P) x-barrierTrialS (trialSeq Vc V) x :=by
  rw [twenty_populationRowField hN,twenty_caseField hN]
  unfold shiftedRowField twentyRowWeights realEnergyRowTrialField realEnergyField
  dsimp
  push_cast
  ring

theorem twenty_shiftedColumnField (a : ℚ) (Vc : List ℤ) (V : List TailQ) (s : ℝ) :
    shiftedColumnField (twentyColumnWeights a) Vc V s=
      (3/20:ℝ)*Real.log s+(1/20:ℝ)*Real.log (1-s)+(a:ℝ)*Real.log (1+s)+
      2*barrierTrialT (trialSeq Vc V) s :=by
  unfold shiftedColumnField twentyColumnWeights realEnergyColumnTrialField realEnergyColumnField
  dsimp
  push_cast
  ring

/-- For the first case, the effective stored trial is half of the canonical trial. -/
theorem twenty_shiftedFirstRowField {N : ℕ} (hN : 0<N) (lambda : ℚ)
    (Pc Vc : List ℤ) (P V : List TailQ) (x : ℝ) :
    shiftedRowField (twentyRowWeights 1 lambda) Pc Vc P V x=
      paramPopulationRowField twenty N 1 x+(lambda:ℝ)*paramCaseField twenty N x-
      2*barrierTrialT (fun j =>2*trialSeq Pc P j) x-barrierTrialS (trialSeq Vc V) x :=by
  rw [twenty_shiftedRowField hN,population_trialT_mul]
  norm_num only [Rat.cast_one]
  ring

end
end CatalanMeasure.Parametric
