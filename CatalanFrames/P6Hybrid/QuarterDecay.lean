module
public import CatalanFrames.P6Hybrid.QuarterAssembly
public import CatalanCore.Cert.SigmaQuarter.Final
public import CatalanCore.Cert.Sigma300.Glue
public import CatalanCore.Decay.Rect.DecayMinor
@[expose] public section
open CatalanCore CatalanCore.Rect CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.Quarter
open CatalanCore.Cert.SigmaQuarter

theorem adm_real {r m : ℕ} (ha : Adm r m) :
    (((1/4 : ℚ)) : ℝ)*r ≤ m ∧ (m : ℝ) ≤ (((1/4 : ℚ)) : ℝ)*r + 3/4 := by
  have h1 : (r : ℝ) ≤ 4*m := by exact_mod_cast ha.1
  have h2 : (4 : ℝ)*m ≤ r+3 := by exact_mod_cast ha.2
  push_cast
  constructor <;> linarith

/-- The general common-minor decay engine is instantiated without a new
determinant estimate or any historical witness certificate. -/
theorem decay : HasDecay family (2323303/500000) (4013201/500000) := by
  have hInu : (((184428/100000 : ℚ)) : ℝ) ≤
      CatalanCore.Decay.Jfun (((1/4 : ℚ)) : ℝ) := by
    convert Inu_le using 1 <;> norm_num
  have h := hasDecay_commonMinorFam (Fr := p6Frame)
    CatalanCore.Cert.Sigma300.p6_decayOK certQ
    (α := 1/4) (by norm_num) (a := 3/4) (by norm_num)
    hg_Q mQ_nonneg (Rc := 16) (by norm_num) cQ_norm
    hInu D_le (by rw [certQ_ccert]; norm_num) 1
    (fun r m h => adm_real h)
  rw [certQ_ccert] at h
  convert h using 1 <;> norm_num

theorem chi3_measure : Measure.MeasureLBAt chi3L2 ((((37493/2500) : ℚ)) : ℝ) := by
  convert chi3_measure_of_decay decay using 1 <;> norm_num
end CatalanFrames.P6Hybrid.Quarter
#print axioms CatalanFrames.P6Hybrid.Quarter.decay
#print axioms CatalanFrames.P6Hybrid.Quarter.chi3_measure
