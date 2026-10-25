module
public import CatalanCore.Cert.QuarterContour.ModelCurve
public import CatalanCore.Cert.QuarterContour.ModelLedger
public import CatalanCore.Cert.QuarterContour.ModelErrorCeil
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.ModelGeometry
open CatalanCore.Cert.QuarterCompute
open CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial

/-- Atomic soundness of the integer-checked dyadic polynomial model. -/
theorem weighted_point_lower (S : ℕ) (m : Params) (p : Pt) (j : Jet)
    (hm : validParams m = true) (hj : validJet S m p j = true) (v : ℝ) (hv : |v| ≤ 1) :
    -(p.2.2 : ℝ)*(Model.logUpS (centreArg m p) : ℝ)/2^97 -
      (1/2)*((j.2.2 : ℝ)/2^32)*LogModel.poly 15 (roundedT S j v) -
      (errorCeil S j : ℝ)/2^64 ≤
    ((p.2.2 : ℝ)/2^32)*CatalanLambda.Decay.krho (1/2048 : ℝ) (modelZ m v) (QuarterContour.cpt p) := by
  obtain ⟨hq,hmass,hal,hau,hbl,hbu,hcap⟩ := validJet_facts S m p j hj
  obtain ⟨hU,hdiv,hrho⟩ := validParams_facts m hm
  obtain ⟨hS,hr,hd,ht,ht'⟩ := jet_rounding S m p j hj v hv
  have hqR : 0 < (q0N m p : ℝ) := by exact_mod_cast hq
  have hUR : 0 < (m.U : ℝ) := by exact_mod_cast hU
  have hc : 0 < centreQ m p := by unfold centreQ;positivity
  have htt : 0 < 1+exactT m p v := by linarith only [hr,(abs_le.mp ht).1]
  have hlog : Real.log (modelQ m p v) = Real.log (centreQ m p)+Real.log (1+exactT m p v) := by
    rw [modelQ_factor m p v hm (ne_of_gt hq),Real.log_mul hc.ne' htt.ne']
  have he := (abs_le.mp (jet_log_error S m p j hj v hv 15)).2
  have hb := centre_log_upper m p hU hq
  change Real.log (centreQ m p) ≤ _ at hb
  have hu : Real.log (modelQ m p v) ≤ (Model.logUpS (centreArg m p) : ℝ)/2^64+
      LogModel.poly 15 (roundedT S j v)+((radius S j)^16+2/(S : ℝ))/(1-radius S j) := by
    rw [hlog]
    linarith only [he,hb]
  let w : ℝ := (p.2.2 : ℝ)/2^32
  have hw : 0 ≤ w := by dsimp [w];positivity
  have hmul := mul_le_mul_of_nonneg_left hu hw
  have hk : -w*((Model.logUpS (centreArg m p) : ℝ)/2^64+
      LogModel.poly 15 (roundedT S j v)+((radius S j)^16+2/(S : ℝ))/(1-radius S j))/2 ≤
      w*CatalanLambda.Decay.krho (1/2048 : ℝ) (modelZ m v) (QuarterContour.cpt p) := by
    change _ ≤ w*(-(1/2 : ℝ)*Real.log (modelQ m p v))
    nlinarith only [hmul]
  have herr := errorCeil_bound S j hcap
  change ((j.2.2 : ℝ)/2^32)/2 * ((radius S j)^16+2/(S : ℝ))/(1-radius S j) ≤ _ at herr
  rw [hmass] at herr
  have hsplit : -w*((Model.logUpS (centreArg m p) : ℝ)/2^64+
      LogModel.poly 15 (roundedT S j v)+((radius S j)^16+2/(S : ℝ))/(1-radius S j))/2 =
      -(p.2.2 : ℝ)*(Model.logUpS (centreArg m p) : ℝ)/2^97-
      w/2*LogModel.poly 15 (roundedT S j v)-w/2*((radius S j)^16+2/(S : ℝ))/(1-radius S j) := by
    dsimp [w]
    ring
  rw [hsplit] at hk
  rw [hmass]
  change _ ≤ w*_
  dsimp [w] at hk ⊢
  linarith only [hk,herr]
end CatalanCore.Cert.QuarterContour.ModelGeometry
#print axioms CatalanCore.Cert.QuarterContour.ModelGeometry.weighted_point_lower