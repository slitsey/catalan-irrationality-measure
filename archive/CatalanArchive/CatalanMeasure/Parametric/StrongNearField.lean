module
public import CatalanMeasure.Cert.FieldEval
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
@[expose] public section
namespace CatalanMeasure.Parametric
open CatalanMeasure.Cert OAI.InternalCatalan Set
noncomputable section

private def nearBase (y : ℝ) : ℝ :=
  -(9/10:ℝ)*Real.log (1+y^2)+(3/4)*Real.log y-(9/50)*y

private def nearNumerator (y : ℝ) : ℝ :=
  3/4-(9/50)*y-(21/20)*y^2-(9/50)*y^3

private theorem near_deriv {y : ℝ} (hy : 0<y) :
    HasDerivAt nearBase (nearNumerator y/(y*(1+y^2))) y := by
  have hd : 1+y^2≠0 := by positivity
  have hp : HasDerivAt (fun x : ℝ => 1+x^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (1:ℝ)
  have hh := (((hp.log hd).const_mul (-(9/10:ℝ))).add
    ((Real.hasDerivAt_log hy.ne').const_mul (3/4:ℝ))).sub
    ((hasDerivAt_id y).const_mul (9/50:ℝ))
  refine hh.congr_deriv ?_
  unfold nearNumerator
  field_simp
  ring

private def nearBoxTerms : List LogTerm :=
  [⟨-9/10,0,1+(1811/2500)^2,0⟩,⟨3/4,0,1449/2000,0⟩]

private def nearBoxOK : Bool :=
  match sumLogs nearBoxTerms with
  | some ve => decide (ve.1+ve.2-(9/50)*(1811/2500) ≤ -(3/4:ℚ))
  | none => false

private theorem near_box :
    -(9/10:ℝ)*Real.log (1+(1811/2500:ℝ)^2)+
      (3/4)*Real.log (1449/2000:ℝ)-(9/50)*(1811/2500) ≤ -(3/4:ℝ) := by
  have hc : nearBoxOK=true := by decide +kernel
  unfold nearBoxOK at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hv : (nearBoxTerms.map LogTerm.val).sum =
        -(9/10:ℝ)*Real.log (1+(1811/2500:ℝ)^2)+
          (3/4)*Real.log (1449/2000:ℝ) := by
      simp only [nearBoxTerms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm (-9/10) (1+(1811/2500)^2) (by norm_num),
        realLogTerm (3/4) (1449/2000) (by norm_num)]
      norm_num
    rw [hv] at hh
    have hq : ve.1+ve.2-(9/50:ℚ)*(1811/2500) ≤ -(3/4:ℚ) := of_decide_eq_true hc
    have hr : ((ve.1+ve.2-(9/50:ℚ)*(1811/2500):ℚ):ℝ) ≤ ((-(3/4):ℚ):ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    norm_num at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

private theorem near_numerator_antitone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    nearNumerator y ≤ nearNumerator x := by
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  unfold nearNumerator
  linarith only [hxy,h2,h3]

private theorem near_box_dominates {y : ℝ}
    (hy : y ∈ Icc (1811/2500:ℝ) (1449/2000:ℝ)) : nearBase y ≤ -(3/4:ℝ) := by
  have hpos : 0<y := by linarith only [hy.1]
  have hlog1 : Real.log (1+(1811/2500:ℝ)^2) ≤ Real.log (1+y^2) :=
    Real.log_le_log (by positivity) (by nlinarith only [hy.1])
  have hlog2 : Real.log y ≤ Real.log (1449/2000:ℝ) := Real.log_le_log hpos hy.2
  have hh := near_box
  unfold nearBase
  linarith only [hlog1,hlog2,hy.1,hh]

/-- The stronger finite near-field payment holds under the original first-term
lower bound, uniformly on the whole positive interval. -/
theorem near_residual_field_le_three_fourths {p y : ℝ} (hp : (9/50:ℝ)≤p)
    (hy : 0<y) (_hy1 : y≤1) :
    -(9/10:ℝ)*Real.log (1+y^2)+(3/4)*Real.log y-p*y ≤ -(3/4:ℝ) := by
  have hmono : MonotoneOn nearBase (Ioc (0:ℝ) (1811/2500:ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx
      exact (near_deriv hx.1).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ioc,mem_Ioo] at hx
      exact (near_deriv hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ioc,mem_Ioo] at hx
      rw [(near_deriv hx.1).deriv]
      apply div_nonneg _ (mul_nonneg hx.1.le (by positivity))
      have hh := near_numerator_antitone hx.1.le hx.2.le
      norm_num [nearNumerator] at hh ⊢
      linarith only [hh]
  have hanti : AntitoneOn nearBase (Ici (1449/2000:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro x hx
      have hx0 : 0<x := lt_of_lt_of_le (by norm_num : (0:ℝ)<1449/2000) hx
      exact (near_deriv hx0).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ici,mem_Ioi] at hx
      exact (near_deriv (by linarith only [hx])).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ici,mem_Ioi] at hx
      have hx0 : 0<x := by linarith only [hx]
      rw [(near_deriv hx0).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg hx0.le (by positivity))
      have hh := near_numerator_antitone (by norm_num : (0:ℝ)≤1449/2000) hx.le
      norm_num [nearNumerator] at hh ⊢
      linarith only [hh]
  have hb : nearBase y ≤ -(3/4:ℝ) := by
    by_cases ha : y≤1811/2500
    · exact (hmono ⟨hy,ha⟩ (by norm_num) ha).trans (near_box_dominates (by norm_num))
    · by_cases hc : 1449/2000≤y
      · exact (hanti (by norm_num) hc hc).trans (near_box_dominates (by norm_num))
      · exact near_box_dominates ⟨le_of_not_ge ha,(le_of_not_ge hc)⟩
  have hpy := mul_le_mul_of_nonneg_right hp hy.le
  unfold nearBase at hb
  linarith only [hb,hpy]

end
end CatalanMeasure.Parametric
