module
public import CatalanMeasure.Parametric.PopulationCase
public import CatalanMeasure.Parametric.RestrictedQuadrature
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
noncomputable section

def paramPopulationRowField (P : Parameters) (N : ℕ) (k x : ℝ) : ℝ :=
  (P.A N:ℝ)/(P.n N:ℝ)*Real.log |x|+2*(P.h N:ℝ)/(P.n N:ℝ)*Real.log (1-x)-
    ((P.H N:ℝ)/(P.n N:ℝ)+(k-2)/2)*Real.log (1+x^2)

def paramResidualFixedOne (P : Parameters) (N : ℕ) (lambda x : ℝ) : ℝ :=
  -(P.A N:ℝ)/(P.n N:ℝ)*Real.log 2-
    ((1/2:ℝ)-(P.g N:ℝ)/(P.n N:ℝ))*Real.log (1+x^2)+lambda*paramCaseField P N x

/-- A uniform cap, valid on all real x; no sampling assumption is used. -/
theorem paramResidualFixedOne_le {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0<N) {lambda : ℝ} (hlambda : 0 ≤ lambda) (x : ℝ) :
    paramResidualFixedOne P N lambda x ≤
      -(P.A N:ℝ)/(P.n N:ℝ)*Real.log 2+lambda*2*(P.g N:ℝ)/(P.n N:ℝ) :=by
  have hn : (0:ℝ)<P.n N :=by exact_mod_cast n_pos hP hN
  have hg :=two_g_lt_n hP hN
  have hgr : 2*(P.g N:ℝ)<(P.n N:ℝ) :=by exact_mod_cast hg
  have hcoef : 0 ≤ (1/2:ℝ)-(P.g N:ℝ)/(P.n N:ℝ) :=by
    have hh : (P.g N:ℝ)/(P.n N:ℝ) ≤ 1/2 :=by
      rw [div_le_iff₀ hn]
      linarith
    linarith
  have hlog : 0 ≤ Real.log (1+x^2) :=Real.log_nonneg (by nlinarith [sq_nonneg x])
  have hr : 0 ≤ 2*x^2/(1+x^2) :=div_nonneg (by positivity) (by positivity)
  have ha :=mul_nonneg hcoef hlog
  have hb :=mul_nonneg hlambda hr
  unfold paramResidualFixedOne paramCaseField
  ring_nf at ha hb ⊢
  linarith only [ha,hb]

end
end CatalanMeasure.Parametric
