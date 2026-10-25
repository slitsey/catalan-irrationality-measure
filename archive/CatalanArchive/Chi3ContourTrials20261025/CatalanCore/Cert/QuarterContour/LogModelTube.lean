module
public import CatalanCore.Cert.QuarterContour.LogModel
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.LogModel

/-- Uniform displacement bound for the smoothed logarithmic kernel. -/
lemma krho_shift {rho W : ℝ} (hr : 0 < rho) (hW : 0 ≤ W) (z z0 c : ℂ)
    (hd : ‖z-z0‖ ≤ W) :
    CatalanLambda.Decay.krho rho z0 c - (W/rho+(W/rho)^2)/2 ≤
      CatalanLambda.Decay.krho rho z c := by
  let a := ‖z0-c‖
  let q0 := a^2+rho^2
  let q := ‖z-c‖^2+rho^2
  have ha : 0 ≤ a := norm_nonneg _
  have hp0 : 0 < q0 := by dsimp [q0]; positivity
  have hp : 0 < q := by dsimp [q]; positivity
  have hn : ‖z-c‖ ≤ W+a := by dsimp [a]; linarith [norm_sub_le_norm_sub_add_norm_sub z z0 c]
  have hs : ‖z-c‖^2 ≤ (W+a)^2 := by gcongr
  have hdiff : q-q0 ≤ 2*W*a+W^2 := by dsimp [q,q0]; nlinarith [hs]
  have hcross : 2*a*rho ≤ q0 := by dsimp [q0]; nlinarith [sq_nonneg (a-rho)]
  have hbase : rho^2 ≤ q0 := by dsimp [q0]; nlinarith [sq_nonneg a]
  have hc : 2*W*a/q0 ≤ W/rho := by
    apply (div_le_div_iff₀ hp0 hr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hcross hW]
  have hw : W^2/q0 ≤ (W/rho)^2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg W) (sq_pos_of_pos hr) hbase
  have hlog := Real.log_le_sub_one_of_pos (div_pos hp hp0)
  rw [Real.log_div hp.ne' hp0.ne'] at hlog
  have hdiv : q/q0-1 = (q-q0)/q0 := by field_simp
  rw [hdiv] at hlog
  have hb : Real.log q-Real.log q0 ≤ W/rho+(W/rho)^2 := by
    calc
      _ ≤ (q-q0)/q0 := hlog
      _ ≤ (2*W*a+W^2)/q0 := (div_le_div_iff_of_pos_right hp0).mpr hdiff
      _ = 2*W*a/q0+W^2/q0 := add_div _ _ _
      _ ≤ W/rho+(W/rho)^2 := add_le_add hc hw
  change -(1/2 : ℝ)*Real.log q0 - _ ≤ -(1/2 : ℝ)*Real.log q
  linarith

lemma Usig_shift {K : ℕ} {rho W : ℝ} (hr : 0 < rho) (hW : 0 ≤ W)
    (c : Fin K → ℂ) (m : Fin K → ℝ) (hm : ∀ i, 0 ≤ m i) (hprob : ∑ i, m i = 1)
    (z z0 : ℂ) (hd : ‖z-z0‖ ≤ W) :
    CatalanLambda.Decay.Usig rho c m z0 - (W/rho+(W/rho)^2)/2 ≤
      CatalanLambda.Decay.Usig rho c m z := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (krho_shift hr hW z z0 (c i) hd) (hm i))
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hprob, one_mul] at h
  exact h

lemma ray_quadratic (x0 y0 dx dy px py rho v : ℝ) :
    (x0+dx*v-px)^2+(y0+dy*v-py)^2+rho^2 =
      ((x0-px)^2+(y0-py)^2+rho^2) +
      (2*dx*(x0-px)+2*dy*(y0-py))*v+(dx^2+dy^2)*v^2 := by ring

lemma normalized_ratio (x0 y0 dx dy px py rho v : ℝ)
    (h0 : (x0-px)^2+(y0-py)^2+rho^2 ≠ 0) :
    (((x0+dx*v-px)^2+(y0+dy*v-py)^2+rho^2)-
       ((x0-px)^2+(y0-py)^2+rho^2))/((x0-px)^2+(y0-py)^2+rho^2) =
    ((2*dx*(x0-px)+2*dy*(y0-py))/((x0-px)^2+(y0-py)^2+rho^2))*v +
    ((dx^2+dy^2)/((x0-px)^2+(y0-py)^2+rho^2))*v^2 := by
  field_simp
  ring

lemma ratio_bound (a b v : ℝ) (hv : |v| ≤ 1) : |a*v+b*v^2| ≤ |a|+|b| := by
  calc
    _ ≤ |a*v|+|b*v^2| := abs_add_le _ _
    _ = |a| * |v|+|b| * |v|^2 := by rw [abs_mul,abs_mul,abs_pow]
    _ ≤ |a| * 1+|b| * 1^2 := by gcongr
    _ = _ := by ring
end CatalanCore.Cert.QuarterContour.LogModel
#print axioms CatalanCore.Cert.QuarterContour.LogModel.krho_shift