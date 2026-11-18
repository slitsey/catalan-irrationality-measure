module
public import CatalanCore.Li2.DecayCert.Compile.Perturbation
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem norm_log_half_jphi_of_bound (ζ : ℂ) (hs : 1 < jc ζ) (H : ℝ)
    (hH : ‖jphi ζ‖ ≤ H) :
    ‖Complex.log (jphi ζ/2)‖ ≤ Real.log H+Real.log 2+Real.pi := by
  have hp : 0 < ‖jphi ζ‖ := lt_trans (by norm_num) (jphi_spec hs).1
  have hHpos : 0 < H := hp.trans_le hH
  have hlo : 0 ≤ Real.log ‖jphi ζ‖ := Real.log_nonneg (jphi_spec hs).1.le
  have hhi : Real.log ‖jphi ζ‖ ≤ Real.log H := Real.log_le_log hp hH
  have ht : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : |Real.log ‖jphi ζ/2‖| ≤ Real.log H+Real.log 2 := by
    rw [norm_div,Complex.norm_two,Real.log_div hp.ne' (by norm_num)]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hlo,abs_of_nonneg ht]; linarith)
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by
    simp only [Complex.log_re,Complex.log_im]
    exact add_le_add hlog (Complex.abs_arg_le_pi _))

theorem jphi_le_of_quadratic_bound (ζ : ℂ) (hs : 1 < jc ζ) (Z H : ℝ)
    (hZ : ‖ζ‖ ≤ Z) (hH : Z ≤ H) (hsq : Z^2+1 ≤ (H-Z)^2) : ‖jphi ζ‖ ≤ H := by
  have hroot : Real.sqrt (‖ζ‖^2+1) ≤ H-Z := by
    have hn : 0 ≤ H-Z := sub_nonneg.mpr hH
    have hsqζ : ‖ζ‖^2 ≤ Z^2 := pow_le_pow_left₀ (norm_nonneg ζ) hZ 2
    have hupper : ‖ζ‖^2+1 ≤ (H-Z)^2 := by linarith
    rw [← Real.sqrt_sq hn]
    exact Real.sqrt_le_sqrt hupper
  exact (norm_jphi_upper ζ hs).trans (by linarith)

theorem discPrimitive_norm_bound_checked (d : SegmentData) (ζ γ : ℂ) (hs : 1 < jc ζ)
    (dist R fraction H : ℝ) (hdist : dist=Metric.infDist ζ sourceSlit) (hd : 0 < dist)
    (hf : fraction < 1) (hγ : ‖γ‖*R ≤ fraction*dist) (hφ : ‖jphi ζ‖ ≤ H)
    (G : ℂ → ℂ) (hG : IsDiscSegmentPrimitive d ζ γ R G) :
    ∀ u ∈ Metric.ball (0:ℂ) R, ‖G u‖ ≤
      |d.c 0| *(Real.log H+Real.log 2+Real.pi-Real.log (1-fraction))+
        ∑ k ∈ Finset.range d.N, |d.c (k+1)|/(k+1:ℕ) := by
  rcases hG with ⟨L,hLan,hLzero,hbranch⟩
  intro u hu
  have huR : ‖u‖ < R := by simpa only [Metric.mem_ball,dist_zero_right] using hu
  have ha : ‖γ*u‖ ≤ fraction*dist := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left huR.le (norm_nonneg γ)).trans hγ
  have had : ‖γ*u‖ < dist := ha.trans_lt (by nlinarith)
  have hfrac : ‖γ*u‖/dist ≤ fraction := (div_le_iff₀ hd).mpr ha
  have hlog : -Real.log (1-‖γ*u‖/dist) ≤ -Real.log (1-fraction) := by
    apply neg_le_neg
    exact Real.log_le_log (sub_pos.mpr hf) (by linarith)
  have hL : ‖L u‖ ≤ Real.log H+Real.log 2+Real.pi-Real.log (1-fraction) := by
    have hdiff := branchLog_drift L ζ γ R dist hd hLan hLzero
      (fun v hv => ⟨(hbranch v hv).1,(hbranch v hv).2.1⟩) hdist u huR had
    have hzero := norm_log_half_jphi_of_bound ζ hs H hφ
    rw [← hLzero] at hzero
    have htri := norm_le_norm_sub_add (L u) (L 0)
    linarith
  have hterms : ‖∑ k ∈ Finset.range d.N,
      (d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)/(k+1:ℕ)‖ ≤
      ∑ k ∈ Finset.range d.N, |d.c (k+1)|/(k+1:ℕ) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    have hphi := (jphi_spec (hbranch u hu).1).1
    have hinv : ‖(jphi (ζ+γ*u))⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (lt_trans (by norm_num) hphi)).mpr hphi.le
    rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]
    have hn : ‖(jphi (ζ+γ*u))⁻¹‖^(k+1) ≤ 1 := pow_le_one₀ (norm_nonneg _) hinv
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (abs_nonneg (d.c (k+1)))
  rw [(hbranch u hu).2.2]
  calc
    _ ≤ ‖(d.c 0:ℂ)*L u‖+‖∑ k ∈ Finset.range d.N,
        (d.c (k+1):ℂ)*(jphi (ζ+γ*u))⁻¹^(k+1)/(k+1:ℕ)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left hL (abs_nonneg _)) hterms

#print axioms norm_log_half_jphi_of_bound
#print axioms jphi_le_of_quadratic_bound
#print axioms discPrimitive_norm_bound_checked
end
end CatalanCore.Li2.DecayCert
