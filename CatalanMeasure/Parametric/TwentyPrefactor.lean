module
public import CatalanMeasure.Parametric.TwentyWeightedIntegrand
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter Real
open scoped BigOperators Topology
noncomputable section

def twentyPrefactorLinearK : ℝ :=2+400*Real.exp 12

theorem twentyPrefactorLinearK_pos : 0<twentyPrefactorLinearK :=by
  unfold twentyPrefactorLinearK
  positivity

theorem twenty_sheet_prefactor_le {N : ℕ} (hN : 0<N) :
    (2:ℝ)^(twenty.n N)*twentySheetPrefactor N ≤
      2*(twentyPrefactorLinearK*(N:ℝ))^(20*N) :=by
  have hnN : twenty.n N=20*N :=rfl
  have hN1 : (1:ℝ) ≤ N :=by exact_mod_cast hN
  have hn1 : (1:ℝ) ≤ (twenty.n N:ℝ) :=by rw [hnN];push_cast;nlinarith only [hN1]
  have he : (1:ℝ) ≤ Real.exp 12 :=by rw [Real.one_le_exp_iff];norm_num
  have hr :=Real.rpow_le_rpow_of_exponent_le hn1
    (show (twenty.n N:ℝ)/2 ≤ (twenty.n N:ℝ) by linarith only [hn1])
  rw [Real.rpow_natCast] at hr
  have hb : (3/2:ℝ)*(twenty.n N:ℝ) ≤ 1+10*Real.exp 12*(twenty.n N:ℝ) :=by
    nlinarith only [mul_le_mul_of_nonneg_right he (show (0:ℝ) ≤ (twenty.n N:ℝ) by positivity)]
  have hfirst : (3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^((twenty.n N:ℝ)/2) ≤
      (1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N) :=by
    calc
      _ ≤ (3/2:ℝ)^(twenty.n N)*(twenty.n N:ℝ)^(twenty.n N) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = ((3/2:ℝ)*(twenty.n N:ℝ))^(twenty.n N) :=(mul_pow _ _ _).symm
      _ ≤ _ :=pow_le_pow_left₀ (by positivity) hb _
  have hS : twentySheetPrefactor N ≤ 2*(1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N) :=by
    unfold twentySheetPrefactor
    linarith only [hfirst]
  have hK : 2*(1+10*Real.exp 12*(twenty.n N:ℝ)) ≤ twentyPrefactorLinearK*(N:ℝ) :=by
    rw [hnN]
    unfold twentyPrefactorLinearK
    push_cast
    nlinarith only [hN1]
  calc
    _ ≤ (2:ℝ)^(twenty.n N)*(2*(1+10*Real.exp 12*(twenty.n N:ℝ))^(twenty.n N)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 2*(2*(1+10*Real.exp 12*(twenty.n N:ℝ)))^(twenty.n N) :=by rw [mul_pow];ring
    _ ≤ 2*(twentyPrefactorLinearK*(N:ℝ))^(twenty.n N) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hK _) (by norm_num)
    _ = _ :=by rw [hnN]

theorem twenty_prefactor_error_tendsto :
    Tendsto (fun N : ℕ =>
      (Real.log 2+20*(N:ℝ)*(Real.log twentyPrefactorLinearK+Real.log (N:ℝ)))/(20*(N:ℝ))^2)
      atTop (𝓝 0) :=by
  have hi : Tendsto (fun N : ℕ =>(N:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ =>Real.log (N:ℝ)/(N:ℝ)) atTop (𝓝 0) :=by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ =>(N:ℝ)) atTop atTop)
  have hh :=((hi.pow 2).const_mul (Real.log 2/400)).add
    (((hi.const_mul (Real.log twentyPrefactorLinearK)).add hl).div_const 20)
  simp only [zero_pow (by norm_num : 2≠0),mul_zero,add_zero,zero_div] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ)≠0 :=by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  <;> ring

theorem twenty_sheet_prefactor_eventually {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,(2:ℝ)^(twenty.n N)*twentySheetPrefactor N ≤
      Real.exp (ε*(20*(N:ℝ))^2) :=by
  have hh :=(tendsto_order.mp twenty_prefactor_error_tendsto).2 ε hε
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with N hhN hN
  have hn : (0:ℝ)<N :=by exact_mod_cast hN
  have hlog :=(div_lt_iff₀ (sq_pos_of_pos (by positivity : (0:ℝ)<20*(N:ℝ)))).mp hhN
  have he : 2*(twentyPrefactorLinearK*(N:ℝ))^(20*N)=
      Real.exp (Real.log 2+20*(N:ℝ)*(Real.log twentyPrefactorLinearK+Real.log (N:ℝ))) :=by
    rw [Real.exp_add,mul_add,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
    rw [show 20*(N:ℝ)=((20*N:ℕ):ℝ) by push_cast;rfl,
      Real.exp_nat_mul,Real.exp_nat_mul,Real.exp_log twentyPrefactorLinearK_pos,Real.exp_log hn,
      mul_pow]
  exact (twenty_sheet_prefactor_le hN).trans
    (by rw [he];exact Real.exp_le_exp.mpr hlog.le)

end
end CatalanMeasure.Parametric
