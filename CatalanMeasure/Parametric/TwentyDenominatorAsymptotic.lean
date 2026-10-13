module
public import CatalanMeasure.Parametric.TwentyDenominatorGrowth
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter Real
open scoped BigOperators Topology
noncomputable section

theorem twentyCombinedOddLoss_above {x : ℝ} (hx : 27 ≤ x) :
    twentyCombinedOddLoss x=0 :=by
  rw [twentyCombinedOddLoss,twentyOddLoss_segment7 x hx,
    twentyPrimeGain_right (by linarith only [hx])]
  ring

theorem twenty_large_prime_sum_le (N : ℕ) :
    (∑ p ∈ (Finset.Ioc 0 (OAI.InternalCatalan.H N)).filter
      (fun p : ℕ =>p.Prime ∧ 2*Real.sqrt (OAI.InternalCatalan.H N)<(p:ℝ)),
      twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ)) ≤
    ∑ p ∈ Finset.Ioc 0 (27*N) with p.Prime,
      twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ) :=by
  let f : ℕ → ℝ :=fun p =>twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ)
  let s :=measurePrimes N
  let t :=(Finset.Ioc 0 (27*N)).filter Nat.Prime
  have ht : t ⊆ s :=by
    intro p hp
    have hpI :=Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hpI.1).1,?_⟩,hpI.2⟩
    have hh :=(Finset.mem_Ioc.mp hpI.1).2
    unfold OAI.InternalCatalan.H
    omega
  have he : (∑ p ∈ s,f p)=∑ p ∈ t,f p :=by
    symm
    apply Finset.sum_subset ht
    intro p hp hout
    have hpI :=Finset.mem_filter.mp hp
    have hpH : 27*N<p :=by
      by_contra hn
      push Not at hn
      exact hout (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpI.2.pos,hn⟩,hpI.2⟩)
    have hN : 0<N :=by
      have hh :=(Finset.mem_Ioc.mp hpI.1).2
      unfold OAI.InternalCatalan.H at hh
      omega
    have hn : (0:ℝ)<N :=by exact_mod_cast hN
    have hr : (27:ℝ) ≤ (p:ℝ)/N :=by
      apply (le_div_iff₀ hn).mpr
      exact_mod_cast hpH.le
    simp only [f,twentyCombinedOddLoss_above hr,zero_mul]
  calc
    _ ≤ ∑ p ∈ s,f p :=by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hh :=Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hh.1,hh.2.1⟩
      · intro p hp _
        exact mul_nonneg (twentyCombinedOddLoss_bounds _).1
          (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le))
    _ = _ :=he

theorem twenty_large_prime_normalized_eventually_upper {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,
      ((N:ℝ)*∑ p ∈ (Finset.Ioc 0 (OAI.InternalCatalan.H N)).filter
        (fun p : ℕ =>p.Prime ∧ 2*Real.sqrt (OAI.InternalCatalan.H N)<(p:ℝ)),
        twentyCombinedOddLoss ((p:ℝ)/N)*Real.log (p:ℝ))/(20*(N:ℝ))^2 <
      8795/4800+ε :=by
  have hh :=(tendsto_order.mp twentyCombinedOddLoss_normalized_prime_sum_tendsto).2
    (8795/4800+ε) (by linarith only [hε])
  filter_upwards [hh] with N hN
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (twenty_large_prime_sum_le N) (Nat.cast_nonneg N))
      (sq_nonneg _)) hN

theorem twenty_log_denomBound_eventually_le {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,Real.log (twentyDenomBound N) ≤
      (8795/4800+(21/200)*Real.log 2+ε)*(20*(N:ℝ))^2 :=by
  have h2 :=(tendsto_order.mp (twenty_tendsto_twoAdic_log_error 0)).2 (ε/8) (by positivity)
  have hs :=(tendsto_order.mp (smallOddPrimeError_div_sq_tendsto_zero 1)).2
    (25*ε/576) (by positivity)
  have hl :=twenty_large_prime_normalized_eventually_upper (ε :=ε/4) (by positivity)
  obtain ⟨K,hK⟩ :=exists_nat_gt (131/ε)
  filter_upwards [h2,hs,hl,eventually_ge_atTop K,eventually_gt_atTop (0:ℕ)]
    with N h2N hsN hlN hKN hN
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  have hnN : (OAI.InternalCatalan.n N:ℝ)=48*(N:ℝ) :=by simp [OAI.InternalCatalan.n]
  have hHN : (OAI.InternalCatalan.H N:ℝ)=65*(N:ℝ) :=by simp [OAI.InternalCatalan.H]
  have hn : (0:ℝ)<20*(N:ℝ) :=by positivity
  have hn2 : (0:ℝ)<(20*(N:ℝ))^2 :=sq_pos_of_pos hn
  have hεN : 131<ε*(N:ℝ) :=by
    have hKR : (K:ℝ) ≤ N :=by exact_mod_cast hKN
    have h1 :=(div_lt_iff₀ hε).mp hK
    nlinarith only [h1,mul_le_mul_of_nonneg_right hKR hε.le]
  have hlog2 : (0:ℝ)<Real.log 2 :=Real.log_pos (by norm_num)
  have hlog2' : Real.log 2<1 :=by
    have hh :=Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ)<2) (by norm_num)
    linarith only [hh]
  have h2N' : 2+Real.logb 2 (8*discrepancyNormFactor 0*(27*(N:ℝ))^2)<
      ε/8*(20*(N:ℝ)) :=(div_lt_iff₀ hn).mp h2N
  have hN1 : (1:ℝ) ≤ N :=by exact_mod_cast hN
  have hone : (1:ℝ) ≤ ε/8*(20*(N:ℝ))^2 :=by
    nlinarith only [hN1,mul_lt_mul_of_pos_right hεN hNR]
  have hT2 : (twentyTwoAdicBound N+1)*Real.log 2 ≤
      ((21/200)*Real.log 2+ε/4)*(20*(N:ℝ))^2 :=by
    have hb : twentyTwoAdicBound N+1 ≤ (21/200+ε/4)*(20*(N:ℝ))^2 :=by
      unfold twentyTwoAdicBound
      nlinarith only [hone,mul_lt_mul_of_pos_left h2N' hn]
    have hb0 : 0 ≤ twentyTwoAdicBound N+1 :=by linarith only [twentyTwoAdicBound_nonneg hN]
    have he0 : 0 ≤ ε/4*(20*(N:ℝ))^2 :=by positivity
    nlinarith only [mul_le_mul_of_nonneg_right hb hlog2.le,
      mul_le_mul_of_nonneg_left hlog2'.le he0]
  have hS : smallOddPrimeError 1 N ≤ ε/4*(20*(N:ℝ))^2 :=by
    have hh :=((div_lt_iff₀ (sq_pos_of_pos (by rw [hnN];positivity))).mp hsN).le
    rw [hnN] at hh
    nlinarith only [hh]
  have hL :=((div_lt_iff₀ hn2).mp hlN).le
  have hθ : Chebyshev.theta (OAI.InternalCatalan.H N:ℝ) ≤ ε/4*(20*(N:ℝ))^2 :=by
    have hh :=Chebyshev.theta_le_log4_mul_x
      (show (0:ℝ) ≤ (OAI.InternalCatalan.H N:ℝ) by positivity)
    have hlog4 : Real.log 4<2 :=by
      have he : Real.log 4=2*Real.log 2 :=by
        rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
        norm_num
      linarith only [hlog2',he]
    rw [hHN] at hh ⊢
    nlinarith only [hh,mul_lt_mul_of_pos_right hεN hNR,
      mul_lt_mul_of_pos_right hlog4 hNR]
  have hmain :=twenty_log_denomBound_le hN
  linarith only [hmain,hT2,hS,hL,hθ]

end
end CatalanMeasure.Parametric
