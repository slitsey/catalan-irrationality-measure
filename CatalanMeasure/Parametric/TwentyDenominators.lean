module
public import CatalanMeasure.Parametric.TwentyTwoAdicValuation
public import CatalanMeasure.Parametric.TwentyCombinedOddLoss
public import CatalanMeasure.Parametric.OddLogBounds
public import CatalanMeasure.Denominators
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Filter Real
open scoped BigOperators Topology
noncomputable section

def twentyTwoAdicBound (N : ℕ) : ℝ :=
  42*(N:ℝ)^2+40*N+(20*(N:ℝ))*Real.logb 2
    (8*discrepancyNormFactor 0*(27*(N:ℝ))^2)

def twentyDenomExp (N p : ℕ) : ℕ :=
  if p=2 then ⌈twentyTwoAdicBound N⌉₊
  else if (p:ℝ) ≤ 2*Real.sqrt (OAI.InternalCatalan.H N) then
    6*OAI.InternalCatalan.n N*Nat.log p (OAI.InternalCatalan.H N)
  else ⌈(N:ℝ)*twentyCombinedOddLoss ((p:ℝ)/N)⌉₊

def twentyDenomBound (N : ℕ) : ℕ :=∏ p ∈ measurePrimes N,p^twentyDenomExp N p

theorem twentyDenomBound_ne_zero (N : ℕ) : twentyDenomBound N≠0 :=by
  unfold twentyDenomBound
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero

theorem twentyTwoAdicBound_nonneg {N : ℕ} (hN : 0<N) : 0 ≤ twentyTwoAdicBound N :=by
  have hF :=one_le_discrepancyNormFactor 0
  have hH : (1:ℝ) ≤ 27*(N:ℝ) :=by
    have hn : (1:ℝ) ≤ N :=by exact_mod_cast hN
    linarith only [hn]
  have ha : (1:ℝ) ≤ 8*discrepancyNormFactor 0*(27*(N:ℝ))^2 :=by nlinarith
  have hl :=Real.logb_nonneg (b :=2) (by norm_num) ha
  unfold twentyTwoAdicBound
  positivity

theorem twenty_large_prime_geometry {N p : ℕ} (hbig : 1000000000000 ≤ N)
    (hcut : 2*Real.sqrt (OAI.InternalCatalan.H N)<(p:ℝ)) :
    1000000 ≤ p ∧ 27*N<p^2 :=by
  have hn : (1000000000000:ℝ) ≤ N :=by exact_mod_cast hbig
  have hs :=Real.sq_sqrt (Nat.cast_nonneg (OAI.InternalCatalan.H N))
  have hs0 :=Real.sqrt_nonneg (OAI.InternalCatalan.H N:ℝ)
  have hh : (OAI.InternalCatalan.H N:ℝ)=65*(N:ℝ) :=by
    simp only [OAI.InternalCatalan.H,Nat.cast_mul,Nat.cast_ofNat]
  rw [hh] at hs hs0 hcut
  have hpR : (1000000:ℝ) ≤ p :=by nlinarith only [hn,hs,hs0,hcut]
  have hsqR : (27:ℝ)*N<(p:ℝ)^2 :=by nlinarith only [hn,hs,hs0,hcut]
  constructor
  · exact_mod_cast hpR
  · exact_mod_cast hsqR

theorem twenty_combined_odd_large_all {N p : ℕ} [Fact p.Prime]
    (hbig : 1000000000000 ≤ N) (hp2 : p≠2)
    (hcut : 2*Real.sqrt (OAI.InternalCatalan.H N)<(p:ℝ))
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(N:ℝ)*twentyCombinedOddLoss ((p:ℝ)/N) ≤
      (padicValRat p (determinantRat twenty z N):ℝ) :=by
  have hN : 0<N :=by omega
  have hg :=twenty_large_prime_geometry hbig hcut
  by_cases hh : p ≤ 27*N
  · exact twenty_combined_determinant_odd_profile hN hp2 hg.1 hg.2 hh z hz
  have hn : (0:ℝ)<N :=by exact_mod_cast hN
  have hratio : (27:ℝ) ≤ (p:ℝ)/N :=by
    apply (le_div_iff₀ hn).mpr
    exact_mod_cast (show 27*N ≤ p by omega)
  rw [twentyCombinedOddLoss,twentyOddLoss_segment7 _ hratio,
    twentyPrimeGain_right (by linarith only [hratio])]
  simp only [mul_zero,zero_mul,sub_zero,neg_zero]
  exact_mod_cast paramDeterminantRat_above_degrees_local_integral twenty (N :=N) (p :=p) hp2
    (by rw [twenty_H];omega) z hz

theorem twenty_integer_odd_log_bound {N p : ℕ} [Fact p.Prime]
    (hp2 : p≠2) (i : ℕ) :
    -((6*OAI.InternalCatalan.n N*Nat.log p (OAI.InternalCatalan.H N):ℕ):ℤ) ≤
      padicValRat p (determinantRat twenty (i:ℚ) N) :=by
  have hv :=paramDeterminantRat_odd_prime_log_lower twenty hp2 (i:ℚ) N
  simp only [Rat.den_natCast,padicValNat.one,Nat.cast_zero,sub_zero] at hv
  have hlog : Nat.log p (twenty.H N) ≤ Nat.log p (OAI.InternalCatalan.H N) :=
    Nat.log_mono_right (by rw [twenty_H];unfold OAI.InternalCatalan.H;omega)
  have hnn : twenty.n N ≤ OAI.InternalCatalan.n N :=by
    change 20*N ≤ 48*N
    omega
  have hm :=Nat.mul_le_mul (Nat.mul_le_mul_left 6 hnn) hlog
  have hmI : ((6*twenty.n N*Nat.log p (twenty.H N):ℕ):ℤ) ≤
      ((6*OAI.InternalCatalan.n N*Nat.log p (OAI.InternalCatalan.H N):ℕ):ℤ) :=by exact_mod_cast hm
  push_cast at hmI ⊢
  nlinarith only [hv,hmI]

theorem twenty_integer_determinant_valuation {N : ℕ} (hbig : 1000000000000 ≤ N)
    (i : ℕ) {p : ℕ} [Fact p.Prime] (hd : determinantRat twenty (i:ℚ) N≠0) :
    -(twentyDenomExp N p:ℤ) ≤ padicValRat p (determinantRat twenty (i:ℚ) N) :=by
  have hN : 0<N :=by omega
  unfold twentyDenomExp
  split_ifs with h2 hsmall
  · subst p
    have hv :=twentyDeterminantRat_two_adic_valuation_lower (i:ℚ) hN hd
    have hF :=discrepancyNormFactor_natCast_le i
    have hFi :=one_le_discrepancyNormFactor (i:ℚ)
    have hH : (0:ℝ)<27*(N:ℝ) :=by positivity
    have hH2 :=pow_pos hH 2
    have hl : Real.logb 2 (8*discrepancyNormFactor (i:ℚ)*(27*(N:ℝ))^2) ≤
        Real.logb 2 (8*discrepancyNormFactor 0*(27*(N:ℝ))^2) :=by
      apply Real.logb_le_logb_of_le (by norm_num)
      · exact mul_pos (mul_pos (by norm_num) (by linarith only [hFi])) hH2
      · exact mul_le_mul_of_nonneg_right (by linarith only [hF]) hH2.le
    have hc :=Nat.le_ceil (twentyTwoAdicBound N)
    have hm :=mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ 20*(N:ℝ))
    have hr : -(⌈twentyTwoAdicBound N⌉₊:ℝ) ≤
        (padicValRat 2 (determinantRat twenty (i:ℚ) N):ℝ) :=by
      unfold twentyTwoAdicBound at hc ⊢
      nlinarith only [hv,hc,hm]
    exact_mod_cast hr
  · exact twenty_integer_odd_log_bound h2 i
  · have hv :=twenty_combined_odd_large_all hbig h2 (not_le.mp hsmall)
      (i:ℚ) (natCast_den_zmod_ne_zero i p)
    have hc :=Nat.le_ceil ((N:ℝ)*twentyCombinedOddLoss ((p:ℝ)/N))
    have hr : -(⌈(N:ℝ)*twentyCombinedOddLoss ((p:ℝ)/N)⌉₊:ℝ) ≤
        (padicValRat p (determinantRat twenty (i:ℚ) N):ℝ) :=by linarith only [hv,hc]
    exact_mod_cast hr

theorem twenty_den_dvd_denomBound {N : ℕ} (hbig : 1000000000000 ≤ N) (i : ℕ)
    (hd : determinantRat twenty (i:ℚ) N≠0) :
    (determinantRat twenty (i:ℚ) N).den ∣ twentyDenomBound N :=by
  have hM :=twentyDenomBound_ne_zero N
  rw [← Nat.factorization_le_iff_dvd (Rat.den_pos _).ne' hM,Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime :=⟨hp⟩
    rw [Nat.factorization_def _ hp]
    by_cases hS : p∈measurePrimes N
    · have h1 :=padicValNat_den_le_of_padicValRat (twenty_integer_determinant_valuation (p :=p) hbig i hd)
      have h2 : twentyDenomExp N p ≤ (twentyDenomBound N).factorization p :=by
        apply (hp.pow_dvd_iff_le_factorization hM).mp
        unfold twentyDenomBound
        exact Finset.dvd_prod_of_mem (fun p =>p^twentyDenomExp N p) hS
      exact h1.trans h2
    · have hH : OAI.InternalCatalan.H N<p :=by
        by_contra hle
        push Not at hle
        exact hS (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,hle⟩,hp⟩)
      have hp2 : p≠2 :=by unfold OAI.InternalCatalan.H at hH;omega
      have hv :=paramDeterminantRat_above_degrees_local_integral twenty (N :=N) (p :=p) hp2
        (by rw [twenty_H];unfold OAI.InternalCatalan.H at hH;omega)
        (i:ℚ) (natCast_den_zmod_ne_zero i p)
      have h0 :=padicValNat_den_le_of_padicValRat (e :=0) (by simpa using hv)
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem twenty_exists_int_denomBound_mul {N : ℕ} (hbig : 1000000000000 ≤ N) (i : ℕ) :
    ∃ m : ℤ,(twentyDenomBound N:ℚ)*determinantRat twenty (i:ℚ) N=m :=by
  by_cases hd : determinantRat twenty (i:ℚ) N=0
  · exact ⟨0,by rw [hd,mul_zero,Int.cast_zero]⟩
  obtain ⟨c,hc⟩ :=twenty_den_dvd_denomBound hbig i hd
  refine ⟨(c:ℤ)*(determinantRat twenty (i:ℚ) N).num,?_⟩
  rw [hc]
  push_cast
  have hh :=Rat.mul_den_eq_num (determinantRat twenty (i:ℚ) N)
  linear_combination (c:ℚ)*hh

end
end CatalanMeasure.Parametric
