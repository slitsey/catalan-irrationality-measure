module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyOddNormalization
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPrimeGain
public import CatalanArchive.CatalanMeasure.Parametric.TwentySparseValuation
public import OAI.NumberTheory.Catalan.Arithmetic.OddPrimeLossNormalization
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Real Filter
open scoped BigOperators Topology
noncomputable section

def twentyCombinedOddLoss (x : ℝ) : ℝ :=twentyOddLoss x-twentyPrimeGain x

theorem continuous_twentyCombinedOddLoss : Continuous twentyCombinedOddLoss :=
  continuous_twentyOddLoss.sub continuous_twentyPrimeGain

theorem twentyOddLoss_bounds (x : ℝ) : 0 ≤ twentyOddLoss x ∧ twentyOddLoss x ≤ 40 :=by
  by_cases h0 : x ≤ 10
  · rw [twentyOddLoss_segment0 x h0];norm_num
  by_cases h1 : x ≤ 12
  · rw [twentyOddLoss_segment1 x (by linarith) h1];constructor <;> linarith
  by_cases h2 : x ≤ 27/2
  · rw [twentyOddLoss_segment2 x (by linarith) h2];norm_num
  by_cases h3 : x ≤ 14
  · rw [twentyOddLoss_segment3 x (by linarith) h3];constructor <;> linarith
  by_cases h4 : x ≤ 16
  · rw [twentyOddLoss_segment4 x (by linarith) h4];constructor <;> linarith
  by_cases h5 : x ≤ 24
  · rw [twentyOddLoss_segment5 x (by linarith) h5];constructor <;> linarith
  by_cases h6 : x ≤ 27
  · rw [twentyOddLoss_segment6 x (by linarith) h6];constructor <;> linarith
  rw [twentyOddLoss_segment7 x (by linarith)];norm_num

theorem twentyCombinedOddLoss_bounds (x : ℝ) :
    0 ≤ twentyCombinedOddLoss x ∧ twentyCombinedOddLoss x ≤ 40 :=by
  have hg :=twentyPrimeGain_bounds x
  have hl :=twentyOddLoss_bounds x
  constructor
  · by_cases hz : twentyPrimeGain x=0
    · simpa [twentyCombinedOddLoss,hz] using hl.1
    · have hw :=twentyPrimeGain_pos_window (lt_of_le_of_ne hg.1 (Ne.symm hz))
      rw [twentyCombinedOddLoss,twentyOddLoss_segment0 x (by linarith only [hw.2])]
      linarith only [hg.2]
  · unfold twentyCombinedOddLoss
    linarith only [hl.2,hg.1]

theorem twentyCombinedOddLoss_small {x : ℝ} (hx : x ≤ 1) :
    twentyCombinedOddLoss x=40 :=by
  rw [twentyCombinedOddLoss,twentyOddLoss_segment0 x (by linarith only [hx]),
    twentyPrimeGain_left (by linarith only [hx])]
  ring

theorem integral_twentyCombinedOddLoss :
    (∫ x in (0:ℝ)..27,twentyCombinedOddLoss x)=8795/12 :=by
  have hg0 : (∫ x in (0:ℝ)..1,twentyPrimeGain x)=0 :=by
    calc
      _ = ∫ x in (0:ℝ)..1,(0:ℝ) :=by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num)] at hx
        exact twentyPrimeGain_left (by linarith only [hx.2])
      _ = _ :=by simp
  have hg :=intervalIntegral.integral_add_adjacent_intervals (μ :=MeasureTheory.volume)
    (continuous_twentyPrimeGain.intervalIntegrable 0 1)
    (continuous_twentyPrimeGain.intervalIntegrable 1 27)
  rw [hg0,integral_twentyPrimeGain,zero_add] at hg
  unfold twentyCombinedOddLoss
  rw [intervalIntegral.integral_sub
    (continuous_twentyOddLoss.intervalIntegrable 0 27)
    (continuous_twentyPrimeGain.intervalIntegrable 0 27),integral_twentyOddLoss,← hg]
  norm_num

theorem integral_twentyCombinedOddLoss_one :
    (∫ x in (1:ℝ)..27,twentyCombinedOddLoss x)=8315/12 :=by
  have hfirst : (∫ x in (0:ℝ)..1,twentyCombinedOddLoss x)=40 :=by
    calc
      _ = ∫ x in (0:ℝ)..1,(40:ℝ) :=by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le (by norm_num)] at hx
        exact twentyCombinedOddLoss_small hx.2
      _ = _ :=by norm_num
  have hh :=intervalIntegral.integral_add_adjacent_intervals (μ :=MeasureTheory.volume)
    (continuous_twentyCombinedOddLoss.intervalIntegrable 0 1)
    (continuous_twentyCombinedOddLoss.intervalIntegrable 1 27)
  rw [hfirst,integral_twentyCombinedOddLoss] at hh
  linarith only [hh]

theorem twenty_combined_determinant_odd_profile {N p : ℕ} [Fact p.Prime]
    (hN : 0<N) (hp2 : p≠2) (hlarge : 1000000 ≤ p) (hHsq : 27*N<p^2)
    (hpH : p ≤ 27*N) (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(N:ℝ)*twentyCombinedOddLoss ((p:ℝ)/(N:ℝ)) ≤
      (padicValRat p (determinantRat twenty z N):ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  have hzP : (((p:ℚ)*z).den : ZMod p)≠0 :=
    (rational_residue_mul (by simp : ((p:ℚ).den : ZMod p)≠0) hz).1
  by_cases hg : twentyPrimeGain ((p:ℝ)/(N:ℝ))=0
  · simpa [twentyCombinedOddLoss,hg] using twenty_determinant_odd_profile hN hp2 hHsq hpH z hz
  have hgpos : 0<twentyPrimeGain ((p:ℝ)/(N:ℝ)) :=
    lt_of_le_of_ne (twentyPrimeGain_bounds _).1 (Ne.symm hg)
  have hw :=twentyPrimeGain_pos_window hgpos
  have hloR :=(lt_div_iff₀ hNR).mp hw.1
  have hhiR :=(div_lt_iff₀ hNR).mp hw.2
  have hlo : 22*N ≤ 3*p :=by
    have hh : (22:ℝ)*N ≤ 3*(p:ℝ) :=by linarith only [hloR]
    exact_mod_cast hh
  have hhi : 3*p ≤ 26*N :=by
    have hh : 3*(p:ℝ) ≤ (26:ℝ)*N :=by linarith only [hhiR]
    exact_mod_cast hh
  rw [twentyCombinedOddLoss,twentyOddLoss_segment0 _ (by linarith only [hw.2])]
  by_cases hmid : 3*p ≤ 24*N
  · have hmR : (p:ℝ)/(N:ℝ) ≤ 8 :=by
      apply (div_le_iff₀ hNR).mpr
      have hh : 3*(p:ℝ) ≤ 24*(N:ℝ) :=by exact_mod_cast hmid
      linarith only [hh]
    rw [twentyPrimeGain_ramp hw.1.le hmR]
    have hv : -((40*N-(3*p-22*N):ℕ):ℝ) ≤
        (padicValRat p (determinantRat twenty z N):ℝ) :=by
      exact_mod_cast twenty_early_sparse_valuation hN hlarge hlo hmid hHsq z hzP
    rw [Nat.cast_sub (by omega : 3*p-22*N ≤ 40*N),Nat.cast_sub hlo] at hv
    push_cast at hv
    have he : -(N:ℝ)*(40-0*((p:ℝ)/(N:ℝ))-(3*((p:ℝ)/(N:ℝ))-22))=
        -(40*(N:ℝ)-(3*(p:ℝ)-22*(N:ℝ))) :=by field_simp;ring
    rwa [he]
  · have hmR : 8 ≤ (p:ℝ)/(N:ℝ) :=by
      apply (le_div_iff₀ hNR).mpr
      have hh : 24*(N:ℝ) ≤ 3*(p:ℝ) :=by exact_mod_cast (show 24*N ≤ 3*p by omega)
      linarith only [hh]
    rw [twentyPrimeGain_fall hmR hw.2.le]
    have hv : -((40*N-(26*N-3*p):ℕ):ℝ) ≤
        (padicValRat p (determinantRat twenty z N):ℝ) :=by
      exact_mod_cast twenty_upper_sparse_valuation hN hlarge (by omega) hhi hHsq z hzP
    rw [Nat.cast_sub (by omega : 26*N-3*p ≤ 40*N),Nat.cast_sub hhi] at hv
    push_cast at hv
    have he : -(N:ℝ)*(40-0*((p:ℝ)/(N:ℝ))-(26-3*((p:ℝ)/(N:ℝ))))=
        -(40*(N:ℝ)-(26*(N:ℝ)-3*(p:ℝ))) :=by field_simp;ring
    rwa [he]

end
end CatalanMeasure.Parametric
