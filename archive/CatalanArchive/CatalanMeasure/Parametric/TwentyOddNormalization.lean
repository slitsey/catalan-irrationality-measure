module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyOddValuation
public import CatalanArchive.CatalanMeasure.Parametric.TwentyOddLoss
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

theorem twentyOddLossNat_cast {N p : ℕ} (hN : 0<N) :
    (twentyOddLossNat N p:ℝ)=(N:ℝ)*twentyOddLoss ((p:ℝ)/(N:ℝ)) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  have hratio (k : ℕ) : ((p:ℝ)/(N:ℝ) ≤ (k:ℝ)) ↔ p ≤ k*N :=by
    rw [div_le_iff₀ hNR]
    norm_cast
  have hhalfR : ((p:ℝ)/(N:ℝ) ≤ (27/2:ℝ)) ↔ 2*p ≤ 27*N :=by
    rw [div_le_iff₀ hNR]
    constructor
    · intro hh
      have hc : 2*(p:ℝ) ≤ 27*(N:ℝ) :=by linarith only [hh]
      exact_mod_cast hc
    · intro hh
      have hc : 2*(p:ℝ) ≤ 27*(N:ℝ) :=by exact_mod_cast hh
      linarith only [hc]
  have haff (c m : ℕ) (hd : m*p ≤ c*N) :
      ((c*N-m*p:ℕ):ℝ)=(N:ℝ)*((c:ℝ)-(m:ℝ)*((p:ℝ)/(N:ℝ))) :=by
    rw [Nat.cast_sub hd]
    push_cast
    field_simp <;> ring
  unfold twentyOddLossNat
  split_ifs with h10 h12 hhalf h14 h16 h24 h27
  · rw [twentyOddLoss_segment0 ((p:ℝ)/(N:ℝ)) ((hratio 10).mpr h10)]
    push_cast; ring
  · rw [twentyOddLoss_segment1 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 10).not.mpr h10;linarith only [hh]) ((hratio 12).mpr h12)]
    exact haff 60 2 (by omega)
  · rw [twentyOddLoss_segment2 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 12).not.mpr h12;linarith only [hh]) ((hhalfR).mpr hhalf)]
    push_cast; ring
  · rw [twentyOddLoss_segment3 ((p:ℝ)/(N:ℝ)) (by have hh :=(hhalfR).not.mpr hhalf;linarith only [hh]) ((hratio 14).mpr h14)]
    exact haff 63 2 (by omega)
  · rw [twentyOddLoss_segment4 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 14).not.mpr h14;linarith only [hh]) ((hratio 16).mpr h16)]
    exact haff 91 4 (by omega)
  · rw [twentyOddLoss_segment5 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 16).not.mpr h16;linarith only [hh]) ((hratio 24).mpr h24)]
    exact haff 75 3 (by omega)
  · rw [twentyOddLoss_segment6 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 24).not.mpr h24;linarith only [hh]) ((hratio 27).mpr h27)]
    simpa only [Nat.cast_ofNat,Nat.cast_one,one_mul] using haff 27 1 (by omega)
  · rw [twentyOddLoss_segment7 ((p:ℝ)/(N:ℝ)) (by have hh :=(hratio 27).not.mpr h27;linarith only [hh])]
    push_cast; ring

theorem twenty_determinant_odd_profile {N p : ℕ} [Fact p.Prime]
    (hN : 0<N) (hp2 : p≠2) (hHsq : 27*N<p^2) (hpH : p ≤ 27*N)
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(N:ℝ)*twentyOddLoss ((p:ℝ)/(N:ℝ)) ≤ (padicValRat p (determinantRat twenty z N):ℝ) :=by
  have hh : -(twentyOddLossNat N p:ℝ) ≤ (padicValRat p (determinantRat twenty z N):ℝ) :=by
    exact_mod_cast twenty_determinant_odd_valuation hN hp2 hHsq hpH z hz
  rw [twentyOddLossNat_cast hN] at hh
  simpa only [neg_mul] using hh

end
end CatalanMeasure.Parametric
