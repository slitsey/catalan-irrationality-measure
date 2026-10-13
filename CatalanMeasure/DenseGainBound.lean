module
public import CatalanMeasure.DenseDenominators
public import CatalanMeasure.SparseGainBound
@[expose] public section
namespace OAI.InternalCatalan
open Real CatalanMeasure
noncomputable section

theorem denseGain_pos_conditions {N p : ℕ} (hN : 1000000 ≤ N)
    (hgain : 0<densePrimeGain ((p:ℝ)/N)) :
    1000000 ≤ p ∧ 18*N ≤ p ∧ p ≤ 21*N ∧ 65*N<p^2 ∧
      2*Real.sqrt (H N)<(p:ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ) ≤ N :=by exact_mod_cast (show 1 ≤ N by omega)
  have hpR : (0:ℝ) ≤ p :=by positivity
  have hw :=densePrimeGain_pos_window hgain
  have hlo : 18*(N:ℝ)<(p:ℝ) :=(lt_div_iff₀ hNR).mp hw.1
  have hhi : (p:ℝ)<21*(N:ℝ) :=(div_lt_iff₀ hNR).mp hw.2
  have hsquare : (65:ℝ)*(N:ℝ)<(p:ℝ)^2 :=by nlinarith [sq_nonneg ((p:ℝ)-18*N)]
  have hNs : (1000000:ℝ) ≤ N :=by exact_mod_cast hN
  have hlarge : 1000000 ≤ p :=by
    have hh : (1000000:ℝ) ≤ p :=by linarith
    exact_mod_cast hh
  have hcut : (4:ℝ)*(H N:ℝ)<(p:ℝ)^2 :=by
    simp only [H,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [sq_nonneg ((p:ℝ)-18*N)]
  refine ⟨hlarge,by exact_mod_cast hlo.le,by exact_mod_cast hhi.le,
    by exact_mod_cast hsquare,?_⟩
  have hs :=Real.sq_sqrt (Nat.cast_nonneg (H N))
  have hs0 :=Real.sqrt_nonneg (H N)
  nlinarith

theorem denomExp_eq_96_of_denseGain {N p : ℕ} (hN : 1000000 ≤ N)
    (hg : 0<densePrimeGain ((p:ℝ)/N)) : denomExp N p=96*N :=by
  obtain ⟨hlarge,hlo,hhi,hsq,hcut⟩ :=denseGain_pos_conditions hN hg
  have hp2 : p≠2 :=by omega
  have hNR : (0:ℝ)<N :=by exact_mod_cast (show 0<N by omega)
  have hratio : (p:ℝ)/(N:ℝ) ≤ 25 :=by
    have hh : (p:ℝ) ≤ 21*(N:ℝ) :=by exact_mod_cast hhi
    rw [div_le_iff₀ hNR]
    nlinarith
  unfold denomExp
  rw [ite_eq_right hp2,ite_eq_right (not_le.mpr hcut),oddPrimeLoss_of_le_25 _ hratio]
  have he : (N:ℝ)*96=((96*N:ℕ):ℝ) :=by push_cast; ring
  rw [he,Nat.ceil_natCast]

theorem densePrimeGain_scaled_le_modes {N p : ℕ} (hN : 0<N) (hp : p ≤ 21*N) :
    (N:ℝ)*densePrimeGain ((p:ℝ)/N) ≤ ((min (4*N) (63*N-3*p):ℕ):ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  have hcut : 3*p ≤ 63*N :=by omega
  have hb :=densePrimeGain_bounds ((p:ℝ)/N)
  have hratio : (p:ℝ)/(N:ℝ) ≤ 21 :=by
    rw [div_le_iff₀ hNR]
    exact_mod_cast hp
  have hlinear :=hb.2.2
  rw [max_eq_left (by linarith : 0 ≤ 63-3*((p:ℝ)/N))] at hlinear
  have h4 :=mul_le_mul_of_nonneg_left hb.2.1 hNR.le
  have hr :=mul_le_mul_of_nonneg_left hlinear hNR.le
  have he : (N:ℝ)*(63-3*((p:ℝ)/N))=63*N-3*p :=by field_simp
  rw [he] at hr
  rw [Nat.cast_min,Nat.cast_sub hcut]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  exact le_min (by nlinarith) hr

theorem denseDenomExp_gain_le {N p : ℕ} (hN : 1000000 ≤ N) :
    (denseDenomExp N p:ℝ) ≤ (denomExp N p:ℝ)-(N:ℝ)*densePrimeGain ((p:ℝ)/N) :=by
  have hg0 :=(densePrimeGain_bounds ((p:ℝ)/N)).1
  by_cases hz : densePrimeGain ((p:ℝ)/N)=0
  · rw [hz,mul_zero,sub_zero]
    exact_mod_cast denseDenomExp_le N p
  have hpos : 0<densePrimeGain ((p:ℝ)/N) :=lt_of_le_of_ne hg0 (Ne.symm hz)
  obtain ⟨hlarge,hlo,hhi,hsq,hcut⟩ :=denseGain_pos_conditions hN hpos
  have hN0 : 0<N :=by omega
  have he :=denomExp_eq_96_of_denseGain hN hpos
  by_cases hearly : 3*p ≤ 58*N
  · have hw : densePrimeWindow N p :=⟨hlarge,hlo,hearly,hsq⟩
    have hlower : 54*N ≤ 3*p :=by omega
    have hsave : 3*p-54*N ≤ 96*N :=by omega
    have hNR : (0:ℝ)<N :=by exact_mod_cast hN0
    have hl : (18:ℝ) ≤ (p:ℝ)/N :=by
      rw [le_div_iff₀ hNR]
      exact_mod_cast hlo
    have hh : (p:ℝ)/N ≤ 58/3 :=by
      rw [div_le_iff₀ hNR]
      have ht : 3*(p:ℝ) ≤ 58*(N:ℝ) :=by exact_mod_cast hearly
      linarith
    have hb : (denseDenomExp N p:ℝ) ≤ ((96*N-(3*p-54*N):ℕ):ℝ) :=by
      unfold denseDenomExp
      rw [ite_eq_left hw]
      exact_mod_cast Nat.min_le_right (sparseDenomExp N p) (96*N-(3*p-54*N))
    rw [he,densePrimeGain_ramp hl hh]
    rw [Nat.cast_sub hsave,Nat.cast_sub hlower] at hb
    simp only [Nat.cast_mul,Nat.cast_ofNat] at hb ⊢
    have hc : (N:ℝ)*(3*((p:ℝ)/N)-54)=3*p-54*N :=by field_simp
    rw [hc]
    exact hb
  · have hw : sparsePrimeWindow N p :=⟨hlarge,by omega,hhi,hsq⟩
    have hb :=densePrimeGain_scaled_le_modes hN0 hhi
    have hmin : min (4*N) (63*N-3*p) ≤ 96*N :=by
      have :=Nat.min_le_left (4*N) (63*N-3*p)
      omega
    have hexp : sparseDenomExp N p=96*N-min (4*N) (63*N-3*p) :=by
      unfold sparseDenomExp
      rw [ite_eq_left hw,he,Nat.min_eq_right (Nat.sub_le _ _)]
    have hle : (denseDenomExp N p:ℝ) ≤ (sparseDenomExp N p:ℝ) :=by
      exact_mod_cast denseDenomExp_le_sparse N p
    rw [hexp,Nat.cast_sub hmin] at hle
    rw [he]
    linarith

end
end OAI.InternalCatalan
