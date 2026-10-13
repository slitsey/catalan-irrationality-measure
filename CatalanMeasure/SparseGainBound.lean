module
public import CatalanMeasure.SparseDenominators
@[expose] public section
namespace OAI.InternalCatalan
open Real CatalanMeasure
noncomputable section

theorem sparseGain_pos_conditions {N p : ℕ} (hN : 1000000 ≤ N)
    (hgain : 0<sparsePrimeGain ((p:ℝ)/N)) :
    sparsePrimeWindow N p ∧ 2*Real.sqrt (H N)<(p:ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ) ≤ N :=by exact_mod_cast (show 1 ≤ N by omega)
  have hpR : (0:ℝ) ≤ p :=by positivity
  have hw :=sparsePrimeGain_pos_window hgain
  have hlo : 58*(N:ℝ)<3*(p:ℝ) :=by
    have hh :=(lt_div_iff₀ hNR).mp hw.1
    linarith
  have hhi : (p:ℝ)<21*(N:ℝ) :=(div_lt_iff₀ hNR).mp hw.2
  have hp19 : 19*(N:ℝ)<(p:ℝ) :=by linarith
  have hsquare : (65:ℝ)*(N:ℝ)<(p:ℝ)^2 :=by nlinarith [sq_nonneg ((p:ℝ)-19*N)]
  have hNs : (1000000:ℝ) ≤ N :=by exact_mod_cast hN
  have hlarge : 1000000 ≤ p :=by
    have hh : (1000000:ℝ) ≤ p :=by linarith
    exact_mod_cast hh
  have hcut : (4:ℝ)*(H N:ℝ)<(p:ℝ)^2 :=by
    simp only [H,Nat.cast_mul,Nat.cast_ofNat]
    nlinarith [sq_nonneg ((p:ℝ)-19*N)]
  refine ⟨⟨hlarge,?_,?_,?_⟩,?_⟩
  · exact_mod_cast hlo.le
  · exact_mod_cast hhi.le
  · exact_mod_cast hsquare
  · have hs :=Real.sq_sqrt (Nat.cast_nonneg (H N))
    have hs0 :=Real.sqrt_nonneg (H N)
    nlinarith

theorem denomExp_eq_96_of_sparseWindow {N p : ℕ} (hN : 0<N) (hw : sparsePrimeWindow N p)
    (hlarge : 2*Real.sqrt (H N)<(p:ℝ)) : denomExp N p=96*N :=by
  have hp2 : p≠2 :=by have :=hw.1; omega
  have hratio : (p:ℝ)/(N:ℝ) ≤ 25 :=by
    have hNR : (0:ℝ)<N :=by exact_mod_cast hN
    have hhi : (p:ℝ) ≤ 21*(N:ℝ) :=by exact_mod_cast hw.2.2.1
    rw [div_le_iff₀ hNR]
    nlinarith
  unfold denomExp
  rw [ite_eq_right hp2,ite_eq_right (not_le.mpr hlarge),oddPrimeLoss_of_le_25 _ hratio]
  have he : (N:ℝ)*96=((96*N:ℕ):ℝ) :=by push_cast; ring
  rw [he,Nat.ceil_natCast]

theorem sparsePrimeGain_scaled_le_modes {N p : ℕ} (hN : 0<N) (hp : p ≤ 21*N) :
    (N:ℝ)*sparsePrimeGain ((p:ℝ)/N) ≤ ((min (4*N) (63*N-3*p):ℕ):ℝ) :=by
  have hNR : (0:ℝ)<N :=by exact_mod_cast hN
  have hcut : 3*p ≤ 63*N :=by omega
  have hb :=sparsePrimeGain_bounds ((p:ℝ)/N)
  have hratio : (p:ℝ)/(N:ℝ) ≤ 21 :=by
    rw [div_le_iff₀ hNR]
    exact_mod_cast hp
  have hlinear :=hb.2.2
  rw [max_eq_left (by linarith : 0 ≤ 63-3*((p:ℝ)/N))] at hlinear
  have h4 :=mul_le_mul_of_nonneg_left hb.2.1 hNR.le
  have hr :=mul_le_mul_of_nonneg_left hlinear hNR.le
  have he : (N:ℝ)*(63-3*((p:ℝ)/N))=63*N-3*p :=by
    field_simp
  rw [he] at hr
  rw [Nat.cast_min,Nat.cast_sub hcut]
  simp only [Nat.cast_mul,Nat.cast_ofNat]
  exact le_min (by nlinarith) hr

theorem sparseDenomExp_gain_le {N p : ℕ} (hN : 1000000 ≤ N) :
    (sparseDenomExp N p:ℝ) ≤ (denomExp N p:ℝ)-(N:ℝ)*sparsePrimeGain ((p:ℝ)/N) :=by
  have hg0 :=(sparsePrimeGain_bounds ((p:ℝ)/N)).1
  by_cases hz : sparsePrimeGain ((p:ℝ)/N)=0
  · rw [hz,mul_zero,sub_zero]
    exact_mod_cast sparseDenomExp_le N p
  have hpos : 0<sparsePrimeGain ((p:ℝ)/N) :=lt_of_le_of_ne hg0 (Ne.symm hz)
  have hw :=sparseGain_pos_conditions hN hpos
  have hN0 : 0<N :=by omega
  have he :=denomExp_eq_96_of_sparseWindow hN0 hw.1 hw.2
  have hb :=sparsePrimeGain_scaled_le_modes hN0 hw.1.2.2.1
  have hmin : min (4*N) (63*N-3*p) ≤ 96*N :=by
    have :=Nat.min_le_left (4*N) (63*N-3*p)
    omega
  unfold sparseDenomExp
  rw [ite_eq_left hw.1,he,Nat.min_eq_right (Nat.sub_le _ _),Nat.cast_sub hmin]
  linarith

end
end OAI.InternalCatalan
