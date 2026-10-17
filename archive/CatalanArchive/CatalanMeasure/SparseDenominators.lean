module
public import CatalanMeasure.Denominators
public import CatalanArchive.CatalanMeasure.Parametric.BaselineBridge
public import CatalanArchive.CatalanMeasure.SparseGainPNT
@[expose] public section
namespace OAI.InternalCatalan
open Filter Real CatalanMeasure
open scoped Topology BigOperators
noncomputable section

def sparsePrimeWindow (N p : ℕ) : Prop :=
  1000000 ≤ p ∧ 58*N ≤ 3*p ∧ p ≤ 21*N ∧ 65*N<p^2

instance (N p : ℕ) : Decidable (sparsePrimeWindow N p) :=by
  unfold sparsePrimeWindow
  infer_instance

def sparseDenomExp (N p : ℕ) : ℕ :=
  if sparsePrimeWindow N p then min (denomExp N p) (96*N-min (4*N) (63*N-3*p))
    else denomExp N p

def sparseDenomBound (N : ℕ) : ℕ :=∏ p ∈ measurePrimes N,p^sparseDenomExp N p

theorem sparseDenomExp_le (N p : ℕ) : sparseDenomExp N p ≤ denomExp N p :=by
  unfold sparseDenomExp
  split_ifs
  · exact Nat.min_le_left _ _
  · rfl

theorem sparseDenomBound_ne_zero (N : ℕ) : sparseDenomBound N≠0 :=by
  unfold sparseDenomBound
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Finset.mem_filter.mp hp).2.ne_zero

theorem padicValRat_determinantRat_sparse_natCast_lower {N : ℕ} (hN : 0<N) (i : ℕ)
    {p : ℕ} [hp : Fact p.Prime] (hd : determinantRat (i:ℚ) N≠0) :
    -(sparseDenomExp N p:ℤ) ≤ padicValRat p (determinantRat (i:ℚ) N) :=by
  have hold :=padicValRat_determinantRat_natCast_lower (ℓ:=p) hN i hd
  unfold sparseDenomExp
  split_ifs with hw
  · have hpz : (((p:ℚ)*(i:ℚ)).den : ZMod p)≠0 :=by
      simpa only [Nat.cast_mul] using natCast_den_zmod_ne_zero (p*i) p
    have hnew :=CatalanMeasure.Parametric.determinantRat_sparse_prime_valuation
      hN hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 (i:ℚ) hpz
    by_cases hle : denomExp N p ≤ 96*N-min (4*N) (63*N-3*p)
    · rw [Nat.min_eq_left hle]
      exact hold
    · rw [Nat.min_eq_right (by omega)]
      exact hnew
  · exact hold

theorem den_dvd_sparseDenomBound {N : ℕ} (hN : 0<N) (i : ℕ)
    (hd : determinantRat (i:ℚ) N≠0) : (determinantRat (i:ℚ) N).den ∣ sparseDenomBound N :=by
  have hB :=sparseDenomBound_ne_zero N
  rw [← Nat.factorization_le_iff_dvd (Rat.den_pos _).ne' hB,Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · haveI : Fact p.Prime :=⟨hp⟩
    rw [Nat.factorization_def _ hp]
    by_cases hS : p∈measurePrimes N
    · have h1 :=padicValNat_den_le_of_padicValRat (padicValRat_determinantRat_sparse_natCast_lower (p:=p) hN i hd)
      have h2 : sparseDenomExp N p ≤ (sparseDenomBound N).factorization p :=by
        apply (hp.pow_dvd_iff_le_factorization hB).mp
        unfold sparseDenomBound
        exact Finset.dvd_prod_of_mem (fun p =>p^sparseDenomExp N p) hS
      exact h1.trans h2
    · have hH : H N<p :=by
        by_contra hh
        exact hS (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp.pos,by omega⟩,hp⟩)
      have hp2 : p≠2 :=by unfold H at hH; omega
      have hv :=determinantRat_above_degrees_local_integral hp2 hN hH.le (i:ℚ)
        (natCast_den_zmod_ne_zero i p)
      have h0 :=padicValNat_den_le_of_padicValRat (e:=0) (by simpa using hv)
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

theorem exists_int_sparseDenomBound_mul {N : ℕ} (hN : 0<N) (i : ℕ) :
    ∃ m : ℤ,(sparseDenomBound N:ℚ)*determinantRat (i:ℚ) N=m :=by
  by_cases hd : determinantRat (i:ℚ) N=0
  · exact ⟨0,by rw [hd,mul_zero,Int.cast_zero]⟩
  obtain ⟨c,hc⟩ :=den_dvd_sparseDenomBound hN i hd
  refine ⟨(c:ℤ)*(determinantRat (i:ℚ) N).num,?_⟩
  rw [hc]
  push_cast
  have hh :=Rat.mul_den_eq_num (determinantRat (i:ℚ) N)
  linear_combination (c:ℚ)*hh

theorem log_sparseDenomBound_eq (N : ℕ) :
    Real.log (sparseDenomBound N)=∑ p ∈ measurePrimes N,(sparseDenomExp N p:ℝ)*Real.log p :=by
  unfold sparseDenomBound
  rw [Nat.cast_prod,Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.cast_pow,Real.log_pow]
  · intro p hp
    exact_mod_cast pow_ne_zero (sparseDenomExp N p) (Finset.mem_filter.mp hp).2.ne_zero

end
end OAI.InternalCatalan
