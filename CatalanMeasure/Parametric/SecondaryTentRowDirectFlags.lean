module
public import CatalanMeasure.Parametric.SecondaryTentRowDivisor
public import CatalanMeasure.Parametric.SecondaryTentRowFlags
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

theorem secondaryTent_row_bounded_monic_factor {K : Type*} [Field K]
    (A F : K[X]) (m : ℕ) (hA : A.Monic) (hd : A ∣ F)
    (hF : F.natDegree ≤ A.natDegree+m) :
    ∃ G : K[X], F=A*G ∧ G.natDegree≤m := by
  refine ⟨F /ₘ A,?_,?_⟩
  · have h := modByMonic_add_div F A
    rw [(modByMonic_eq_zero_iff_dvd hA).mpr hd,zero_add] at h
    exact h.symm
  · rw [natDegree_divByMonic F hA]
    omega

/-- The two x=0 flags supply the quadratic factor of the direct natural
numerator. -/
theorem secondaryTent_row_natural_quadratic_flag {K : Type*} [Field K]
    (h2 : (2:K)≠0) (p a m : ℕ) (U V : K[X])
    (hU : U.natDegree≤a+m) (hV : V.natDegree≤a+m)
    (hdU : X^a ∣ U) (hdV : X^a ∣ V) :
    (X^2+1)^a ∣ secondaryTentRowNaturalNumerator p (a+m) U V := by
  obtain ⟨u,hu,hdu⟩ := secondaryTent_row_bounded_monic_factor (X^a) U m (monic_X.pow a)
    hdU (by simpa using hU)
  obtain ⟨v,hv,hdv⟩ := secondaryTent_row_bounded_monic_factor (X^a) V m (monic_X.pow a)
    hdV (by simpa using hV)
  refine ⟨(X-1)^p*secondaryTentRowInput m u+(X+1)^p*secondaryTentRowInput m v,?_⟩
  unfold secondaryTentRowNaturalNumerator
  rw [hu,hv,secondaryTent_rowInput_X_pow_mul h2 a m u hdu,
    secondaryTent_rowInput_X_pow_mul h2 a m v hdv]
  ring

/-- The literal U/V divisibility flags pay both branch factors of K.
The proof extracts bounded polynomial quotients and uses the exact
ramified substitution factorization. -/
theorem secondaryTent_row_natural_branch_flags {K : Type*} [Field K]
    (h2 : (2:K)≠0) (N n m p : ℕ) (U V : K[X]) (hp : p=2*n+1)
    (hU : U.natDegree≤N+n+m) (hV : V.natDegree≤N+n+m)
    (hu₁ : (X-1)^N ∣ U) (hu₂ : (X+1)^n ∣ U) (hv₁ : (X-1)^(N+n) ∣ V) :
    (X-1)^(p+2*N-1)*(X+1)^(p-1) ∣ secondaryTentRowNaturalNumerator p (N+n+m) U V := by
  have hm : (X-1 : K[X]).Monic := by simpa using monic_X_sub_C (1:K)
  have hp₁ : (X+1 : K[X]).Monic := by simpa using monic_X_add_C (1:K)
  have ha : ((X-1 : K[X])^N*(X+1)^n).Monic := (hm.pow N).mul (hp₁.pow n)
  have had : ((X-1 : K[X])^N*(X+1)^n).natDegree=N+n := by
    rw [natDegree_mul (hm.pow N).ne_zero (hp₁.pow n).ne_zero]
    simp [natDegree_pow, show (X-1 : K[X]).natDegree=1 by simpa using natDegree_X_sub_C (1:K),
      show (X+1 : K[X]).natDegree=1 by simpa using natDegree_X_add_C (1:K)]
  have hdiv : (X-1)^N*(X+1)^n ∣ U := by
    simpa [secondaryTentRowDivisor] using secondaryTent_row_divisor_dvd h2 0 0 N n U
      (by simp) (by simp) hu₁ hu₂
  obtain ⟨u,hu,hdu⟩ := secondaryTent_row_bounded_monic_factor _ U m ha hdiv (by simpa [had] using hU)
  obtain ⟨v,hv,hdv⟩ := secondaryTent_row_bounded_monic_factor ((X-1)^(N+n)) V m
    (hm.pow (N+n)) hv₁ (by simpa [natDegree_pow,
      show (X-1 : K[X]).natDegree=1 by simpa using natDegree_X_sub_C (1:K)] using hV)
  refine ⟨(X-1)*secondaryTentRowInput m u+(X+1)*secondaryTentRowInput m v,?_⟩
  unfold secondaryTentRowNaturalNumerator
  rw [hu,hv,mul_assoc]
  exact secondaryTent_row_UV_flag_factorization h2 N n m p u v hp hdu hdv

/-- Once the lower endpoint flag is supplied, every literal natural flag
has been assembled into the single actual-row divisor. -/
theorem secondaryTent_row_natural_total_flags {K : Type*} [Field K]
    (h2 : (2:K)≠0) (N n p a l d mq mb : ℕ) (U V : K[X])
    (hp : p=2*n+1) (hdq : d=a+mq) (hdb : d=N+n+mb)
    (hU : U.natDegree≤d) (hV : V.natDegree≤d)
    (hu₀ : X^a ∣ U) (hv₀ : X^a ∣ V)
    (hu₁ : (X-1)^N ∣ U) (hu₂ : (X+1)^n ∣ U) (hv₁ : (X-1)^(N+n) ∣ V)
    (hz : X^l ∣ secondaryTentRowNaturalNumerator p d U V) :
    secondaryTentRowDivisor l a (p+2*N-1) (p-1) ∣ secondaryTentRowNaturalNumerator p d U V := by
  have hq := secondaryTent_row_natural_quadratic_flag h2 p a mq U V
    (by simpa [← hdq] using hU) (by simpa [← hdq] using hV) hu₀ hv₀
  have hb := secondaryTent_row_natural_branch_flags h2 N n mb p U V hp
    (by simpa [← hdb] using hU) (by simpa [← hdb] using hV) hu₁ hu₂ hv₁
  rw [← hdq] at hq
  rw [← hdb] at hb
  exact secondaryTent_row_divisor_dvd h2 l a (p+2*N-1) (p-1) _ hz hq
    ((dvd_mul_right _ _).trans hb) ((dvd_mul_left _ _).trans hb)

end
end CatalanMeasure.Parametric
