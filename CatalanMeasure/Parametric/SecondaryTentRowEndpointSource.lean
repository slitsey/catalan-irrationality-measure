module
public import CatalanMeasure.Parametric.SecondaryTentRowSourceJunction
public import Mathlib.Algebra.Polynomial.Div
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

/-- The source's degree≤5 part after removing the single z-dz channel. -/
def secondaryTentRowTRemainder {K : Type*} [CommRing K] (c : Fin 7 → K) : K[X] :=
  ∑ k : Fin 6, C (![ -c 6, -c 0+c 6, c 0-c 1+c 3-c 4-c 6,
    -c 0+c 1-c 2+c 4-c 5+c 6, c 0-c 1+c 2+c 3+c 5, c 1-c 2] k) * X^k.val

theorem secondaryTent_row_t_remainder_degree {K : Type*} [CommRing K]
    (c : Fin 7 → K) : (secondaryTentRowTRemainder c).natDegree≤5 := by
  unfold secondaryTentRowTRemainder
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ k.val).trans (by have h := k.isLt; omega)

/-- Both natural source numerators share exactly the same infinity
combination: the coefficient of z^6 is the z-dz differential coefficient. -/
theorem secondaryTent_row_t_top_split {K : Type*} [CommRing K]
    (c : Fin 7 → K) :
    secondaryTentRowTNumerator c = C (c 2)*X^6+secondaryTentRowTRemainder c := by
  simp [secondaryTentRowTNumerator, secondaryTentRowTRemainder, Fin.sum_univ_succ,
    map_add, map_sub, map_neg]
  ring

theorem secondaryTent_row_t_ordinary_zero_factor {K : Type*} [CommRing K]
    (c : Fin 7 → K) (hb : c 6=0) : X ∣ secondaryTentRowTNumerator c := by
  refine ⟨(X^2+1)*(X-1)*(C (c 0)+C (c 1)*X+C (c 2)*X^2) +
    C (c 3)*X*(X^2+1)+C (c 4)*X*(X-1)+C (c 5)*X^2*(X-1),?_⟩
  simp only [secondaryTentRowTNumerator,hb,map_zero,mul_zero,zero_mul,add_zero]
  ring

/-- The ordinary source packet pays z^(2p) before any additional lower
endpoint conditions are imposed. -/
theorem secondaryTent_row_ordinary_packet_zero_factor {K : Type*} [CommRing K]
    {ι : Type*} [Fintype ι] (p n : ℕ) (c : ι → (Fin 7 → K)) (I : ι → K[X])
    (hb : ∀ i, c i 6=0 ∨ I i=0) :
    X^(2*p) ∣ (8*X)^p * ∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTNumerator (c i))^p := by
  have hs : X^p ∣ ∑ i, secondaryTentRowInput n (I i)*(secondaryTentRowTNumerator (c i))^p := by
    apply Finset.dvd_sum
    intro i hi
    rcases hb i with hb₁ | hb₂
    · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (secondaryTent_row_t_ordinary_zero_factor (c i) hb₁) p) _
    · simp [hb₂,secondaryTentRowInput,secondaryTentRowHom]
  have hx : X^p ∣ (8*X : K[X])^p := by rw [mul_pow]; exact dvd_mul_left _ _
  have hh := mul_dvd_mul hx hs
  simpa only [← pow_add, show p+p=2*p by omega] using hh

/-- A small boundary input pays its exact lower endpoint factor, while
all remaining channels have the ordinary z factor. -/
theorem secondaryTent_row_boundary_packet_zero_factor {K : Type*} [Field K]
    (h2 : (2:K)≠0) {ι : Type*} [Fintype ι] (b : ι) (p m : ℕ)
    (c : ι → (Fin 7 → K)) (I : ι → K[X]) (hm : m≤p-1)
    (hI : (I b).natDegree≤m) (hb : ∀ i, i≠b → c i 6=0) :
    X^(p+(p-1-m)) ∣ (8*X)^p * ∑ i, secondaryTentRowInput (p-1) (I i)*(secondaryTentRowTNumerator (c i))^p := by
  classical
  have hs : X^(p-1-m) ∣ ∑ i, secondaryTentRowInput (p-1) (I i)*(secondaryTentRowTNumerator (c i))^p := by
    apply Finset.dvd_sum
    intro i hi
    by_cases hib : i=b
    · subst i
      exact dvd_mul_of_dvd_left (secondaryTent_rowInput_lower_factor h2 m (p-1) (I b) hm hI) _
    · have ht := pow_dvd_pow_of_dvd (secondaryTent_row_t_ordinary_zero_factor (c i) (hb i hib)) p
      exact dvd_mul_of_dvd_right ((pow_dvd_pow (X : K[X]) (by omega : p-1-m≤p)).trans ht) _
  have hx : X^p ∣ (8*X : K[X])^p := by rw [mul_pow]; exact dvd_mul_left _ _
  simpa only [← pow_add] using mul_dvd_mul hx hs

/-- The negative-side Taylor flag is literally one block of coefficients
of K; no rational Taylor series or denominator units are needed. -/
theorem secondaryTent_row_lower_coefficients_flag {K : Type*} [CommRing K]
    (s t : ℕ) (F : K[X]) (hs : X^s ∣ F)
    (ht : ∀ j : Fin t, F.coeff (s+j.val)=0) : X^(s+t) ∣ F := by
  apply X_pow_dvd_iff.mpr
  intro k hk
  by_cases hks : k<s
  · exact X_pow_dvd_iff.mp hs k hks
  · have hsk : s≤k := Nat.le_of_not_gt hks
    have hkt : k-s<t := by omega
    simpa only [Nat.add_sub_of_le hsk] using ht ⟨k-s,hkt⟩

end
end CatalanMeasure.Parametric
