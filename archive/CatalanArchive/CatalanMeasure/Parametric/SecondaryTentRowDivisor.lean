module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentRowNaturalPacket
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.Coprime.Lemmas
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

def secondaryTentRowDivisor {K : Type*} [CommRing K] (l a b c : ℕ) : K[X] :=
  X^l * (X^2+1)^a * (X-1)^b * (X+1)^c

theorem secondaryTent_row_divisor_monic {K : Type*} [CommRing K]
    (l a b c : ℕ) : (secondaryTentRowDivisor (K := K) l a b c).Monic := by
  unfold secondaryTentRowDivisor
  exact (((monic_X.pow l).mul ((by simpa using
    (monic_X_pow_add_C (1:K) (by decide : 2≠0)) : (X^2+1 : K[X]).Monic).pow a)).mul
      ((by simpa using monic_X_sub_C (1:K) : (X-1 : K[X]).Monic).pow b)).mul
        ((by simpa using monic_X_add_C (1:K) : (X+1 : K[X]).Monic).pow c)

theorem secondaryTent_row_divisor_degree {K : Type*} [Field K]
    (l a b c : ℕ) : (secondaryTentRowDivisor (K := K) l a b c).natDegree=l+2*a+b+c := by
  have hq : (X^2+1 : K[X]).Monic := by
    simpa using monic_X_pow_add_C (1:K) (by decide : 2≠0)
  have hm : (X-1 : K[X]).Monic := by simpa using monic_X_sub_C (1:K)
  have hp : (X+1 : K[X]).Monic := by simpa using monic_X_add_C (1:K)
  unfold secondaryTentRowDivisor
  rw [natDegree_mul (((monic_X.pow l).mul (hq.pow a)).mul (hm.pow b)).ne_zero (hp.pow c).ne_zero,
    natDegree_mul ((monic_X.pow l).mul (hq.pow a)).ne_zero (hm.pow b).ne_zero,
    natDegree_mul (monic_X.pow l).ne_zero (hq.pow a).ne_zero]
  simp only [natDegree_pow, natDegree_X, mul_one]
  have hqd : (X^2+1 : K[X]).natDegree=2 := by
    simpa using natDegree_X_pow_add_C (n := 2) (r := (1:K))
  have hmd : (X-1 : K[X]).natDegree=1 := by simpa using natDegree_X_sub_C (1:K)
  have hpd : (X+1 : K[X]).natDegree=1 := by simpa using natDegree_X_add_C (1:K)
  rw [hqd,hmd,hpd]
  omega

/-- All four elementary pole factors are pairwise coprime outside
characteristic two; no root extension for the quadratic is required. -/
theorem secondaryTent_row_divisor_dvd {K : Type*} [Field K] (h2 : (2:K)≠0)
    (l a b c : ℕ) (F : K[X]) (hz : X^l ∣ F) (hq : (X^2+1)^a ∣ F)
    (hm : (X-1)^b ∣ F) (hp : (X+1)^c ∣ F) :
    secondaryTentRowDivisor l a b c ∣ F := by
  have hinv : (C (2⁻¹:K) : K[X])*2=1 := by
    rw [← C_ofNat, ← C_mul, inv_mul_cancel₀ h2, C_1]
  have hzq : IsCoprime (X : K[X]) (X^2+1) := ⟨-X,1,by ring⟩
  have hzm : IsCoprime (X : K[X]) (X-1) := ⟨1,-1,by ring⟩
  have hzp : IsCoprime (X : K[X]) (X+1) := ⟨-1,1,by ring⟩
  have hqmp : IsCoprime (X^2+1 : K[X]) ((X-1)*(X+1)) := by
    refine ⟨C (2⁻¹:K),-C (2⁻¹:K),?_⟩
    calc
      _ = C (2⁻¹:K)*2 := by ring
      _ = 1 := hinv
  have hmp : IsCoprime (X-1 : K[X]) (X+1) := by
    refine ⟨-C (2⁻¹:K),C (2⁻¹:K),?_⟩
    calc
      _ = C (2⁻¹:K)*2 := by ring
      _ = 1 := hinv
  have h₁ : X^l*(X^2+1)^a ∣ F := hzq.pow.mul_dvd hz hq
  have h₂ : X^l*(X^2+1)^a*(X-1)^b ∣ F :=
    (hzm.pow.mul_left hqmp.of_mul_right_left.pow).mul_dvd h₁ hm
  exact ((hzp.pow.mul_left hqmp.of_mul_right_right.pow).mul_left hmp.pow).mul_dvd h₂ hp

def secondaryTentRowTotalDivisor {K : Type*} [CommRing K] (N p a : ℕ) : K[X] :=
  secondaryTentRowDivisor (24*N-2*p) a (p+2*N-1) (p-1)

def secondaryTentRowQuotientLinear {K : Type*} [Field K] (N p a : ℕ) :
    K[X] →ₗ[K] K[X] := Polynomial.divByMonicHom (secondaryTentRowTotalDivisor N p a)

def secondaryTentRowCoefficients {K : Type*} [Field K] (n : ℕ) :
    K[X] →ₗ[K] (Fin n → K) where
  toFun F i := F.coeff i.val
  map_add' F G := by ext i; simp
  map_smul' t F := by ext i; simp

/-- The actual row coefficient map: the quotient is z^(2N) times the
Laurent row, and coefficient i corresponds to physical ell=i-2N. -/
def secondaryTentRowQuotientCoefficients {K : Type*} [Field K] (N p a : ℕ) :
    K[X] →ₗ[K] (Fin (20*N) → K) :=
  (secondaryTentRowCoefficients (20*N)).comp (secondaryTentRowQuotientLinear N p a)

theorem secondaryTent_row_total_divisor_degree {K : Type*} [Field K]
    (N p a g : ℕ) (hp : 0<p) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N) :
    (secondaryTentRowTotalDivisor (K := K) N p a).natDegree+28*N+2=10*p := by
  unfold secondaryTentRowTotalDivisor
  rw [secondaryTent_row_divisor_degree]
  omega

theorem secondaryTent_row_quotient_degree {K : Type*} [Field K]
    (N p a g : ℕ) (F : K[X]) (hN : 0<N) (hp : 0<p) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N) (hF : F.natDegree+8*N+3≤10*p) :
    (secondaryTentRowQuotientLinear N p a F).natDegree<20*N := by
  change (F /ₘ secondaryTentRowTotalDivisor N p a).natDegree<20*N
  have hmo : (secondaryTentRowTotalDivisor (K := K) N p a).Monic :=
    secondaryTent_row_divisor_monic _ _ _ _
  rw [natDegree_divByMonic F hmo]
  have hdeg := secondaryTent_row_total_divisor_degree (K := K) N p a g hp hpN hag hgp
  omega

/-- Truncating to the actual20N coefficients loses nothing on a divisible
packet satisfying the proved upper cap. -/
theorem secondaryTent_row_quotient_coefficients_injective {K : Type*} [Field K]
    (N p a g : ℕ) (F G : K[X]) (hN : 0<N) (hp : 0<p) (hpN : 2*p≤24*N)
    (hag : a+g=p) (hgp : g+4*p=27*N)
    (hF : F.natDegree+8*N+3≤10*p) (hG : G.natDegree+8*N+3≤10*p)
    (hdF : secondaryTentRowTotalDivisor N p a ∣ F)
    (hdG : secondaryTentRowTotalDivisor N p a ∣ G)
    (heq : secondaryTentRowQuotientCoefficients N p a F =
      secondaryTentRowQuotientCoefficients N p a G) : F=G := by
  have hqF := secondaryTent_row_quotient_degree N p a g F hN hp hpN hag hgp hF
  have hqG := secondaryTent_row_quotient_degree N p a g G hN hp hpN hag hgp hG
  have hQ : secondaryTentRowQuotientLinear N p a F = secondaryTentRowQuotientLinear N p a G := by
    ext i
    by_cases hi : i<20*N
    · exact congrFun heq ⟨i,hi⟩
    · rw [coeff_eq_zero_of_natDegree_lt (hqF.trans_le (Nat.le_of_not_gt hi)),
        coeff_eq_zero_of_natDegree_lt (hqG.trans_le (Nat.le_of_not_gt hi))]
  have hm := congrArg (fun Q : K[X] => secondaryTentRowTotalDivisor N p a * Q) hQ
  have hmo : (secondaryTentRowTotalDivisor (K := K) N p a).Monic :=
    secondaryTent_row_divisor_monic (24*N-2*p) a (p+2*N-1) (p-1)
  have hrec (P : K[X]) (hd : secondaryTentRowTotalDivisor N p a ∣ P) :
      secondaryTentRowTotalDivisor N p a * secondaryTentRowQuotientLinear N p a P = P := by
    have h := modByMonic_add_div P (secondaryTentRowTotalDivisor N p a)
    rw [(modByMonic_eq_zero_iff_dvd hmo).mpr hd, zero_add] at h
    exact h
  simpa only [hrec F hdF,hrec G hdG] using hm

end
end CatalanMeasure.Parametric
