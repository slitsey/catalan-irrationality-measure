module
public import CatalanMeasure.Parametric.UpperPrimeValuation
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

def twentyOddLossNat (N p : ℕ) : ℕ :=
  if p ≤ 10*N then 40*N else
  if p ≤ 12*N then 60*N-2*p else
  if 2*p ≤ 27*N then 36*N else
  if p ≤ 14*N then 63*N-2*p else
  if p ≤ 16*N then 91*N-4*p else
  if p ≤ 24*N then 75*N-3*p else
  if p ≤ 27*N then 27*N-p else 0

theorem twenty_lowerPrimeLoss_eq {N p : ℕ} (hhalf : 2*p ≤ 27*N) :
    lowerPrimeLoss twenty N p=twentyOddLossNat N p :=by
  unfold lowerPrimeLoss lowerPairCount twentyOddLossNat
  rw [twenty_H,twenty_A]
  simp only [Parameters.L,Parameters.n,Parameters.q,Parameters.b,twenty]
  split_ifs <;> omega

theorem twenty_upperPrimeLoss_eq {N p : ℕ} (hhalf : 27*N ≤ 2*p) (hpH : p ≤ 27*N) :
    upperPrimeLoss twenty N p=twentyOddLossNat N p :=by
  unfold upperPrimeLoss
  simp only [paramUpperRetainedSize,paramUpperPairedSize,paramUpperExceptionalSize,
    Fintype.card_coe,paramUpperRetainedSet_card,paramUpperPairHighSet_card,paramUpperExceptionalSet_card]
  rw [twenty_H,twenty_A]
  simp only [Parameters.L,Parameters.n,Parameters.q,Parameters.b,twenty]
  unfold twentyOddLossNat
  split_ifs <;> omega

/-- Actual twenty-row odd-prime cost, with the screened piecewise model now proved. -/
theorem twenty_determinant_odd_valuation {N p : ℕ} [Fact p.Prime]
    (hN : 0<N) (hp2 : p≠2) (hHsq : 27*N<p^2) (hpH : p ≤ 27*N)
    (z : ℚ) (hz : (z.den : ZMod p)≠0) :
    -(twentyOddLossNat N p:ℤ) ≤ padicValRat p (determinantRat twenty z N) :=by
  have hHsq' : twenty.H N<p^2 :=by rw [twenty_H];exact hHsq
  by_cases hhalf : 2*p ≤ 27*N
  · have hzp : (((p:ℚ)*z).den : ZMod p)≠0 :=(rational_residue_mul (a :=(p:ℚ)) (by simp) hz).1
    have hh :=determinantRat_lower_prime_valuation twenty_admissible hp2 hN hHsq' z hzp
    rw [twenty_lowerPrimeLoss_eq hhalf] at hh
    exact hh
  · have hhalf' : twenty.H N ≤ 2*p :=by rw [twenty_H];omega
    have hpH' : p ≤ twenty.H N :=by rw [twenty_H];exact hpH
    have hA : twenty.A N ≤ p :=by rw [twenty_A];omega
    have hLH : twenty.L N<twenty.H N :=by
      rw [twenty_H]
      simp only [Parameters.L,Parameters.n,Parameters.b,Parameters.q,twenty]
      omega
    have hbp : twenty.b N<p :=by simp only [Parameters.b,twenty];omega
    have hJL : twenty.H N-p ≤ twenty.L N :=by
      rw [twenty_H]
      simp only [Parameters.L,Parameters.n,Parameters.b,Parameters.q,twenty]
      omega
    have hh :=determinantRat_upper_prime_valuation twenty twenty_admissible hp2 hN hHsq'
      hpH' hhalf' hA hLH hbp hJL z hz
    rw [twenty_upperPrimeLoss_eq (by omega) hpH] at hh
    exact hh

end
end CatalanMeasure.Parametric
