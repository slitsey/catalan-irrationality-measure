module
public import CatalanMeasure.Parametric.PairedPrimeColumns
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentReconstruction
public import CatalanMeasure.Parametric.TwentyParameters

/-!
# Actual secondary-tent source as fixed Frobenius coefficient pairings

This module starts at the literal `rawEntry_primeDigitPair`, including the
signed boundary moment at v=0. It proves that the source uses exactly six
moment coefficients and five zeta coefficients throughout the tent window.
The reversed polynomials below turn sampling into one ordinary coefficient
of a product with a literal p-th power. No Cartier or residue hypothesis is
used in these source identities.
-/

@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
open scoped BigOperators
noncomputable section

/-- Reverse a finite source list, retaining its declared length. -/
def secondaryTentSourceReverse {K : Type*} [CommSemiring K]
    (m : ℕ) (f : ℕ → K) : K[X] :=
  ∑ v ∈ Finset.range m, monomial (m - 1 - v) (f v)

theorem secondaryTent_source_reverse_coeff {K : Type*} [CommSemiring K]
    {m v : ℕ} (hv : v<m) (f : ℕ → K) :
    (secondaryTentSourceReverse m f).coeff (m-1-v)=f v := by
  classical
  rw [secondaryTentSourceReverse, finsetSum_coeff]
  rw [Finset.sum_eq_single v]
  · simp
  · intro i hi hiv
    have him : i<m := Finset.mem_range.mp hi
    have hne : m-1-i ≠ m-1-v := by omega
    simp [coeff_monomial, hne]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr hv)).elim

/-- An exact coefficient realization of digit sampling. -/
theorem secondaryTent_source_sample_coefficient {K : Type*} [CommSemiring K]
    (m p e : ℕ) (f : ℕ → K) (Q : K[X]) :
    primeDigitSample m p e f Q =
      (Q * expand K p (secondaryTentSourceReverse m f)).coeff ((m-1)*p+e) := by
  classical
  unfold primeDigitSample secondaryTentSourceReverse
  simp only [map_sum, expand_monomial, Finset.mul_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro v hv
  have hvlt : v < m := Finset.mem_range.mp hv
  have heq : (m-1)*p+e = (v*p+e)+(m-1-v)*p := by
    have hh : m-1 = v+(m-1-v) := by omega
    calc
      (m-1)*p+e = (v+(m-1-v))*p+e := congrArg (fun a => a*p+e) hh
      _ = (v*p+e)+(m-1-v)*p := by ring
  rw [heq, coeff_mul_monomial]

/-- In the prime field, the source expansion is a literal Frobenius power. -/
theorem secondaryTent_source_sample_frobenius {p : ℕ} [Fact p.Prime]
    (m e : ℕ) (f : ℕ → ZMod p) (Q : (ZMod p)[X]) :
    primeDigitSample m p e f Q =
      (Q * (secondaryTentSourceReverse m f)^p).coeff ((m-1)*p+e) := by
  simpa only [ZMod.expand_card] using
    secondaryTent_source_sample_coefficient m p e f Q

theorem secondaryTent_source_sample_truncate {K : Type*} [CommSemiring K]
    {H m p e : ℕ} (hm : m ≤ H) (f : ℕ → K) (Q : K[X])
    (hQ : ∀ v, m ≤ v → Q.coeff (v*p+e)=0) :
    primeDigitSample H p e f Q = primeDigitSample m p e f Q := by
  classical
  unfold primeDigitSample
  symm
  apply Finset.sum_subset (Finset.range_mono hm)
  intro v hv hvm
  have hmv : m ≤ v := by simpa only [Finset.mem_range, not_lt] using hvm
  rw [hQ v hmv, zero_mul]

/-- The six actual signed moments. In particular the first one is
`momentRatSigned (-1) J`, rather than an extrapolated positive moment. -/
def secondaryTentSourceMoment (p J : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  secondaryTentSourceReverse 6
    (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) J))

def secondaryTentSourceZeta (p J : ℕ) [Fact p.Prime] : (ZMod p)[X] :=
  secondaryTentSourceReverse 5
    (fun v => palindromicRatResidue p (zetaRat v J))

theorem secondaryTent_source_boundary_coefficient (p J : ℕ) [Fact p.Prime] :
    (secondaryTentSourceMoment p J).coeff 5 =
      palindromicRatResidue p (boundaryPlus (J+1)) := by
  simpa [secondaryTentSourceMoment, momentRatSigned, momentRatNegOne] using
    secondaryTent_source_reverse_coeff (m:=6) (v:=0) (by decide)
      (fun v => palindromicRatResidue p (momentRatSigned ((v:ℤ)-1) J))

/-- A source identity on the actual row polynomials, not a model matrix.
The bound H≤5p is exactly what removes all higher moment indices. -/
theorem secondaryTent_source_actual_pair {P : Parameters} {p N r j : ℕ}
    [hp : Fact p.Prime] (hAdm : Admissible P) (hN : 0<N)
    (hsmall : 5 ≤ P.H N) (hwidth : P.H N ≤ 5*p) :
    primeDigitPair (P.H N) p j
        ((rowP P N r).map (Int.castRingHom (ZMod p)))
        ((rowD P N r).map (Int.castRingHom (ZMod p))) =
      (X*oddPrimeWeight p*((rowP P N r).map (Int.castRingHom (ZMod p))) *
        (secondaryTentSourceMoment p (j/p))^p).coeff (5*p+j%p) -
      (3/2:ZMod p)*
        (((rowD P N r).map (Int.castRingHom (ZMod p))) *
          (secondaryTentSourceZeta p (j/p))^p).coeff (4*p+j%p) := by
  let F := (rowP P N r).map (Int.castRingHom (ZMod p))
  let G := (rowD P N r).map (Int.castRingHom (ZMod p))
  have hF (i : ℕ) (hi : P.H N ≤ i) : F.coeff i=0 := by
    simp only [F, coeff_map, rowP_coeff_eq_zero_of_ge hAdm hN hi, map_zero]
  have hG (i : ℕ) (hi : P.H N ≤ i) : G.coeff i=0 := by
    simp only [G, coeff_map, rowD_coeff_eq_zero_of_ge hAdm hN hi, map_zero]
  have hM (v : ℕ) (hv : 6 ≤ v) :
      (X*oddPrimeWeight p*F).coeff (v*p+j%p)=0 := by
    apply weighted_prime_coeff_zero_high hp.out.pos F hF
    have hm := Nat.mul_le_mul_right p hv
    omega
  have hZ (v : ℕ) (hv : 5 ≤ v) : G.coeff (v*p+j%p)=0 := by
    apply hG
    have hm := Nat.mul_le_mul_right p hv
    omega
  unfold primeDigitPair
  rw [secondaryTent_source_sample_truncate (by omega : 6 ≤ P.H N+1) _ _ hM,
    secondaryTent_source_sample_truncate hsmall _ _ hZ,
    secondaryTent_source_sample_frobenius, secondaryTent_source_sample_frobenius]
  rfl

/-- The source bridge starting directly at the scaled rational raw entry. -/
theorem secondaryTent_source_raw_entry {P : Parameters} {p N r j : ℕ}
    [hp : Fact p.Prime] (hAdm : Admissible P) (hN : 0<N) (hp2 : p≠2)
    (hH : P.H N<p^2) (hj : j<P.H N)
    (hsmall : 5 ≤ P.H N) (hwidth : P.H N ≤ 5*p)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat P z N r j) =
      (X*oddPrimeWeight p*((rowP P N r).map (Int.castRingHom (ZMod p))) *
        (secondaryTentSourceMoment p (j/p))^p).coeff (5*p+j%p) -
      (3/2:ZMod p)*
        (((rowD P N r).map (Int.castRingHom (ZMod p))) *
          (secondaryTentSourceZeta p (j/p))^p).coeff (4*p+j%p) := by
  rw [rawEntry_primeDigitPair hAdm hN hp2 hH hj z hzp]
  exact secondaryTent_source_actual_pair hAdm hN hsmall hwidth

/-- The elementary source width and macro count hold on the complete
canonical tent interval, before any constraints on row inputs. -/
theorem secondaryTent_source_twenty_window {N p j : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hwindow : 52*N < 9*p) (hj : j<24*N) :
    5 ≤ twenty.H N ∧ twenty.H N ≤ 5*p ∧
      twenty.H N < p^2 ∧ j < twenty.H N ∧ j/p < 5 := by
  simp only [twenty_H]
  have hp6 : 6 ≤ p := by nlinarith
  have hwidth : 27*N ≤ 5*p := by nlinarith
  have hjp : j < 5*p := by nlinarith
  refine ⟨by omega, hwidth, ?_, by omega, ?_⟩
  · nlinarith
  · exact (Nat.div_lt_iff_lt_mul hp.out.pos).mpr (by simpa [Nat.mul_comm] using hjp)

/-- The fully specialized actual source theorem: all size hypotheses other
than the lower tent window are discharged arithmetically. -/
theorem secondaryTent_source_twenty_raw_entry {p N r j : ℕ} [hp : Fact p.Prime]
    (hN : 0<N) (hwindow : 52*N < 9*p) (hj : j<24*N)
    (z : ℚ) (hzp : (((p:ℚ)*z).den : ZMod p)≠0) :
    palindromicRatResidue p ((p:ℚ)^2*rawEntryRat twenty z N r j) =
      (X*oddPrimeWeight p*((rowP twenty N r).map (Int.castRingHom (ZMod p))) *
        (secondaryTentSourceMoment p (j/p))^p).coeff (5*p+j%p) -
      (3/2:ZMod p)*
        (((rowD twenty N r).map (Int.castRingHom (ZMod p))) *
          (secondaryTentSourceZeta p (j/p))^p).coeff (4*p+j%p) := by
  have hs := secondaryTent_source_twenty_window hN hwindow hj
  have hp2 : p≠2 := by intro he; subst p; nlinarith
  exact secondaryTent_source_raw_entry twenty_admissible hN hp2 hs.2.2.1
    hs.2.2.2.1 hs.1 hs.2.1 z hzp

end
end CatalanMeasure.Parametric
