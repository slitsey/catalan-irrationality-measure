module
public import CatalanMeasure.Parametric.SecondaryTentDimension
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
open scoped BigOperators
noncomputable section

/-- Polynomial coefficient model for the inverse Cartier reconstruction.
Each packet occupies one residue class of exponents modulo `p`. -/
def secondaryTentInterleave {K : Type*} [CommSemiring K] (p : ℕ)
    (A : Fin p → K[X]) : K[X] :=
  ∑ e : Fin p, Polynomial.expand K p (A e) * X ^ e.val

/-- Extraction at the unramified coefficient parameter: exponent `p*k+e`
recovers precisely the `k`th coefficient of packet `e`. -/
theorem secondaryTent_interleave_coeff {K : Type*} [CommSemiring K]
    {p : ℕ} (hp : 0 < p) (A : Fin p → K[X]) (e : Fin p) (k : ℕ) :
    (secondaryTentInterleave p A).coeff (p * k + e.val) = (A e).coeff k := by
  classical
  rw [secondaryTentInterleave, finsetSum_coeff]
  rw [Finset.sum_eq_single e]
  · rw [coeff_mul_X_pow, coeff_expand_mul' hp]
  · intro j hj hje
    rw [coeff_mul_X_pow']
    split_ifs with hle
    · rw [coeff_expand hp]
      have hn : ¬ p ∣ p * k + e.val - j.val := by
        intro hd
        have heq : p * k + e.val = (p * k + e.val - j.val) + j.val :=
          (Nat.sub_add_cancel hle).symm
        have hm := congrArg (fun n : ℕ => n % p) heq
        have hev : e.val = j.val := by
          simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hd,
            Nat.mod_eq_of_lt e.isLt, Nat.mod_eq_of_lt j.isLt] using hm
        exact hje (Fin.ext hev.symm)
      rw [ite_eq_right hn]
    · rfl
  · simp

theorem secondaryTent_interleave_injective {K : Type*} [CommSemiring K]
    {p : ℕ} (hp : 0 < p) : Function.Injective (secondaryTentInterleave (K := K) p) := by
  intro A B h
  funext e
  ext k
  have hc := congrArg (fun f : K[X] => f.coeff (p * k + e.val)) h
  simpa only [secondaryTent_interleave_coeff hp] using hc

def secondaryTentInterleaveLinear {K : Type*} [Field K] (p : ℕ) :
    (Fin p → K[X]) →ₗ[K] K[X] where
  toFun := secondaryTentInterleave p
  map_add' := by
    intro A B
    simp [secondaryTentInterleave, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c A
    simp [secondaryTentInterleave, Finset.smul_sum]

/-- Both polynomial numerators can be extracted coefficient by coefficient.
The seed map may take values in pairs: this is the common-denominator
`(P,Q)` representation of the five fixed differentials. -/
theorem secondaryTent_seed_reconstruction_injective {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {p : ℕ} (hp : 0 < p)
    (seed : V →ₗ[K] (K[X] × K[X])) (hseed : Function.Injective seed) :
    Function.Injective (fun c : Fin p → V =>
      (secondaryTentInterleave p (fun e => (seed (c e)).1),
       secondaryTentInterleave p (fun e => (seed (c e)).2))) := by
  intro c d h
  have hU := secondaryTent_interleave_injective hp (congrArg Prod.fst h)
  have hV := secondaryTent_interleave_injective hp (congrArg Prod.snd h)
  funext e
  apply hseed
  exact Prod.ext (congrFun hU e) (congrFun hV e)

/-- Over the prime field, polynomial expansion is exactly the Frobenius
power. Thus coefficient extraction proves the required packet independence
without a normality or generic-rank assumption. -/
theorem secondaryTent_frobenius_packet_coeff {p : ℕ} [Fact p.Prime]
    (A : Fin p → (ZMod p)[X]) (e : Fin p) (k : ℕ) :
    (∑ j : Fin p, (A j) ^ p * X ^ j.val).coeff (p * k + e.val) = (A e).coeff k := by
  simpa only [secondaryTentInterleave, ZMod.expand_card] using
    secondaryTent_interleave_coeff (Fact.out : p.Prime).pos A e k

theorem secondaryTent_frobenius_packets_zero_iff {p : ℕ} [Fact p.Prime]
    (A : Fin p → (ZMod p)[X]) :
    (∑ j : Fin p, (A j) ^ p * X ^ j.val) = 0 ↔ ∀ j, A j = 0 := by
  constructor
  · intro h e
    ext k
    have hc := congrArg (fun f : (ZMod p)[X] => f.coeff (p * k + e.val)) h
    simpa only [secondaryTent_frobenius_packet_coeff, coeff_zero] using hc
  · intro h
    simp [h, (Fact.out : p.Prime).ne_zero]

end
end CatalanMeasure.Parametric
