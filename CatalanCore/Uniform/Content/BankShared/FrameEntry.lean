module

public import CatalanCore.Arith.Hybrid.Tropical
public import CatalanCore.Frame.Spec
public import Mathlib.Data.Nat.Log

@[expose] public section
set_option Elab.async false

/-! # Crude entry valuations of the Loewner matrix (canonical extraction of B4b proofs)

For a `Frame` `Fr`, a prime `p` and nodes `A, B ≤ N` (`1 ≤ N`),
`p ^ (2 ⌊log_p N⌋ + cFr Fr) * Fr.Mn A B` is `p`-integral.  Here `cFr Fr` is a constant depending only on
the frame.  This is the entry bound behind the crude exponent `Ecrude` (SPEC-thirds, "Complete
treatment of small and exceptional primes"); no cancellation or gcd assumption is used. -/

namespace CatalanCore.Uniform.Content.BankShared
open CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid Polynomial Finset

section Inverse
variable {p : ℕ} [hp : Fact p.Prime]

lemma mem_of_le {L L' : ℕ} {x : ℚ} (h : L ≤ L') (hx : (p : ℚ) ^ L * x ∈ LocRing p) :
    (p : ℚ) ^ L' * x ∈ LocRing p :=
  GLE.C_iff.1 ((GLE.C_iff.2 hx).mono h)

lemma pow_mul_inv_mem {n X : ℕ} (hn : 0 < n) (hnX : n ≤ X) :
    (p : ℚ) ^ (Nat.log p X) * (1 / (n : ℚ)) ∈ LocRing p := by
  have hle : n.factorization p ≤ Nat.log p X :=
    Nat.le_log_of_pow_le hp.out.one_lt
      ((Nat.le_of_dvd hn (Nat.ordProj_dvd n p)).trans hnX)
  have h := div_mem_locRing (p := p) hn (W := p ^ (Nat.log p X)) (pow_dvd_pow p hle)
  simpa [div_eq_mul_inv] using h

lemma log_mul_le {D N : ℕ} (hD : 0 < D) (hN : 0 < N) :
    Nat.log p (D * N) ≤ Nat.log p N + D := by
  have h1 : D < p ^ D := Nat.lt_pow_self hp.out.one_lt
  have h2 : N < p ^ (Nat.log p N + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt N
  have h3 : D * N < p ^ (Nat.log p N + D + 1) := by
    calc D * N < p ^ D * p ^ (Nat.log p N + 1) := Nat.mul_lt_mul'' h1 h2
      _ = p ^ (Nat.log p N + D + 1) := by rw [← pow_add]; congr 1; omega
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero hD.ne' hN.ne') h3
  omega

/-- `p ^ (⌊log_p N⌋ + D) / n` is `p`-integral for `1 ≤ n ≤ D N`. -/
lemma inv_mem_D {D N n : ℕ} (hD : 0 < D) (hN : 0 < N) (hn : 0 < n) (hnD : n ≤ D * N) :
    (p : ℚ) ^ (Nat.log p N + D) * (1 / (n : ℚ)) ∈ LocRing p :=
  mem_of_le (log_mul_le (p := p) hD hN) (pow_mul_inv_mem hn hnD)

end Inverse

/-- Natural size of a positive shift `μ`: denominator plus numerator. -/
def Dm (μ : ℚ) : ℕ := μ.den + μ.num.toNat

/-- A positive constant dominating every `Dm (Fr.μ i)`. -/
def Dc (Fr : Frame) : ℕ := 1 + ∑ i, Dm (Fr.μ i)

lemma Dc_pos (Fr : Frame) : 0 < Dc Fr := by unfold Dc; omega

lemma Dm_le_Dc (Fr : Frame) (i : Fin Fr.d) : Dm (Fr.μ i) ≤ Dc Fr := by
  unfold Dc
  have := Finset.single_le_sum (f := fun j => Dm (Fr.μ j)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)
  omega

/-- `(k - 1) + μ = ((k-1) den + num)/den` for `μ > 0`. -/
lemma shift_eq {μ : ℚ} (hμ : 0 < μ) {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℚ) - 1 + μ) = (((k - 1) * μ.den + μ.num.toNat : ℕ) : ℚ) / (μ.den : ℚ) := by
  have hnum : (μ.num.toNat : ℤ) = μ.num := Int.toNat_of_nonneg (Rat.num_pos.2 hμ).le
  have hden : (μ.den : ℚ) ≠ 0 := by exact_mod_cast μ.den_nz
  have hnum' : ((μ.num.toNat : ℕ) : ℚ) = (μ.num : ℚ) := by exact_mod_cast hnum
  have hk1 : (((k - 1 : ℕ)) : ℚ) = (k : ℚ) - 1 := by rw [Nat.cast_sub hk]; simp
  rw [eq_div_iff hden, Nat.cast_add, Nat.cast_mul, hk1, hnum']
  have := Rat.mul_den_eq_num μ
  linear_combination this

lemma shift_pos {μ : ℚ} (hμ : 0 < μ) {k : ℕ} (hk : 1 ≤ k) :
    0 < (k - 1) * μ.den + μ.num.toNat := by
  have : 0 < μ.num := Rat.num_pos.2 hμ
  omega

lemma shift_le {μ : ℚ} {k N : ℕ} (hk : k ≤ N) (hk1 : 1 ≤ k) :
    (k - 1) * μ.den + μ.num.toNat ≤ Dm μ * N := by
  unfold Dm
  have h1 : (k - 1) * μ.den ≤ N * μ.den := Nat.mul_le_mul_right _ (by omega)
  have h2 : μ.num.toNat ≤ μ.num.toNat * N := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

section Terms
variable {p : ℕ} [hp : Fact p.Prime] (Fr : Frame)

/-- Exponent for a single inverse shift. -/
def T1 (p N : ℕ) (Fr : Frame) : ℕ := Nat.log p N + Dc Fr

lemma inv_shift_mem (i : Fin Fr.d) {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hk1 : 1 ≤ k) :
    (p : ℚ) ^ (T1 p N Fr) * (1 / ((k : ℚ) - 1 + Fr.μ i)) ∈ LocRing p := by
  have hμ := (Fr.hμ i).1
  have hn := shift_pos hμ hk1
  have hle : (k - 1) * (Fr.μ i).den + (Fr.μ i).num.toNat ≤ Dc Fr * N :=
    (shift_le hk hk1).trans (Nat.mul_le_mul_right _ (Dm_le_Dc Fr i))
  have h := inv_mem_D (p := p) (Dc_pos Fr) hN hn hle
  rw [shift_eq hμ hk1]
  have e : (p : ℚ) ^ (T1 p N Fr) * (1 / ((((k - 1) * (Fr.μ i).den + (Fr.μ i).num.toNat : ℕ) : ℚ)
      / ((Fr.μ i).den : ℚ))) = (((Fr.μ i).den : ℕ) : ℤ) *
      ((p : ℚ) ^ (Nat.log p N + Dc Fr) *
        (1 / ((((k - 1) * (Fr.μ i).den + (Fr.μ i).num.toNat : ℕ)) : ℚ))) := by
    unfold T1; rw [one_div_div]; push_cast; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) h

lemma delta_mem {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hk1 : 1 ≤ k) :
    (p : ℚ) ^ (T1 p N Fr) * Fr.Delta k ∈ LocRing p := by
  unfold Frame.Delta
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro i _
  have h := inv_shift_mem (p := p) Fr i hN hk hk1
  have e : (p : ℚ) ^ (T1 p N Fr) * ((Fr.w i : ℚ) / ((k : ℚ) - 1 + Fr.μ i)) =
      (Fr.w i : ℤ) * ((p : ℚ) ^ (T1 p N Fr) * (1 / ((k : ℚ) - 1 + Fr.μ i))) := by
    push_cast; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) h

lemma dsq_mem {N k : ℕ} (hN : 0 < N) (hk : k ≤ N) (hk1 : 1 ≤ k) :
    (p : ℚ) ^ (2 * T1 p N Fr) * Fr.Dsq k ∈ LocRing p := by
  unfold Frame.Dsq
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro i _
  have h := inv_shift_mem (p := p) Fr i hN hk hk1
  have e : (p : ℚ) ^ (2 * T1 p N Fr) * ((Fr.w i : ℚ) / ((k : ℚ) - 1 + Fr.μ i) ^ 2) =
      (Fr.w i : ℤ) * ((p : ℚ) ^ (T1 p N Fr) * (1 / ((k : ℚ) - 1 + Fr.μ i))) ^ 2 := by
    push_cast; generalize (k : ℚ) - 1 + Fr.μ i = x; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).pow_mem h 2)

lemma sumDelta_mem {N a b : ℕ} (hN : 0 < N) (hb : b ≤ N) :
    (p : ℚ) ^ (T1 p N Fr) * ∑ k ∈ Ioc a b, Fr.Delta k ∈ LocRing p := by
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro k hk
  rw [Finset.mem_Ioc] at hk
  exact delta_mem Fr hN (by omega) (by omega)

lemma sumDsq_mem {N a : ℕ} (hN : 0 < N) (ha : a ≤ N) :
    (p : ℚ) ^ (2 * T1 p N Fr) * ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ LocRing p := by
  rw [Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro k hk
  rw [Finset.mem_Icc] at hk
  exact dsq_mem Fr hN (by omega) (by omega)

lemma norm_inv_mem : (p : ℚ) ^ (Fr.norm.num.toNat) * (1 / Fr.norm) ∈ LocRing p := by
  have hpos : 0 < Fr.norm.num := Rat.num_pos.2 Fr.hnorm
  have hn : 0 < Fr.norm.num.toNat := by omega
  have hfact : (Fr.norm.num.toNat).factorization p ≤ Fr.norm.num.toNat := by
    have h1 : p ^ ((Fr.norm.num.toNat).factorization p) ≤ Fr.norm.num.toNat :=
      Nat.le_of_dvd hn (Nat.ordProj_dvd _ p)
    have h2 : (Fr.norm.num.toNat).factorization p < p ^ ((Fr.norm.num.toNat).factorization p) :=
      Nat.lt_pow_self hp.out.one_lt
    omega
  have h := div_mem_locRing (p := p) hn (W := p ^ (Fr.norm.num.toNat)) (pow_dvd_pow p hfact)
  have hnum : (Fr.norm.num.toNat : ℤ) = Fr.norm.num := Int.toNat_of_nonneg hpos.le
  have hnum' : ((Fr.norm.num.toNat : ℕ) : ℚ) = (Fr.norm.num : ℚ) := by exact_mod_cast hnum
  have e : (p : ℚ) ^ (Fr.norm.num.toNat) * (1 / Fr.norm) =
      (Fr.norm.den : ℤ) * (((p ^ (Fr.norm.num.toNat) : ℕ) : ℚ) / ((Fr.norm.num.toNat : ℕ) : ℚ)) := by
    rw [hnum']
    have hnn : (Fr.norm.num : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hne : Fr.norm ≠ 0 := Fr.hnorm.ne'
    have hm := Rat.mul_den_eq_num Fr.norm
    have e1 : (1 : ℚ) / Fr.norm = (Fr.norm.den : ℚ) / (Fr.norm.num : ℚ) := by
      rw [div_eq_div_iff hne hnn]; linear_combination (-1 : ℚ) * hm
    rw [e1]; push_cast; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) h

end Terms

/-- The frame constant of the crude exponent. -/
def cFr (Fr : Frame) : ℕ := Fr.norm.num.toNat + 2 * Dc Fr

section Entry
variable {p : ℕ} [hp : Fact p.Prime] (Fr : Frame)

theorem mn_mem {N A B : ℕ} (hN : 0 < N) (hA : A ≤ N) (hB : B ≤ N) :
    (p : ℚ) ^ (2 * Nat.log p N + cFr Fr) * Fr.Mn A B ∈ LocRing p := by
  unfold Frame.Mn
  split_ifs with h
  · have h1 := norm_inv_mem (p := p) Fr
    have h2 := sumDsq_mem (p := p) Fr hN hA
    have e : (p : ℚ) ^ (Fr.norm.num.toNat + 2 * T1 p N Fr) *
        (-(1 / Fr.norm) * ∑ k ∈ Icc 1 A, Fr.Dsq k) =
        -((p : ℚ) ^ (Fr.norm.num.toNat) * (1 / Fr.norm)) *
          ((p : ℚ) ^ (2 * T1 p N Fr) * ∑ k ∈ Icc 1 A, Fr.Dsq k) := by
      rw [pow_add]; ring
    have hm : (p : ℚ) ^ (Fr.norm.num.toNat + 2 * T1 p N Fr) *
        (-(1 / Fr.norm) * ∑ k ∈ Icc 1 A, Fr.Dsq k) ∈ LocRing p := by
      rw [e]; exact (LocRing p).mul_mem ((LocRing p).neg_mem h1) h2
    refine mem_of_le ?_ hm
    unfold T1 cFr; omega
  · have h1 := norm_inv_mem (p := p) Fr
    have hlt : min A B < max A B := lt_of_le_of_ne (min_le_max) (by
      intro hh; apply h; rcases le_total A B with hab | hab
      · rw [min_eq_left hab, max_eq_right hab] at hh; exact hh
      · rw [min_eq_right hab, max_eq_left hab] at hh; exact hh.symm)
    have hmax : max A B ≤ N := max_le hA hB
    have h3 : (1 : ℚ) / (((max A B : ℕ) : ℚ) - ((min A B : ℕ) : ℚ)) =
        1 / (((max A B - min A B : ℕ)) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
    have h4 := pow_mul_inv_mem (p := p) (n := max A B - min A B) (X := N) (by omega) (by omega)
    have h2 := sumDelta_mem (p := p) Fr hN (a := min A B) hmax
    have e : (p : ℚ) ^ (Fr.norm.num.toNat + Nat.log p N + T1 p N Fr) *
        (1 / Fr.norm * (1 / (((max A B : ℕ) : ℚ) - ((min A B : ℕ) : ℚ))) *
          ∑ k ∈ Ioc (min A B) (max A B), Fr.Delta k) =
        ((p : ℚ) ^ (Fr.norm.num.toNat) * (1 / Fr.norm)) *
          ((p : ℚ) ^ (Nat.log p N) * (1 / (((max A B - min A B : ℕ)) : ℚ))) *
          ((p : ℚ) ^ (T1 p N Fr) * ∑ k ∈ Ioc (min A B) (max A B), Fr.Delta k) := by
      rw [← h3]; simp only [pow_add]; ring
    have hm : (p : ℚ) ^ (Fr.norm.num.toNat + Nat.log p N + T1 p N Fr) *
        (1 / Fr.norm * (1 / (((max A B : ℕ) : ℚ) - ((min A B : ℕ) : ℚ))) *
          ∑ k ∈ Ioc (min A B) (max A B), Fr.Delta k) ∈ LocRing p := by
      rw [e]; exact (LocRing p).mul_mem ((LocRing p).mul_mem h1 h4) h2
    refine mem_of_le ?_ hm
    unfold T1 cFr; omega

end Entry

end CatalanCore.Uniform.Content.BankShared
