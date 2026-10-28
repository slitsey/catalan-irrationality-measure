module

public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

/-!
# UF families: closed forms of the prefix values `V`, `W` of a two-term frame (lane H10)

For the two-term frame `Δ_t = 1/t - q/(q t - o)`, `D_t = 1/t² - q²/(q t - o)²` and nodes `a < N ≤ p²`
the residues `V a = p F(a) mod p` and `W a = p² Σ D_k mod p` of `PoleData` are the images of explicit
RATIONAL numbers that depend on `a` only through the two small integers
`a₁ = ⌊a/p⌋` and `a₂ = ⌊(q a - o)/p⌋` and on `p mod q`:

  `Lval q o r a₁ a₂ = H_1(a₁) - q Σ_{1 ≤ j ≤ a₂, q ∣ p j + o} 1/j`,
  `Eval q o r a₁ a₂ = H_2(a₁) - q² Σ_{1 ≤ j ≤ a₂, q ∣ p j + o} 1/j²`    (`r = p mod q`).

`good_V` / `good_W` prove this (`Good p _ (D.V a)`).  Thus the joint-type data of a UF cell family
is a computable function of the frame data `(q, o)`, the class `r = p mod q` and the integers
`(a₁, a₂)` of its nodes.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic
  CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily

/-- Generalised harmonic sum `Σ_{1 ≤ m ≤ n} 1/m^s` (structural). -/
def harm (s : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => harm s n + 1 / ((n + 1 : ℕ) : ℚ) ^ s

/-- Pole sum `Σ_{1 ≤ j ≤ n, q ∣ r j + o} 1/j^s` (structural). -/
def poleSum (q o r s : ℕ) : ℕ → ℚ
  | 0 => 0
  | j + 1 => poleSum q o r s j + if (r * (j + 1) + o) % q = 0 then 1 / ((j + 1 : ℕ) : ℚ) ^ s else 0

/-- Closed form of the prefix residues, exponent `e` (`e = 1`: `V`, `e = 2`: `W`). -/
def Cval (e q o r a₁ a₂ : ℕ) : ℚ := harm e a₁ - (q : ℚ) ^ e * poleSum q o r e a₂

variable {p : ℕ} [Fact p.Prime]

lemma good_scaled' {n : ℕ} (hn : 0 < n) (h2 : ¬ p ^ 2 ∣ n) :
    Good p ((p : ℚ) / n) (invResidue p n) := by
  have hp := (Fact.out : p.Prime)
  by_cases hd : p ∣ n
  · obtain ⟨j, hj⟩ := hd
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hj; omega
      · exact h
    have hjz : (j : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact h2 (by rw [hj, pow_two]; exact mul_dvd_mul_left p h)
    have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
    have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hq : (n : ℚ) = p * j := by exact_mod_cast hj
    have hd' : p ∣ n := ⟨j, hj⟩
    have hdiv : n / p = j := by rw [hj, Nat.mul_div_right _ hp.pos]
    have g := (Good.one (ℓ := p)).div (Good.natCast (ℓ := p) j) hjz
    refine (g.congr' ?_).congr ?_
    · rw [hq]; field_simp
    · simp [invResidue, hd', hdiv, div_eq_mul_inv]
  · have hnz : (n : ZMod p) ≠ 0 := by
      rwa [Ne, ZMod.natCast_eq_zero_iff]
    have g := ((Good.one (ℓ := p)).div (Good.natCast (ℓ := p) n) hnz).ell_mul
    simpa [invResidue, hd, div_eq_mul_inv] using g

lemma good_inc {n : ℕ} (e : ℕ) (he : 0 < e) (hn : 0 < n) (h2 : ¬ p ^ 2 ∣ n) :
    Good p (if p ∣ n then 1 / ((n / p : ℕ) : ℚ) ^ e else 0) ((invResidue p n) ^ e) := by
  have hp := (Fact.out : p.Prime)
  by_cases hd : p ∣ n
  · obtain ⟨j, hj⟩ := hd
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp at hj; omega
      · exact h
    have hjz : (j : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact h2 (by rw [hj, pow_two]; exact mul_dvd_mul_left p h)
    have hdiv : n / p = j := by rw [hj, Nat.mul_div_right _ hp.pos]
    have g := ((Good.one (ℓ := p)).div (Good.natCast (ℓ := p) j) hjz).pow' e
    rw [if_pos ⟨j, hj⟩, hdiv]
    refine (g.congr' ?_).congr ?_
    · rw [one_div, one_div, inv_pow]
    · have hd' : p ∣ n := ⟨j, hj⟩
      simp [invResidue, hd', hdiv, div_eq_mul_inv]
  · rw [if_neg hd]
    have : invResidue p n = 0 := by simp [invResidue, hd]
    rw [this, zero_pow he.ne']
    exact Good.zero

lemma div_step {p q n n' : ℕ} (hp : 0 < p) (hqp : q < p) (hnn : n < n') (hn' : n' ≤ n + q) :
    (n' / p = n / p ∨ n' / p = n / p + 1) ∧ (p ∣ n' → n' / p = n / p + 1) := by
  have h1 : n / p ≤ n' / p := Nat.div_le_div_right hnn.le
  have h2 : n' / p ≤ n / p + 1 := by
    have : n' / p < n / p + 2 := by
      rw [Nat.div_lt_iff_lt_mul hp]
      have := Nat.lt_mul_div_succ n hp
      nlinarith
    omega
  refine ⟨by omega, fun hd => ?_⟩
  obtain ⟨k, rfl⟩ := hd
  have hk : p * k / p = k := Nat.mul_div_cancel_left k hp
  have h3 : n / p < k := Nat.div_lt_of_lt_mul (by linarith [hnn, Nat.mul_comm p k])
  omega

lemma mod_eq_mod (p q j o : ℕ) : (p % q * j + o) % q = (p * j + o) % q :=
  ((Nat.mod_modEq p q).mul_right j).add_right o

lemma harm_step (e a p : ℕ) :
    harm e ((a + 1) / p) = harm e (a / p) +
      if p ∣ a + 1 then 1 / (((a + 1) / p : ℕ) : ℚ) ^ e else 0 := by
  by_cases hd : p ∣ a + 1
  · have h : (a + 1) / p = a / p + 1 := by rw [Nat.succ_div, if_pos hd]
    rw [h, if_pos hd, harm]
  · have h : (a + 1) / p = a / p := by rw [Nat.succ_div, if_neg hd, add_zero]
    rw [h, if_neg hd, add_zero]

lemma pole_step {p q o : ℕ} (a e : ℕ) (hq : 0 < q) (ho : o < q) (hqp : q < p) :
    poleSum q o (p % q) e ((q * (a + 1) - o) / p) =
      poleSum q o (p % q) e ((q * a - o) / p) +
        if p ∣ q * (a + 1) - o then 1 / (((q * (a + 1) - o) / p : ℕ) : ℚ) ^ e else 0 := by
  have hp : 0 < p := by omega
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h1 : (q * (0 + 1) - o) / p = 0 := Nat.div_eq_of_lt (by omega)
    have h2 : ¬ p ∣ q * (0 + 1) - o := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    simp only [Nat.mul_zero, Nat.zero_sub, Nat.zero_div] at *
    rw [h1, if_neg h2]
    simp [poleSum]
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have hmul : q * (b + 1 + 1) = q * (b + 1) + q := Nat.mul_succ q (b + 1)
    have hmul2 : q * (b + 1) = q * b + q := Nat.mul_succ q b
    have hoq : o ≤ q * b + q := by omega
    have hn' : q * (b + 1 + 1) - o = (q * (b + 1) - o) + q := by omega
    have hnn : q * (b + 1) - o < q * (b + 1 + 1) - o := by omega
    obtain ⟨hcases, hdiv⟩ := div_step hp hqp hnn hn'.le
    by_cases hd : p ∣ q * (b + 1 + 1) - o
    · have hj := hdiv hd
      have hpj : p * ((q * (b + 1) - o) / p + 1) = q * (b + 1 + 1) - o := by
        rw [← hj]; exact Nat.mul_div_cancel' hd
      have hcond : (p % q * ((q * (b + 1) - o) / p + 1) + o) % q = 0 := by
        rw [mod_eq_mod, hpj]
        have : q * (b + 1 + 1) - o + o = q * (b + 1 + 1) := by omega
        rw [this]; exact Nat.mul_mod_right _ _
      rw [if_pos hd, hj, poleSum, if_pos hcond]
    · rw [if_neg hd, add_zero]
      rcases hcases with h | h
      · rw [h]
      · rw [h, poleSum, if_neg, add_zero]
        intro hc
        rw [mod_eq_mod] at hc
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero hc
        have hle := Nat.div_mul_le_self (q * (b + 1 + 1) - o) p
        rw [h] at hle
        have hgt := Nat.lt_mul_div_succ (q * (b + 1) - o) hp
        generalize (q * (b + 1) - o) / p = m at *
        have e : p * (m + 1) = (m + 1) * p := Nat.mul_comm _ _
        have hob : o ≤ q * (b + 1 + 1) := by omega
        have hob2 : o ≤ q * (b + 1) := by omega
        have hle' : q * k ≤ q * (b + 1 + 1) := by omega
        have hlt' : q * (b + 1) < q * k := by omega
        have k1 : k ≤ b + 1 + 1 := Nat.le_of_mul_le_mul_left hle' hq
        have k2 : b + 1 < k := Nat.lt_of_mul_lt_mul_left hlt'
        have hkk : k = b + 1 + 1 := by omega
        subst hkk
        apply hd
        refine ⟨m + 1, ?_⟩
        omega


variable {Fr : Frame} {q o N : ℕ}

/-- The summand of `V` (`e = 1`) and `W` (`e = 2`) of a two-term frame. -/
noncomputable def tm (p : ℕ) [Fact p.Prime] (q o e k : ℕ) : ZMod p :=
  (invResidue p k) ^ e - (q : ZMod p) ^ e * (invResidue p (q * k - o)) ^ e

theorem good_S (e : ℕ) (he : 0 < e) (hq0 : 0 < q) (ho : o < q) (hqp : q < p)
    (hN : N ≤ p * p) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) :
    ∀ a, a < N → Good p (Cval e q o (p % q) (a / p) ((q * a - o) / p))
      (∑ k ∈ Icc 1 a, tm p q o e k) := by
  intro a
  induction a with
  | zero =>
    intro _
    have : Cval e q o (p % q) (0 / p) ((q * 0 - o) / p) = 0 := by
      simp [Cval, harm, poleSum]
    rw [this]; simpa using (Good.zero (ℓ := p))
  | succ a ih =>
    intro ha
    have hp : 0 < p := by omega
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hC : Cval e q o (p % q) ((a + 1) / p) ((q * (a + 1) - o) / p) =
        Cval e q o (p % q) (a / p) ((q * a - o) / p) +
          ((if p ∣ a + 1 then 1 / (((a + 1) / p : ℕ) : ℚ) ^ e else 0) -
            (q : ℚ) ^ e *
              (if p ∣ q * (a + 1) - o then 1 / (((q * (a + 1) - o) / p : ℕ) : ℚ) ^ e else 0)) := by
      unfold Cval
      rw [harm_step, pole_step a e hq0 ho hqp]
      ring
    rw [hC]
    refine (ih (by omega)).add ?_
    have hpos : 0 < q * (a + 1) - o := by
      have : q * (a + 1) = q * a + q := Nat.mul_succ q a
      omega
    have h1 : ¬ p ^ 2 ∣ a + 1 := by
      intro h
      have := Nat.le_of_dvd (by omega) h
      nlinarith
    exact (good_inc e he (by omega) h1).sub
      (((Good.natCast (ℓ := p) q).pow' e).mul (good_inc e he hpos (hsq (a + 1) (by omega) ha)))

theorem dv_eq (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    (twoTermPoleData T hN hsq hnorm hnorm0).dv k = tm p q o 1 k := by
  have e1 := good_scaled' (p := p) (n := k) (by omega) (not_sq_dvd_of_lt (by omega) (by nlinarith))
  have e2 := good_scaled' (p := p) (n := q * k - o) (T.pos hk1) (hsq k hk1 hk)
  have g := (e1.sub ((Good.natCast (ℓ := p) q).mul e2)).congr' (x' := (p : ℚ) * Fr.Delta k) (by
    rw [T.delta_eq k hk1, T.cast_sub hk1]; ring)
  have := g.eq
  show red p ((p : ℚ) * Fr.Delta k) = _
  rw [this]; simp [tm]

theorem sv_eq (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {k : ℕ} (hk1 : 1 ≤ k) (hk : k < N) :
    (twoTermPoleData T hN hsq hnorm hnorm0).sv k = tm p q o 2 k := by
  have e1 := good_scaled' (p := p) (n := k) (by omega) (not_sq_dvd_of_lt (by omega) (by nlinarith))
  have e2 := good_scaled' (p := p) (n := q * k - o) (T.pos hk1) (hsq k hk1 hk)
  have g := ((e1.pow' 2).sub (((Good.natCast (ℓ := p) q).pow' 2).mul (e2.pow' 2))).congr'
    (x' := (p : ℚ) ^ 2 * Fr.Dsq k) (by
      rw [T.dsq_eq k hk1, T.cast_sub hk1]
      have : ((q : ℚ) * k - o) ≠ 0 := by
        have := T.pos hk1
        have h := T.cast_sub (Fr := Fr) (q := q) (o := o) hk1
        rw [← h]; exact_mod_cast this.ne'
      have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp)
  have := g.eq
  show red p ((p : ℚ) ^ 2 * Fr.Dsq k) = _
  rw [this]; simp [tm]

/-- **Closed form of `V`.** -/
theorem good_V (T : TwoTermData Fr q o) (hqp : q < p) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {a : ℕ} (ha : a < N) :
    Good p (Cval 1 q o (p % q) (a / p) ((q * a - o) / p))
      ((twoTermPoleData T hN hsq hnorm hnorm0).V a) := by
  have hg := good_S (p := p) 1 one_pos (by have := T.o_pos; have := T.o_lt; omega) T.o_lt hqp hN
    hsq a ha
  refine hg.congr ?_
  unfold PoleData.V
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  exact (dv_eq T hN hsq hnorm hnorm0 hk.1 (by omega)).symm

/-- **Closed form of `W`.** -/
theorem good_W (T : TwoTermData Fr q o) (hqp : q < p) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {a : ℕ} (ha : a < N) :
    Good p (Cval 2 q o (p % q) (a / p) ((q * a - o) / p))
      ((twoTermPoleData T hN hsq hnorm hnorm0).W a) := by
  have hg := good_S (p := p) 2 (by norm_num) (by have := T.o_pos; have := T.o_lt; omega) T.o_lt
    hqp hN hsq a ha
  refine hg.congr ?_
  unfold PoleData.W
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  exact (sv_eq T hN hsq hnorm hnorm0 hk.1 (by omega)).symm

end CatalanCore.Uniform.Content.UFFamily
