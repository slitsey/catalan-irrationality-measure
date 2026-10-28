module

public import CatalanCore.Arith.Hybrid.PeriodicEntries
public import CatalanCore.Arith.Hybrid.DefBFinal

@[expose] public section

/-!
# Pole data of a general two-term frame `ψ(z+1) - ψ(z+a/q)` (corrected PoleData condition)

For a frame `F` whose increments are `Δ_t = 1/t - q/(q t - o)` and `D_t = 1/t² - q²/(q t - o)²`
(`o = q - a`, any norm), the periodic pole interface `Periodic.PoleData` holds at a prime `p` for
nodes `t < N` under the **corrected** condition

  `N ≤ p²`   and   `p² ∤ q t - o`  for `1 ≤ t < N`

(every crossed pole is then simple; `p ∤ q` is used only through `q < p`).  This replaces the
earlier hypothesis `p > q² + qN/p`.  When the singular indices below `N` are exactly `k` (with
`q k = j p + o`) and `p`, the prefixes of the pole loads are the step functions

  `V(A) = 0 (A < k),  v_k (k ≤ A < p),  v_k + 1 (p ≤ A)`,  `v_k = -q/j`,
  `W(A) = 0 (A < k),  -v_k² (k ≤ A < p),  1 - v_k² (p ≤ A)`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

/-- Two-term frame data: `Δ_t = 1/t - q/(q t - o)`, `D_t = 1/t² - q²/(q t - o)²`, `0 < o < q`. -/
structure TwoTermData (Fr : Frame) (q o : ℕ) : Prop where
  o_pos : 0 < o
  o_lt : o < q
  delta_eq : ∀ t : ℕ, 1 ≤ t →
    Fr.Delta t = 1 / (t : ℚ) - (q : ℚ) / ((q : ℚ) * t - (o : ℚ))
  dsq_eq : ∀ t : ℕ, 1 ≤ t →
    Fr.Dsq t = 1 / (t : ℚ) ^ 2 - (q : ℚ) ^ 2 / ((q : ℚ) * t - (o : ℚ)) ^ 2

section Local

variable {p : ℕ} [Fact p.Prime]

lemma TwoTermData.cast_sub {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {t : ℕ} (ht : 1 ≤ t) :
    (((q * t - o : ℕ)) : ℚ) = (q : ℚ) * t - (o : ℚ) := by
  have : o ≤ q * t := by have := T.o_lt; nlinarith
  rw [Nat.cast_sub this]; push_cast; ring

lemma TwoTermData.pos {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {t : ℕ} (ht : 1 ≤ t) :
    0 < q * t - o := by
  have := T.o_lt; have : q ≤ q * t := Nat.le_mul_of_pos_right q ht
  omega

lemma natCast_ne_zero_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact h

lemma inv_nat_mem {n : ℕ} (h : ¬ p ∣ n) : ((n : ℚ))⁻¹ ∈ S p :=
  ((Good.natCast (ℓ := p) n).inv (natCast_ne_zero_of_not_dvd h)).1

/-- `p / n` is `p`-integral when `p² ∤ n`. -/
lemma p_div_nat_mem {n : ℕ} (hn : 0 < n) (h2 : ¬ p ^ 2 ∣ n) : (p : ℚ) / n ∈ S p := by
  by_cases hd : p ∣ n
  · obtain ⟨n', rfl⟩ := hd
    have hn' : ¬ p ∣ n' := fun h => h2 (by rw [pow_two]; exact mul_dvd_mul_left p h)
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : (p : ℚ) / ((p * n' : ℕ) : ℚ) = ((n' : ℕ) : ℚ)⁻¹ := by
      push_cast
      have hn0 : (n' : ℚ) ≠ 0 := by
        have : n' ≠ 0 := by rintro rfl; simp at hn
        exact_mod_cast this
      field_simp
    rw [this]; exact inv_nat_mem hn'
  · have : (p : ℚ) / n = (p : ℚ) * ((n : ℚ))⁻¹ := by rw [div_eq_mul_inv]
    rw [this]
    exact (S p).mul_mem (Good.natCast (ℓ := p) p).1 (inv_nat_mem hd)

end Local


section Pole

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N : ℕ}

/-- The two singular residue classes: `p ∣ t` or `p ∣ q t - o`. -/
def ttSing (p q o : ℕ) (t : ℤ) : Prop := (p : ℤ) ∣ t ∨ (p : ℤ) ∣ (q : ℤ) * t - o

lemma ttSing_periodic (p q o : ℕ) (t j : ℤ) : ttSing p q o (t + j * p) ↔ ttSing p q o t := by
  unfold ttSing
  have h1 : (p : ℤ) ∣ t + j * p ↔ (p : ℤ) ∣ t := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - j, by linear_combination hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k + j, by linear_combination hk⟩
  have h2 : (p : ℤ) ∣ (q : ℤ) * (t + j * p) - o ↔ (p : ℤ) ∣ (q : ℤ) * t - o := by
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k - q * j, by linear_combination hk⟩
    · rintro ⟨k, hk⟩; exact ⟨k + q * j, by linear_combination hk⟩
  rw [h1, h2]

lemma ttSing_nat (T : TwoTermData Fr q o) {t : ℕ} (ht : 1 ≤ t) :
    ttSing p q o (t : ℤ) ↔ p ∣ t ∨ p ∣ q * t - o := by
  unfold ttSing
  have e : ((q : ℤ) * t - o) = ((q * t - o : ℕ) : ℤ) := by
    have : o ≤ q * t := by have := T.o_lt; nlinarith
    rw [Nat.cast_sub this]; push_cast; ring
  rw [e, Int.natCast_dvd_natCast, Int.natCast_dvd_natCast]

lemma not_sq_dvd_of_lt {t : ℕ} (ht : 0 < t) (hN : t < p * p) : ¬ p ^ 2 ∣ t := by
  intro h
  have := Nat.le_of_dvd ht h
  nlinarith

/-- **PoleData of a two-term frame** under the corrected condition. -/
noncomputable def twoTermPoleData (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : Periodic.PoleData Fr p N where
  singular := ttSing p q o
  periodic := ttSing_periodic p q o
  norm_mem := hnorm
  norm_ne := hnorm0
  delta_mem := fun t ht htN => by
    have h1 : (p : ℚ) / t ∈ S p :=
      p_div_nat_mem (by omega) (not_sq_dvd_of_lt (by omega) (by omega))
    have h2 : (p : ℚ) / ((q * t - o : ℕ) : ℚ) ∈ S p := p_div_nat_mem (T.pos ht) (hsq t ht htN)
    rw [T.delta_eq t ht]
    have e : (p : ℚ) * (1 / (t : ℚ) - (q : ℚ) / ((q : ℚ) * t - (o : ℚ))) =
        (p : ℚ) / t - (q : ℚ) * ((p : ℚ) / ((q * t - o : ℕ) : ℚ)) := by
      rw [T.cast_sub ht]; ring
    rw [e]
    exact (S p).sub_mem h1 ((S p).mul_mem (Good.natCast (ℓ := p) q).1 h2)
  dsq_mem := fun t ht htN => by
    have h1 : (p : ℚ) / t ∈ S p :=
      p_div_nat_mem (by omega) (not_sq_dvd_of_lt (by omega) (by omega))
    have h2 : (p : ℚ) / ((q * t - o : ℕ) : ℚ) ∈ S p := p_div_nat_mem (T.pos ht) (hsq t ht htN)
    rw [T.dsq_eq t ht]
    have e : (p : ℚ) ^ 2 * (1 / (t : ℚ) ^ 2 - (q : ℚ) ^ 2 / ((q : ℚ) * t - (o : ℚ)) ^ 2) =
        ((p : ℚ) / t) ^ 2 - (q : ℚ) ^ 2 * ((p : ℚ) / ((q * t - o : ℕ) : ℚ)) ^ 2 := by
      rw [T.cast_sub ht]
      generalize (q : ℚ) * t - (o : ℚ) = d
      ring
    rw [e]
    exact (S p).sub_mem ((S p).pow_mem h1 2)
      ((S p).mul_mem ((S p).pow_mem (Good.natCast (ℓ := p) q).1 2) ((S p).pow_mem h2 2))
  regular_delta := fun t ht htN hs => by
    rw [ttSing_nat T ht] at hs
    push Not at hs
    rw [T.delta_eq t ht, ← T.cast_sub ht]
    have e : 1 / (t : ℚ) - (q : ℚ) / ((q * t - o : ℕ) : ℚ) =
        ((t : ℚ))⁻¹ - (q : ℚ) * (((q * t - o : ℕ) : ℚ))⁻¹ := by ring
    rw [e]
    exact (S p).sub_mem (inv_nat_mem hs.1)
      ((S p).mul_mem (Good.natCast (ℓ := p) q).1 (inv_nat_mem hs.2))
  regular_dsq := fun t ht htN hs => by
    rw [ttSing_nat T ht] at hs
    push Not at hs
    rw [T.dsq_eq t ht, ← T.cast_sub ht]
    have e : 1 / (t : ℚ) ^ 2 - (q : ℚ) ^ 2 / ((q * t - o : ℕ) : ℚ) ^ 2 =
        (((t : ℚ))⁻¹) ^ 2 - (q : ℚ) ^ 2 * ((((q * t - o : ℕ) : ℚ))⁻¹) ^ 2 := by
      rw [one_div, inv_pow, div_eq_mul_inv, inv_pow]
    rw [e]
    exact (S p).sub_mem ((S p).pow_mem (inv_nat_mem hs.1) 2)
      ((S p).mul_mem ((S p).pow_mem (Good.natCast (ℓ := p) q).1 2)
        ((S p).pow_mem (inv_nat_mem hs.2) 2))

end Pole


section Vals

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N k j : ℕ}

/-- The two-singular-index configuration: `q k = j p + o`; the singular indices below `N ≤ p + k`
are exactly `k` and `p`. -/
structure TTSing (p q o N k j : ℕ) : Prop where
  hqp : q < p
  hk : q * k = j * p + o
  hk0 : 0 < k
  hkp : k < p
  hj0 : 0 < j
  hNk : N ≤ p + k

/-- The residue `v_k = -q/j` of the pole at `k` (`= -1/κ`). -/
def vk (p q j : ℕ) : ZMod p := -((q : ZMod p) * ((j : ZMod p))⁻¹)

lemma TTSing.hjq (T : TwoTermData Fr q o) (S : TTSing p q o N k j) : j < q := by
  have h1 := S.hk; have h2 := T.o_pos; have h3 := S.hkp; have h4 := T.o_lt
  by_contra h
  push Not at h
  have e2 : q * p ≤ j * p := Nat.mul_le_mul_right p h
  have e1 : q * k < q * p := Nat.mul_lt_mul_of_pos_left h3 (by omega)
  linarith

lemma TTSing.hjp (T : TwoTermData Fr q o) (S : TTSing p q o N k j) : j < p := by
  have := S.hjq T; have := S.hqp; omega

lemma TTSing.j_ne (T : TwoTermData Fr q o) (S : TTSing p q o N k j) : (j : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
  have := Nat.le_of_dvd S.hj0 h; have := S.hjp T; omega

lemma TTSing.k_ne (S : TTSing p q o N k j) : (k : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
  have := Nat.le_of_dvd S.hk0 h; have := S.hkp; omega

lemma TTSing.q_ne (T : TwoTermData Fr q o) (S : TTSing p q o N k j) : (q : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; intro h
  have := Nat.le_of_dvd (by have := T.o_pos; have := T.o_lt; omega) h; have := S.hqp; omega

lemma TTSing.vk_ne (T : TwoTermData Fr q o) (S : TTSing p q o N k j) : vk p q j ≠ 0 := by
  unfold vk
  exact neg_ne_zero.2 (mul_ne_zero (S.q_ne T) (inv_ne_zero (S.j_ne T)))

/-- In `[1, N)` the singular indices are exactly `k` and `p`. -/
lemma TTSing.sing_iff (T : TwoTermData Fr q o) (S : TTSing p q o N k j) {t : ℕ} (ht : 1 ≤ t)
    (htN : t < N) : ttSing p q o (t : ℤ) ↔ t = k ∨ t = p := by
  have hp := (Fact.out : p.Prime)
  have hk := S.hk; have hkp := S.hkp; have hNk := S.hNk; have ho := T.o_pos
  have hoq := T.o_lt
  have hoqt : o ≤ q * t := by nlinarith
  constructor
  · intro h
    rw [ttSing_nat T ht] at h
    rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
    · right
      rcases c with _ | _ | c
      · omega
      · omega
      · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
        omega
    · left
      have h1 : (q : ℤ) * t - o = p * c := by
        have := congrArg (fun x : ℕ => (x : ℤ)) hc
        simp only [Nat.cast_mul] at this
        rw [Nat.cast_sub hoqt] at this; push_cast at this; linarith
      have h2 : (q : ℤ) * k = j * p + o := by exact_mod_cast hk
      have hd : (p : ℤ) ∣ (q : ℤ) * ((t : ℤ) - k) := ⟨c - j, by linear_combination h1 - h2⟩
      have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      rcases hpz.dvd_or_dvd hd with h3 | h3
      · have : p ∣ q := Int.natCast_dvd_natCast.1 h3
        have := Nat.le_of_dvd (by omega) this
        have := S.hqp; omega
      · obtain ⟨c', hc'⟩ := h3
        have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
        have hlt : (t : ℤ) < p + k := by exact_mod_cast (by omega : t < p + k)
        have hgt : (-(p : ℤ)) < (t : ℤ) - k := by
          have : (k : ℤ) < p := by exact_mod_cast hkp
          have : (0 : ℤ) < t := by exact_mod_cast (by omega : 0 < t)
          linarith
        rcases lt_trichotomy c' 0 with hneg | hzero | hpos
        · exfalso; nlinarith
        · rw [hzero, mul_zero] at hc'; omega
        · exfalso; nlinarith
  · rintro (h | h)
    · rw [ttSing_nat T ht, h]; right
      rw [Nat.sub_eq_of_eq_add hk]; exact dvd_mul_left p j
    · rw [ttSing_nat T ht, h]; left; exact dvd_rfl

end Vals

end CatalanCore.Uniform.Content.Smith
