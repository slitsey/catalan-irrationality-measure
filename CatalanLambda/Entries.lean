module

public import CatalanLambda.Mod

@[expose] public section

open Finset Matrix

namespace CatalanLambda

section Entries
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

lemma M0n_lt {a b : ℕ} (h : a < b) :
    M0n a b = -(1 / (4 * ((b : ℚ) - (a : ℚ)))) *
      ∑ k ∈ Ioc a b, 1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)) := by
  unfold M0n
  rw [if_neg h.ne, min_eq_left h.le, max_eq_right h.le]

lemma M0n_diag (a : ℕ) :
    M0n a a = -∑ k ∈ Icc 1 a, (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2) := by
  unfold M0n
  rw [if_pos rfl]

lemma M0n_comm (a b : ℕ) : M0n a b = M0n b a := by
  by_cases h : a = b
  · subst h; rfl
  · unfold M0n
    rw [if_neg h, if_neg (Ne.symm h), min_comm, max_comm]

lemma good_T (hlK : ℓ + 1 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    Good ℓ (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))
      (1 / (4 * (k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 1))) := by
  have hk := k_ne hlK hk0 hkl hkK
  have h4 := four_ne (ℓ := ℓ) hlK
  exact Good.one.div (((Good.ofNat 4).mul (Good.natCast k)).mul
    (((Good.ofNat 4).mul (Good.natCast k)).sub Good.one)) (mul_ne_zero (mul_ne_zero h4 hk.1) hk.2)

lemma good_off (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (hab : a < b) (hbl : b < ℓ)
    (hK : ∀ k ∈ Ioc a b, k ≠ K) :
    Good ℓ (M0n a b) (-(1 / (4 * ((b : ZMod ℓ) - a))) *
      ∑ k ∈ Ioc a b, 1 / (4 * (k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 1))) := by
  rw [M0n_lt hab]
  have h4 := four_ne (ℓ := ℓ) hlK
  have hd : (b : ZMod ℓ) - a ≠ 0 := sub_ne_zero.2 (natCast_ne_natCast hbl (by omega) hab.ne')
  refine Good.mul (Good.neg (Good.one.div ((Good.ofNat 4).mul ((Good.natCast b).sub (Good.natCast a)))
    (mul_ne_zero h4 hd))) (Good.sum _ _ _ ?_)
  intro k hk
  have := Finset.mem_Ioc.1 hk
  exact good_T hlK (by omega) (by omega) (hK k hk)

lemma G_comm (a b : ℕ) : G ℓ K a b = G ℓ K b a := by
  unfold G; exact Finset.sum_congr rfl fun t _ => by rw [mul_comm]

/-- low-low off-diagonal entries -/
lemma entry_ll_off (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (hab : a < b) (hb : b < K) :
    Good ℓ (M0n a b) (G ℓ K a b / 16) := by
  have hKl : K ≤ ℓ := by omega
  refine (good_off hlK hab (by omega) (fun k hk => by have := Finset.mem_Ioc.1 hk; omega)).congr ?_
  have h4 := four_ne (ℓ := ℓ) hlK
  have hd : (b : ZMod ℓ) - a ≠ 0 :=
    sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) hab.ne')
  rw [sumT hlK hab.le hb]
  have hG : G ℓ K a b = (U ℓ K a - U ℓ K b) / ((b : ZMod ℓ) - a) :=
    eq_div_of_mul_eq hd (by rw [mul_comm]; exact G_off hlK (by omega) hb)
  rw [hG]
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  field_simp
  ring

lemma Good.pow' {x : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) (n : ℕ) : Good ℓ (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using (Good.one (ℓ := ℓ))
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

lemma good_g (hlK : ℓ + 1 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    Good ℓ (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2)
      (1 / (16 * (k : ZMod ℓ) ^ 2) - 1 / (4 * (k : ZMod ℓ) - 1) ^ 2) := by
  have hk := k_ne hlK hk0 hkl hkK
  have h4 := four_ne (ℓ := ℓ) hlK
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  exact (Good.one.div ((Good.ofNat 16).mul ((Good.natCast k).pow' 2))
    (mul_ne_zero h16 (pow_ne_zero 2 hk.1))).sub
    (Good.one.div ((((Good.ofNat 4).mul (Good.natCast k)).sub Good.one).pow' 2)
    (pow_ne_zero 2 hk.2))

lemma entry_ll_diag (hlK : ℓ + 1 = 4 * K) {a : ℕ} (ha : a < K) :
    Good ℓ (M0n a a) ((cc ℓ K + G ℓ K a a) / 16) := by
  rw [M0n_diag, ← diag_eq hlK ha]
  refine Good.neg (Good.sum _ _ _ ?_)
  intro k hk
  have := Finset.mem_Icc.1 hk
  exact good_g hlK (by omega) (by omega) (by omega)

lemma entry_hh_off (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (hKa : K ≤ a) (hab : a < b) (hbl : b < ℓ) :
    Good ℓ ((ℓ : ℚ) * ℓ * M0n a b) 0 := by
  have h := good_off hlK hab hbl (fun k hk => by have := Finset.mem_Ioc.1 hk; omega)
  have := ((Good.natCast ℓ).mul (Good.natCast ℓ)).mul h
  simpa using this

lemma entry_hh_diag (hlK : ℓ + 1 = 4 * K) {a : ℕ} (hKa : K ≤ a) (hal : a < ℓ)
    {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) :
    Good ℓ ((ℓ : ℚ) * ℓ * (r + M0n a a)) 1 := by
  have hK1 : 1 ≤ K := by omega
  have hKmem : K ∈ Icc 1 a := Finset.mem_Icc.2 ⟨hK1, hKa⟩
  have hlQ : (ℓ : ℚ) = 4 * K - 1 := by
    have : ((ℓ : ℚ)) + 1 = 4 * K := by exact_mod_cast hlK
    linarith
  have hK0 : (K : ℚ) ≠ 0 := by positivity
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    exact this.ne'
  have e : (ℓ : ℚ) * ℓ * (r + M0n a a) =
      (ℓ : ℚ) * ℓ * r - (((ℓ : ℚ) * ℓ) / (16 * (K : ℚ) ^ 2) - 1 +
        ∑ k ∈ (Icc 1 a).erase K, (ℓ : ℚ) * ℓ *
          (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2)) := by
    rw [M0n_diag, ← Finset.add_sum_erase _ _ hKmem, ← Finset.mul_sum, ← hlQ]
    field_simp
    ring
  rw [e]
  have h4 := four_ne (ℓ := ℓ) hlK
  have hKz : (K : ZMod ℓ) ≠ 0 := natCast_ne_zero' (by omega) (by omega)
  have h16 : (16 : ZMod ℓ) ≠ 0 := by
    have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have hl0 : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  have g1 : Good ℓ ((ℓ : ℚ) * ℓ * r) 0 := by
    have := ((Good.natCast ℓ).mul (Good.natCast ℓ)).mul hr
    simpa [hl0] using this
  have g2 : Good ℓ (((ℓ : ℚ) * ℓ) / (16 * (K : ℚ) ^ 2) - 1) (-1) := by
    have := (((Good.natCast ℓ).mul (Good.natCast ℓ)).div
      ((Good.ofNat 16).mul ((Good.natCast K).pow' 2)) (mul_ne_zero h16 (pow_ne_zero 2 hKz))).sub
      (Good.one (ℓ := ℓ))
    simpa [hl0] using this
  have g3 : Good ℓ (∑ k ∈ (Icc 1 a).erase K, (ℓ : ℚ) * ℓ *
      (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2)) 0 := by
    have := Good.sum ((Icc 1 a).erase K) (fun k : ℕ => (ℓ : ℚ) * ℓ *
      (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 1) ^ 2))
      (fun _ => (0 : ZMod ℓ)) (by
        intro k hk
        obtain ⟨hkK, hk'⟩ := Finset.mem_erase.1 hk
        have hk'' := Finset.mem_Icc.1 hk'
        have := ((Good.natCast ℓ).mul (Good.natCast ℓ)).mul (good_g hlK (by omega) (by omega) hkK)
        simpa [hl0] using this)
    simpa using this
  have := g1.sub (g2.add g3)
  simpa using this

/-- low-high entries -/
lemma entry_lh (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (ha : a < K) (hKb : K ≤ b) (hbl : b < ℓ) :
    Good ℓ ((ℓ : ℚ) * M0n a b) (-(1 / (4 * ((b : ZMod ℓ) - a)))) := by
  have hab : a < b := by omega
  have hK1 : 1 ≤ K := by omega
  have hKmem : K ∈ Ioc a b := Finset.mem_Ioc.2 ⟨ha, hKb⟩
  have hlQ : (ℓ : ℚ) = 4 * K - 1 := by
    have : ((ℓ : ℚ)) + 1 = 4 * K := by exact_mod_cast hlK
    linarith
  have hK0 : (K : ℚ) ≠ 0 := by positivity
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    exact this.ne'
  have e : (ℓ : ℚ) * M0n a b = -(1 / (4 * ((b : ℚ) - (a : ℚ)))) *
      (1 / (4 * (K : ℚ)) + ∑ k ∈ (Ioc a b).erase K, (ℓ : ℚ) *
        (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))) := by
    rw [M0n_lt hab, ← Finset.add_sum_erase _ _ hKmem, ← Finset.mul_sum, ← hlQ]
    field_simp
  rw [e]
  have h4 := four_ne (ℓ := ℓ) hlK
  have hd : (b : ZMod ℓ) - a ≠ 0 := sub_ne_zero.2 (natCast_ne_natCast hbl (by omega) hab.ne')
  have hl0 : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  have hKz : (K : ZMod ℓ) ≠ 0 := natCast_ne_zero' (by omega) (by omega)
  have g1 : Good ℓ (1 / (4 * (K : ℚ))) 1 := by
    have := (Good.one (ℓ := ℓ)).div ((Good.ofNat 4).mul (Good.natCast K)) (mul_ne_zero h4 hKz)
    rwa [four_K hlK, div_one] at this
  have g3 : Good ℓ (∑ k ∈ (Ioc a b).erase K, (ℓ : ℚ) *
        (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))) 0 := by
    have := Good.sum ((Ioc a b).erase K) (fun k : ℕ => (ℓ : ℚ) *
        (1 / (4 * (k : ℚ) * (4 * (k : ℚ) - 1)))) (fun _ => (0 : ZMod ℓ)) (by
        intro k hk
        obtain ⟨hkK, hk'⟩ := Finset.mem_erase.1 hk
        have hk'' := Finset.mem_Ioc.1 hk'
        have := (Good.natCast ℓ).mul (good_T hlK (by omega) (by omega) hkK)
        simpa [hl0] using this)
    simpa using this
  have := (Good.neg (Good.one.div ((Good.ofNat 4).mul ((Good.natCast b).sub (Good.natCast a)))
    (mul_ne_zero h4 hd))).mul (g1.add g3)
  simpa using this

end Entries
end CatalanLambda
