module

public import CatalanLambda.Mirror.NVMod

@[expose] public section

open Finset Matrix

namespace CatalanLambda.Mirror

section Entries
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

lemma N0n_diag (a : ℕ) :
    N0n a a = ∑ k ∈ Icc 1 a, (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2) := by
  unfold N0n
  rw [if_pos rfl]

lemma N0n_comm (a b : ℕ) : N0n a b = N0n b a := by
  by_cases h : a = b
  · subst h; rfl
  · unfold N0n
    rw [if_neg h, if_neg (Ne.symm h), min_comm, max_comm]

lemma good_T (hlK : ℓ + 3 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    Good ℓ (3 / ((k : ℚ) * (4 * (k : ℚ) - 3)))
      (3 / ((k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 3))) := by
  have hk := k_ne hlK hk0 hkl hkK
  exact (Good.ofNat 3).div ((Good.natCast k).mul (((Good.ofNat 4).mul (Good.natCast k)).sub
    (Good.ofNat 3))) (mul_ne_zero hk.1 hk.2)

lemma good_off (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (hab : a < b) (hbl : b < ℓ)
    (hK : ∀ k ∈ Ioc a b, k ≠ K) :
    Good ℓ (N0n a b) ((1 / (16 * ((b : ZMod ℓ) - a))) *
      ∑ k ∈ Ioc a b, 3 / ((k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 3))) := by
  rw [N0n_lt hab]
  have hd : (b : ZMod ℓ) - a ≠ 0 := sub_ne_zero.2 (natCast_ne_natCast hbl (by omega) hab.ne')
  refine Good.mul (Good.one.div ((Good.ofNat 16).mul ((Good.natCast b).sub (Good.natCast a)))
    (mul_ne_zero (sixteen_ne hlK) hd)) (Good.sum _ _ _ ?_)
  intro k hk
  have := Finset.mem_Ioc.1 hk
  exact good_T hlK (by omega) (by omega) (hK k hk)

lemma entry_ll_off (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (hab : a < b) (hb : b < K) :
    Good ℓ (N0n a b) (-(G ℓ K a b) / 16) := by
  have hKl : K ≤ ℓ := by omega
  refine (good_off hlK hab (by omega) (fun k hk => by have := Finset.mem_Ioc.1 hk; omega)).congr ?_
  have h16 := sixteen_ne hlK
  have hd : (b : ZMod ℓ) - a ≠ 0 :=
    sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) hab.ne')
  rw [sumT hlK hab.le hb]
  have hG : G ℓ K a b = (U ℓ K a - U ℓ K b) / ((b : ZMod ℓ) - a) :=
    eq_div_of_mul_eq hd (by rw [mul_comm]; exact G_off hlK (by omega) hb)
  rw [hG]
  field_simp
  ring

lemma good_g (hlK : ℓ + 3 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    Good ℓ (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2)
      (1 / (16 * (k : ZMod ℓ) ^ 2) - 1 / (4 * (k : ZMod ℓ) - 3) ^ 2) := by
  have hk := k_ne hlK hk0 hkl hkK
  exact (Good.one.div ((Good.ofNat 16).mul ((Good.natCast k).pow' 2))
    (mul_ne_zero (sixteen_ne hlK) (pow_ne_zero 2 hk.1))).sub
    (Good.one.div ((((Good.ofNat 4).mul (Good.natCast k)).sub (Good.ofNat 3)).pow' 2)
    (pow_ne_zero 2 hk.2))

lemma entry_ll_diag (hlK : ℓ + 3 = 4 * K) {a : ℕ} (ha : a < K) :
    Good ℓ (N0n a a) ((-cc ℓ K - G ℓ K a a) / 16) := by
  rw [N0n_diag, ← diag_eq hlK ha]
  refine Good.sum _ _ _ ?_
  intro k hk
  have := Finset.mem_Icc.1 hk
  exact good_g hlK (by omega) (by omega) (by omega)

lemma entry_hh_off (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (hKa : K ≤ a) (hab : a < b) (hbl : b < ℓ) :
    Good ℓ ((ℓ : ℚ) * ℓ * N0n a b) 0 := by
  have h := good_off hlK hab hbl (fun k hk => by have := Finset.mem_Ioc.1 hk; omega)
  have := ((Good.natCast ℓ).mul (Good.natCast ℓ)).mul h
  simpa using this

lemma entry_hh_diag (hlK : ℓ + 3 = 4 * K) {a : ℕ} (hKa : K ≤ a) (hal : a < ℓ)
    {r : ℚ} {rb : ZMod ℓ} (hr : Good ℓ r rb) :
    Good ℓ ((ℓ : ℚ) * ℓ * (r + N0n a a)) (-1) := by
  have hK1 : 1 ≤ K := by omega
  have hKmem : K ∈ Icc 1 a := Finset.mem_Icc.2 ⟨hK1, hKa⟩
  have hlQ : (ℓ : ℚ) = 4 * K - 3 := by
    have : ((ℓ : ℚ)) + 3 = 4 * K := by exact_mod_cast hlK
    linarith
  have hK0 : (K : ℚ) ≠ 0 := by positivity
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    exact this.ne'
  have e : (ℓ : ℚ) * ℓ * (r + N0n a a) =
      (ℓ : ℚ) * ℓ * r + (((ℓ : ℚ) * ℓ) / (16 * (K : ℚ) ^ 2) - 1 +
        ∑ k ∈ (Icc 1 a).erase K, (ℓ : ℚ) * ℓ *
          (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2)) := by
    rw [N0n_diag, ← Finset.add_sum_erase _ _ hKmem, mul_add, mul_add, ← Finset.mul_sum, ← hlQ]
    field_simp
    ring
  rw [e]
  have h16 := sixteen_ne hlK
  have hKz : (K : ZMod ℓ) ≠ 0 := natCast_ne_zero' (by omega) (by omega)
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
      (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2)) 0 := by
    have := Good.sum ((Icc 1 a).erase K) (fun k : ℕ => (ℓ : ℚ) * ℓ *
      (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2))
      (fun _ => (0 : ZMod ℓ)) (by
        intro k hk
        obtain ⟨hkK, hk'⟩ := Finset.mem_erase.1 hk
        have hk'' := Finset.mem_Icc.1 hk'
        have := ((Good.natCast ℓ).mul (Good.natCast ℓ)).mul (good_g hlK (by omega) (by omega) hkK)
        simpa [hl0] using this)
    simpa using this
  have := g1.add (g2.add g3)
  simpa using this

/-- low-high entries -/
lemma entry_lh (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (ha : a < K) (hKb : K ≤ b) (hbl : b < ℓ) :
    Good ℓ ((ℓ : ℚ) * N0n a b) (1 / (4 * ((b : ZMod ℓ) - a))) := by
  have hab : a < b := by omega
  have hK1 : 1 ≤ K := by omega
  have hKmem : K ∈ Ioc a b := Finset.mem_Ioc.2 ⟨ha, hKb⟩
  have hlQ : (ℓ : ℚ) = 4 * K - 3 := by
    have : ((ℓ : ℚ)) + 3 = 4 * K := by exact_mod_cast hlK
    linarith
  have hK0 : (K : ℚ) ≠ 0 := by positivity
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by
    have : (0 : ℚ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).pos
    exact this.ne'
  have e : (ℓ : ℚ) * N0n a b = (1 / (16 * ((b : ℚ) - (a : ℚ)))) *
      (3 / (K : ℚ) + ∑ k ∈ (Ioc a b).erase K, (ℓ : ℚ) *
        (3 / ((k : ℚ) * (4 * (k : ℚ) - 3)))) := by
    rw [N0n_lt hab, ← Finset.add_sum_erase _ _ hKmem, ← hlQ, ← Finset.mul_sum]
    field_simp
    simp only [mul_comm (4 : ℚ)]
  rw [e]
  have h4 := four_ne (ℓ := ℓ) hlK
  have h16 := sixteen_ne hlK
  have hd : (b : ZMod ℓ) - a ≠ 0 := sub_ne_zero.2 (natCast_ne_natCast hbl (by omega) hab.ne')
  have hl0 : ((ℓ : ℕ) : ZMod ℓ) = 0 := ZMod.natCast_self ℓ
  have hKz : (K : ZMod ℓ) ≠ 0 := natCast_ne_zero' (by omega) (by omega)
  have g1 : Good ℓ (3 / (K : ℚ)) (3 / (K : ZMod ℓ)) :=
    (Good.ofNat 3).div (Good.natCast K) hKz
  have g3 : Good ℓ (∑ k ∈ (Ioc a b).erase K, (ℓ : ℚ) *
        (3 / ((k : ℚ) * (4 * (k : ℚ) - 3)))) 0 := by
    have := Good.sum ((Ioc a b).erase K) (fun k : ℕ => (ℓ : ℚ) *
        (3 / ((k : ℚ) * (4 * (k : ℚ) - 3)))) (fun _ => (0 : ZMod ℓ)) (by
        intro k hk
        obtain ⟨hkK, hk'⟩ := Finset.mem_erase.1 hk
        have hk'' := Finset.mem_Ioc.1 hk'
        have := (Good.natCast ℓ).mul (good_T hlK (by omega) (by omega) hkK)
        simpa [hl0] using this)
    simpa using this
  have := (Good.one.div ((Good.ofNat 16).mul ((Good.natCast b).sub (Good.natCast a)))
    (mul_ne_zero h16 hd)).mul (g1.add g3)
  refine this.congr ?_
  rw [add_zero, K_eq hlK]
  have h3 := three_ne hlK
  have h34 : (3 / 4 : ZMod ℓ) ≠ 0 := div_ne_zero h3 h4
  field_simp
  ring

end Entries

end CatalanLambda.Mirror
