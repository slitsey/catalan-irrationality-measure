module

public import CatalanFrames.P6.NV.Entries

/-!
# P6 NV: middle-node entries modulo `ℓ = 6t+1` (WP11)

The singular term `Δ_K` (`K = 2t+1`, `3K - 2 = ℓ`) reduces `ℓ Δ_K ≡ 6`, `ℓ² D_K ≡ 18`.
-/

@[expose] public section

open Finset CatalanCore

namespace CatalanFrames.P6.NV

open CatalanFrames.P6

variable {ℓ t : ℕ} [Fact ℓ.Prime] (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
include hl ht

lemma K_ne : ((2 * t + 1 : ℕ) : ZMod ℓ) ≠ 0 := zne (by omega) (by omega) (by omega)

lemma K21_ne : 2 * ((2 * t + 1 : ℕ) : ZMod ℓ) - 1 ≠ 0 := by
  have := zne (ℓ := ℓ) (n := 4 * t + 1) (by omega) (by omega) (by omega)
  have e : 2 * ((2 * t + 1 : ℕ) : ZMod ℓ) - 1 = ((4 * t + 1 : ℕ) : ZMod ℓ) := by
    push_cast; ring
  rwa [e]

lemma deltaK_good : Good ℓ ((ℓ : ℚ) * p6Frame.Delta (2 * t + 1)) 6 := by
  have hq := ell_q hl ht
  set kq : ℚ := ((2 * t + 1 : ℕ) : ℚ) with hkq
  have h3 : 3 * kq - 2 = ℓ := by rw [hq, hkq]; push_cast; ring
  have hk0 : kq ≠ 0 := by rw [hkq]; positivity
  have h21 : 2 * kq - 1 ≠ 0 := by
    rw [hkq]; push_cast; intro h; have : (0 : ℚ) ≤ t := t.cast_nonneg; linarith
  have hl0 : (ℓ : ℚ) ≠ 0 := by rw [hq]; positivity
  have e : (ℓ : ℚ) * p6Frame.Delta (2 * t + 1) =
      (ℓ : ℚ) * (1 / kq) + 6 - (ℓ : ℚ) * (6 / (2 * kq - 1)) := by
    rw [Delta_eq (2 * t + 1) (by omega), ← hkq, h3]
    field_simp
  rw [e]
  have g1 : Good ℓ (1 / kq) (1 / ((2 * t + 1 : ℕ) : ZMod ℓ)) :=
    Good.one.div (Good.natCast _) (K_ne hl ht)
  have g21 : Good ℓ (2 * kq - 1) (2 * ((2 * t + 1 : ℕ) : ZMod ℓ) - 1) :=
    (Good.mul (Good.ofNat 2) (Good.natCast _)).sub Good.one
  have g2 := (Good.ofNat 6).div g21 (K21_ne hl ht)
  have := ((g1.ell_mul).add (Good.ofNat 6)).sub g2.ell_mul
  exact this.congr (by ring)

lemma dsqK_good : Good ℓ ((ℓ : ℚ) ^ 2 * p6Frame.Dsq (2 * t + 1)) 18 := by
  have hq := ell_q hl ht
  set kq : ℚ := ((2 * t + 1 : ℕ) : ℚ) with hkq
  have h3 : 3 * kq - 2 = ℓ := by rw [hq, hkq]; push_cast; ring
  have hk0 : kq ≠ 0 := by rw [hkq]; positivity
  have h21 : 2 * kq - 1 ≠ 0 := by
    rw [hkq]; push_cast; intro h; have : (0 : ℚ) ≤ t := t.cast_nonneg; linarith
  have hl0 : (ℓ : ℚ) ≠ 0 := by rw [hq]; positivity
  have e : (ℓ : ℚ) ^ 2 * p6Frame.Dsq (2 * t + 1) =
      (ℓ : ℚ) * ((ℓ : ℚ) * (1 / kq ^ 2)) + 18 - (ℓ : ℚ) * ((ℓ : ℚ) * (12 / (2 * kq - 1) ^ 2)) := by
    rw [Dsq_eq (2 * t + 1) (by omega), ← hkq, h3]
    field_simp
  rw [e]
  have g1 : Good ℓ (1 / kq ^ 2) (1 / ((2 * t + 1 : ℕ) : ZMod ℓ) ^ 2) :=
    Good.one.div ((Good.natCast _).pow' 2) (pow_ne_zero 2 (K_ne hl ht))
  have g21 : Good ℓ (2 * kq - 1) (2 * ((2 * t + 1 : ℕ) : ZMod ℓ) - 1) :=
    (Good.mul (Good.ofNat 2) (Good.natCast _)).sub Good.one
  have g2 := (Good.ofNat 12).div (g21.pow' 2) (pow_ne_zero 2 (K21_ne hl ht))
  have := ((g1.ell_mul.ell_mul).add (Good.ofNat 18)).sub g2.ell_mul.ell_mul
  exact this.congr (by ring)

lemma lowmid_good {a b : ℕ} (ha : a ≤ 2 * t) (hb1 : 2 * t + 1 ≤ b) (hb2 : b ≤ 3 * t) :
    Good ℓ ((ℓ : ℚ) * p6Frame.Mn a b) (1 / (6 * ((b : ZMod ℓ) - a))) := by
  have h : a < b := by omega
  have g36 : Good ℓ (1 / 36 : ℚ) (1 / 36) := Good.one.div (Good.ofNat 36) (n36_ne hl ht)
  have hK : 2 * t + 1 ∈ Ioc a b := Finset.mem_Ioc.2 ⟨by omega, by omega⟩
  have hS : ∑ k ∈ Ioc a b, p6Frame.Delta k =
      p6Frame.Delta (2 * t + 1) + ∑ k ∈ (Ioc a b).erase (2 * t + 1), p6Frame.Delta k :=
    (Finset.add_sum_erase _ _ hK).symm
  have gE := Good.sum (ℓ := ℓ) ((Ioc a b).erase (2 * t + 1)) (fun k => p6Frame.Delta k)
    (fun k => Tri (finv ℓ) t k) fun k hk => by
      have h1 := Finset.mem_erase.1 hk
      have h2 := Finset.mem_Ioc.1 h1.2
      exact delta_good hl ht (by omega) (by omega) h1.1
  have hne : (b : ZMod ℓ) - a ≠ 0 :=
    sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) h.ne')
  have gd : Good ℓ (1 / ((b : ℚ) - a)) (1 / ((b : ZMod ℓ) - a)) :=
    Good.one.div ((Good.natCast b).sub (Good.natCast a)) hne
  have g := (g36.mul gd).mul ((deltaK_good hl ht).add gE.ell_mul)
  rw [Mn_off h, hS]
  refine (g.congr' (by ring)).congr ?_
  have h6 := six_ne hl ht
  have h36 := n36_ne hl ht
  field_simp
  ring

lemma midmid_diag_good {a : ℕ} (ha1 : 2 * t + 1 ≤ a) (ha2 : a ≤ 3 * t) :
    Good ℓ ((ℓ : ℚ) ^ 2 * p6Frame.Mn a a) (-(1 / 2)) := by
  have g36 : Good ℓ (1 / 36 : ℚ) (1 / 36) := Good.one.div (Good.ofNat 36) (n36_ne hl ht)
  have hK : 2 * t + 1 ∈ Icc 1 a := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hS : ∑ k ∈ Icc 1 a, p6Frame.Dsq k =
      p6Frame.Dsq (2 * t + 1) + ∑ k ∈ (Icc 1 a).erase (2 * t + 1), p6Frame.Dsq k :=
    (Finset.add_sum_erase _ _ hK).symm
  have gE := Good.sum (ℓ := ℓ) ((Icc 1 a).erase (2 * t + 1)) (fun k => p6Frame.Dsq k)
    (fun k => Tri (finv2 ℓ) t k) fun k hk => by
      have h1 := Finset.mem_erase.1 hk
      have h2 := Finset.mem_Icc.1 h1.2
      exact dsq_good hl ht h2.1 (by omega) h1.1
  have g := g36.neg.mul ((dsqK_good hl ht).add gE.ell_mul.ell_mul)
  rw [Mn_diag, hS]
  refine (g.congr' (by ring)).congr ?_
  have h36 := n36_ne hl ht
  have h2 := two_ne hl ht
  field_simp
  norm_num

lemma midmid_off_good {a b : ℕ} (ha1 : 2 * t + 1 ≤ a) (h : a < b) (hb2 : b ≤ 3 * t) :
    Good ℓ ((ℓ : ℚ) ^ 2 * p6Frame.Mn a b) 0 := by
  have g36 : Good ℓ (1 / 36 : ℚ) (1 / 36) := Good.one.div (Good.ofNat 36) (n36_ne hl ht)
  have gs := Good.sum (ℓ := ℓ) (Ioc a b) (fun k => p6Frame.Delta k)
    (fun k => Tri (finv ℓ) t k) fun k hk => by
      have h2 := Finset.mem_Ioc.1 hk
      exact delta_good hl ht (by omega) (by omega) (by omega)
  have hne : (b : ZMod ℓ) - a ≠ 0 :=
    sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) h.ne')
  have gd : Good ℓ (1 / ((b : ℚ) - a)) (1 / ((b : ZMod ℓ) - a)) :=
    Good.one.div ((Good.natCast b).sub (Good.natCast a)) hne
  have g := ((g36.mul gd).mul gs).ell_mul.ell_mul
  rw [Mn_off h]
  exact g.congr' (by ring)

end CatalanFrames.P6.NV
