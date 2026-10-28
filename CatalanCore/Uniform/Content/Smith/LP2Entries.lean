module

public import CatalanCore.Uniform.Content.Smith.LP2Table

@[expose] public section

/-!
# LP2 entry table for a general two-term frame

`LP2Hyp` is the hypothesis package of Theorem LP2 (`r < p`, `k ≤ r`, `r + 2m ≤ p + k`, the
corrected PoleData condition).  `LP2Hyp.good_Tg` and `LP2Hyp.good_Td` say that the entries of
`Full(X)` scaled by the D4 potentials `uPot` are `p`-integral with the residues `Tg`, `Td` of
`LP2Table`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N r m k j : ℕ}

/-- Hypotheses of Theorem LP2: primes just above `r`. -/
structure LP2Hyp (Fr : Frame) (p q o r m k j : ℕ) [Fact p.Prime] : Prop where
  cfg : TTCfg Fr p q o (r + 2 * m) k j
  hrp : r < p
  hkr : k ≤ r
  p5 : 5 ≤ p

lemma TTCfg.hN' (C : TTCfg Fr p q o N k j) : N < p * p := by
  have := C.sg.hNk; have := C.sg.hkp; have := (Fact.out : p.Prime).two_le
  nlinarith

lemma good_zero_of_cross {x : ℚ} (hx : (p : ℚ) * x ∈ S p) {e : ℕ} (he : 2 ≤ e) :
    Good p ((p : ℚ) ^ e * x) 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 2 := ⟨e - 2, by omega⟩
  have hpm : (p : ℚ) ∈ S p := (Good.natCast (ℓ := p) p).1
  have hm : (p : ℚ) ^ d * ((p : ℚ) * x) ∈ S p := (S p).mul_mem ((S p).pow_mem hpm d) hx
  have := (good_red hm).ell_mul
  refine this.congr' ?_
  ring

lemma uPot_ge_one {A : ℕ} (hAk : k ≤ A) : 1 ≤ uPot p r k A := by
  unfold uPot; split_ifs <;> omega

lemma TTSing.invRes_self (hp : p.Prime) : invResidue p p = 1 := by
  unfold invResidue
  rw [if_pos dvd_rfl, Nat.div_self hp.pos]; simp

theorem LP2Hyp.good_Tg (H : LP2Hyp Fr p q o r m k j) {A B : ℕ} (hAB : A < B)
    (hBN : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k B) * Fr.Mn A B)
      (Tg p k (red p Fr.norm) (vk p q j) A B) := by
  have C := H.cfg
  have hkp := C.sg.hkp
  have hNk := C.sg.hNk
  have hrp := H.hrp
  have hkr := H.hkr
  have hAN : A < r + 2 * m := by omega
  by_cases hBk : B < k
  · have hA0 : uPot p r k A = 0 := by
      unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
    have hB0 : uPot p r k B = 0 := by
      unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
    rw [hA0, hB0, add_zero, pow_zero, one_mul]
    unfold Tg; rw [if_pos hBk]
    exact C.good_Mn_reg hAB hBN hBk
  · by_cases hAk : A < k
    · have hA0 : uPot p r k A = 0 := by
        unfold uPot; rw [if_pos (by omega), if_neg (by omega)]
      by_cases hBp : B < p
      · have hB1 : uPot p r k B = 1 := by
          unfold uPot; split_ifs <;> omega
        rw [hA0, hB1, zero_add, pow_one]
        have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
        have g := C.D.good_cross_ordered hAB hBN hd
        refine g.congr ?_
        rw [C.V_val hBN, C.V_val hAN]
        unfold Tg
        rw [if_neg hBk, if_pos hAk, if_pos hBp, if_pos (by omega : k ≤ B),
          if_neg (by omega : ¬ k ≤ A), if_neg (by omega : ¬ p ≤ B), if_neg (by omega : ¬ p ≤ A)]
        rw [mul_inv]; ring
      · have hB2 : uPot p r k B = 2 := by
          unfold uPot; rw [if_neg (by omega)]; rw [if_pos (by omega)]
        rw [hA0, hB2, zero_add]
        by_cases hBA : B - A = p
        · have g := C.D.good_square C.hN' hAB hBN
          refine g.congr ?_
          rw [hBA, TTSing.invRes_self (Fact.out : p.Prime), C.V_val hBN, C.V_val hAN]
          unfold Tg
          rw [if_neg hBk, if_pos hAk, if_neg hBp, if_pos hBA, if_pos (by omega : k ≤ B),
            if_neg (by omega : ¬ k ≤ A), if_pos (by omega : p ≤ B), if_neg (by omega : ¬ p ≤ A)]
          ring
        · have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) hBA
          have g := C.D.good_cross hAN hBN hd
          have g2 := g.ell_mul
          refine (g2.congr' (by ring)).congr ?_
          unfold Tg
          rw [if_neg hBk, if_pos hAk, if_neg hBp, if_neg hBA]
    · have h1 := uPot_ge_one (p := p) (r := r) (k := k) (A := A) (by omega)
      have h2 := uPot_ge_one (p := p) (r := r) (k := k) (A := B) (by omega)
      have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
      have g := C.D.good_cross hAN hBN hd
      have := good_zero_of_cross g.1 (e := uPot p r k A + uPot p r k B) (by omega)
      refine this.congr ?_
      unfold Tg
      rw [if_neg hBk, if_neg hAk]

theorem LP2Hyp.good_Td (H : LP2Hyp Fr p q o r m k j) {A : ℕ} (hAr : A < r) :
    Good p ((p : ℚ) ^ (uPot p r k A + uPot p r k A) * Fr.Mn A A)
      (Td p k (red p Fr.norm) (vk p q j) A) := by
  have C := H.cfg
  have hkp := C.sg.hkp
  have hNk := C.sg.hNk
  have hrp := H.hrp
  have hAN : A < r + 2 * m := by omega
  by_cases hAk : A < k
  · have hA0 : uPot p r k A = 0 := by
      unfold uPot; rw [if_pos hAr, if_neg (by omega)]
    rw [hA0, add_zero, pow_zero, one_mul]
    unfold Td; rw [if_pos hAk]
    exact C.good_Mn_diag_reg hAN hAk
  · have hA1 : uPot p r k A = 1 := by
      unfold uPot; rw [if_pos hAr, if_pos (by omega)]
    rw [hA1]
    have g := C.D.good_diagonal hAN
    refine (g.congr' (by norm_num)).congr ?_
    rw [C.W_val hAN]
    unfold Td
    rw [if_neg hAk, if_pos (by omega : k ≤ A), if_neg (by omega : ¬ p ≤ A)]
    ring

end CatalanCore.Uniform.Content.Smith
