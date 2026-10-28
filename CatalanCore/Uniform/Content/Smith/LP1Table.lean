module

public import CatalanCore.Uniform.Content.Smith.TwoTerm2
public import CatalanCore.Arith.Hybrid.DefC5Mat
public import CatalanCore.Uniform.Content.Smith.LP2Entries

@[expose] public section

/-!
# LP1 (last pole cell) for a general two-term frame: the label table under the D2 weights

`LP1Hyp` is the hypothesis package: `p < r`, `r < p + k` (`U = [r - p, k)` is nonempty), the corrected
PoleData condition for nodes `t < N = r + 2m ≤ 2p`.  The D2 weights `wC` are `0` on `U`, `1` on the
rest of the core and on high zone nodes, and `2` on low zone nodes (`z < p + k`).

`TcG` is the reduction of `p^{wC A + wC B} Mn A B`: regular formula for weight `0`, the cross
formula `(nr (B-A))⁻¹ Σ res` for weight `1`, `nr⁻¹ Σ res` on `B - A = p` for weight `2`, `0` otherwise;
`Σ res` is the step function `singG` of the pole-load residues `v, 1, v₂` at `k, p, p + k`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N r m k j : ℕ}

structure LP1Hyp (Fr : Frame) (p q o r m k j : ℕ) [Fact p.Prime] : Prop where
  cfg : TTCfg2 Fr p q o (r + 2 * m) k j
  hrp : p ≤ r
  hUk : r < p + k
  p5 : 5 ≤ p

/-- Sum of the pole-load residues over the singular indices in `(A, B]`. -/
def singG (p k : ℕ) (v v2 : ZMod p) (A B : ℕ) : ZMod p :=
  (if A < k ∧ k ≤ B then v else 0) +
    ((if A < p ∧ p ≤ B then 1 else 0) + (if A < p + k ∧ p + k ≤ B then v2 else 0))

def singDG (p k : ℕ) (v : ZMod p) (A : ℕ) : ZMod p :=
  (if k ≤ A then -v ^ 2 else 0) + (if p ≤ A then 1 else 0)

/-- The residue of `p^w Mn A B`, `A < B`. -/
noncomputable def TCgenG (p k : ℕ) [Fact p.Prime] (nr v v2 : ZMod p) (w A B : ℕ) : ZMod p :=
  if w = 0 then nr⁻¹ * (((B : ZMod p) - A)⁻¹ * (F2 k B - F2 k A))
  else if w = 1 then (nr * ((B : ZMod p) - A))⁻¹ * singG p k v v2 A B
  else if w = 2 ∧ B - A = p then nr⁻¹ * singG p k v v2 A B else 0

noncomputable def TCDgenG (p k : ℕ) [Fact p.Prime] (nr v : ZMod p) (w A : ℕ) : ZMod p :=
  if w = 0 then nr⁻¹ * E2 k A else if w = 2 then -nr⁻¹ * singDG p k v A else 0

lemma good_zero_pow {x : ℚ} (hx : x ∈ S p) {e : ℕ} (he : 1 ≤ e) :
    Good p ((p : ℚ) ^ e * x) 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have hpm : (p : ℚ) ∈ S p := (Good.natCast (ℓ := p) p).1
  have hm : (p : ℚ) ^ d * x ∈ S p := (S p).mul_mem ((S p).pow_mem hpm d) hx
  have := (good_red hm).ell_mul
  refine this.congr' ?_
  ring

lemma TTCfg2.V_diff (C : TTCfg2 Fr p q o N k j) {A B : ℕ} (hAB : A < B) (hBN : B < N) :
    C.D.V B - C.D.V A = singG p k (vk p q j) (vk2 p q j) A B := by
  rw [C.V_val hBN, C.V_val (by omega)]
  unfold singG
  split_ifs <;> first | (exfalso; omega) | ring

theorem TTCfg2.good_TCgen (C : TTCfg2 Fr p q o N k j) {w A B : ℕ} (hAB : A < B) (hBN : B < N)
    (h0 : w = 0 → B < k) (h1 : w = 1 → B - A ≠ p) :
    Good p ((p : ℚ) ^ w * Fr.Mn A B)
      (TCgenG p k (red p Fr.norm) (vk p q j) (vk2 p q j) w A B) := by
  have hN2 := C.sg.hN2
  have hp5 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hNpp : N < p * p := by
    have : 3 ≤ p := by have := C.sg.hqp; have := C.tt.o_lt; have := C.tt.o_pos; omega
    nlinarith
  by_cases hw0 : w = 0
  · subst hw0
    rw [pow_zero, one_mul]
    unfold TCgenG; rw [if_pos rfl]
    exact C.good_Mn_reg hAB hBN (h0 rfl)
  by_cases hw1 : w = 1
  · subst hw1
    rw [pow_one]
    unfold TCgenG; rw [if_neg (by omega), if_pos rfl]
    have hBA := h1 rfl
    have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) hBA
    have g := C.D.good_cross_ordered hAB hBN hd
    rw [C.V_diff hAB hBN] at g
    exact g
  -- w ≥ 2
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
  by_cases hBA : B - A = p
  · have g := C.D.good_square hNpp hAB hBN
    rw [hBA, TTSing.invRes_self (Fact.out : p.Prime), C.V_diff hAB hBN] at g
    by_cases hw2 : w' = 0
    · subst hw2
      unfold TCgenG; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hBA⟩]
      refine g.congr' (by ring) |>.congr ?_
      ring
    · unfold TCgenG
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have := good_zero_pow g.1 (e := w') (by omega)
      exact this.congr' (by ring)
  · have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) hBA
    have g := C.D.good_cross_ordered hAB hBN hd
    unfold TCgenG
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := good_zero_pow g.1 (e := w' + 1) (by omega)
    exact this.congr' (by ring)

theorem TTCfg2.good_TCDgen (C : TTCfg2 Fr p q o N k j) {w A : ℕ} (hAN : A < N) (hApk : A < p + k)
    (hw : w = 0 ∨ w = 2) (h0 : w = 0 → A < k) :
    Good p ((p : ℚ) ^ w * Fr.Mn A A)
      (TCDgenG p k (red p Fr.norm) (vk p q j) w A) := by
  rcases hw with rfl | rfl
  · rw [pow_zero, one_mul]
    unfold TCDgenG; rw [if_pos rfl]
    exact C.good_Mn_diag_reg hAN (h0 rfl)
  · have hNpp : N < p * p := by
      have h2 := C.sg.hN2; have hqp := C.sg.hqp; have := C.tt.o_lt; have := C.tt.o_pos
      have : 3 ≤ p := by omega
      nlinarith
    have g := C.D.good_diagonal hAN
    rw [C.W_val hAN hApk] at g
    unfold TCDgenG
    rw [if_neg (by norm_num), if_pos rfl]
    refine g.congr ?_
    unfold singDG
    ring

end CatalanCore.Uniform.Content.Smith
