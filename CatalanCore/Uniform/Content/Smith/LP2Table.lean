module

public import CatalanCore.Uniform.Content.Smith.TwoTermVals
public import CatalanCore.Uniform.Content.Smith.PoleTransfer

@[expose] public section

/-!
# The label-level reduction table of LP2 for a general two-term frame

For nodes `A < B < N = r + 2m` and the D4 potentials `uPot`, the scaled entry
`p^{uPot A + uPot B} · Mn A B` is `p`-integral with the reduction `Tg A B` (`Td A` on the diagonal):

* `B < k` (regular pair, `uPot = 0`): `nr⁻¹ (B-A)⁻¹ (F(B) - F(A))`;
* `A < k ≤ B < p`: `nr⁻¹ (B-A)⁻¹ v_k`;   `A < k`, `p ≤ B`, `B - A = p`: `nr⁻¹ (v_k + 1)`;
* everything else: `0`.

`Td A = nr⁻¹ E(A)` for `A < k` and `nr⁻¹ v_k²` for `k ≤ A`.  Here `nr` is the reduction of the
frame norm.  All inputs come from `PoleData.good_cross`, `good_square`, `good_diagonal` and the pole
loads `V`, `W` of `TwoTermVals`.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o N k j : ℕ}

/-- The label table for `A < B`. -/
noncomputable def Tg (p k : ℕ) [Fact p.Prime] (nr v : ZMod p) (A B : ℕ) : ZMod p :=
  if B < k then nr⁻¹ * (((B : ZMod p) - A)⁻¹ * (F2 k B - F2 k A))
  else if A < k then
    (if B < p then nr⁻¹ * (((B : ZMod p) - A)⁻¹ * v)
     else if B - A = p then nr⁻¹ * (v + 1) else 0)
  else 0

/-- The diagonal table. -/
noncomputable def Td (p k : ℕ) [Fact p.Prime] (nr v : ZMod p) (A : ℕ) : ZMod p :=
  if A < k then nr⁻¹ * E2 k A else nr⁻¹ * v ^ 2

lemma Mn_ord (Fr : Frame) {A B : ℕ} (h : A < B) :
    Fr.Mn A B = (1 / Fr.norm) * (1 / ((B : ℚ) - A)) * ∑ t ∈ Ioc A B, Fr.Delta t := by
  unfold Frame.Mn
  rw [if_neg h.ne, min_eq_left h.le, max_eq_right h.le]

lemma Mn_dg (Fr : Frame) (A : ℕ) : Fr.Mn A A = -(1 / Fr.norm) * ∑ t ∈ Icc 1 A, Fr.Dsq t := by
  unfold Frame.Mn; rw [if_pos rfl]

lemma F2_sub {k A B : ℕ} (h : A ≤ B) :
    F2 (p := p) k B - F2 (p := p) k A =
      ∑ t ∈ Ioc A B, (((t : ZMod p))⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) := by
  unfold F2
  rw [Icc_eq_Ioc, Icc_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le A) h]
  ring

lemma TTCfg.cast_d (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) :
    (((q * t - o : ℕ)) : ZMod p) = (q : ZMod p) * ((t : ZMod p) - (k : ZMod p)) := by
  have hoqt : o ≤ q * t := by have := C.tt.o_lt; nlinarith
  have hk : ((q * k : ℕ) : ZMod p) = ((j * p + o : ℕ) : ZMod p) := by rw [C.sg.hk]
  push_cast at hk
  rw [ZMod.natCast_self, mul_zero, zero_add] at hk
  rw [Nat.cast_sub hoqt]; push_cast
  linear_combination hk

lemma TTCfg.nonsing (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N) (htk : t < k) :
    ¬ p ∣ t ∧ ¬ p ∣ q * t - o := by
  have h := (C.sg.sing_iff C.tt ht htN)
  have hkp := C.sg.hkp
  have : ¬ ttSing p q o (t : ℤ) := by
    intro hs; rcases h.1 hs with h1 | h1 <;> omega
  rw [ttSing_nat C.tt ht] at this
  push Not at this
  exact this

lemma TTCfg.good_Delta_reg (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N)
    (htk : t < k) :
    Good p (Fr.Delta t) (((t : ZMod p))⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) := by
  obtain ⟨h1, h2⟩ := C.nonsing ht htN htk
  have hq := C.sg.q_ne C.tt
  have e : Fr.Delta t = ((t : ℚ))⁻¹ - (q : ℚ) * (((q * t - o : ℕ) : ℚ))⁻¹ := by
    rw [C.tt.delta_eq t ht, C.tt.cast_sub ht]; ring
  rw [e]
  have g1 := (Good.natCast (ℓ := p) t).inv (natCast_ne_zero_of_not_dvd h1)
  have g2 := (Good.natCast (ℓ := p) (q * t - o)).inv (natCast_ne_zero_of_not_dvd h2)
  have g := g1.sub ((Good.natCast (ℓ := p) q).mul g2)
  refine g.congr ?_
  rw [C.cast_d ht, mul_inv, mul_inv_cancel_left₀ hq]

lemma TTCfg.good_Dsq_reg (C : TTCfg Fr p q o N k j) {t : ℕ} (ht : 1 ≤ t) (htN : t < N)
    (htk : t < k) :
    Good p (Fr.Dsq t)
      ((((t : ZMod p))⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2) := by
  obtain ⟨h1, h2⟩ := C.nonsing ht htN htk
  have hq := C.sg.q_ne C.tt
  have e : Fr.Dsq t = (((t : ℚ))⁻¹) ^ 2 - (q : ℚ) ^ 2 * ((((q * t - o : ℕ) : ℚ))⁻¹) ^ 2 := by
    rw [C.tt.dsq_eq t ht, ← C.tt.cast_sub ht, one_div, inv_pow, div_eq_mul_inv, inv_pow]
  rw [e]
  have g1 := ((Good.natCast (ℓ := p) t).inv (natCast_ne_zero_of_not_dvd h1)).pow' 2
  have g2 := ((Good.natCast (ℓ := p) (q * t - o)).inv (natCast_ne_zero_of_not_dvd h2)).pow' 2
  have g := g1.sub (((Good.natCast (ℓ := p) q).pow' 2).mul g2)
  refine g.congr ?_
  rw [C.cast_d ht, mul_inv, mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq, one_pow,
    one_mul]

lemma TTCfg.good_norm (C : TTCfg Fr p q o N k j) : Good p Fr.norm (red p Fr.norm) :=
  good_red C.hnm

/-- Regular off-diagonal pair. -/
lemma TTCfg.good_Mn_reg (C : TTCfg Fr p q o N k j) {A B : ℕ} (hAB : A < B) (hBN : B < N)
    (hBk : B < k) :
    Good p (Fr.Mn A B)
      ((red p Fr.norm)⁻¹ * (((B : ZMod p) - A)⁻¹ * (F2 k B - F2 k A))) := by
  have hkp := C.sg.hkp
  have hd : ((B : ZMod p) - A) ≠ 0 := zmod_sub_ne_zero_of_lt hAB (by omega)
  rw [Mn_ord Fr hAB]
  have gn := C.good_norm.inv C.hnm0
  have gd := ((Good.natCast (ℓ := p) B).sub (Good.natCast (ℓ := p) A)).inv hd
  have gs : Good p (∑ t ∈ Ioc A B, Fr.Delta t)
      (∑ t ∈ Ioc A B, (((t : ZMod p))⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹)) :=
    Good.sum _ _ _ fun t ht => by
      have := mem_Ioc.1 ht
      exact C.good_Delta_reg (by omega) (by omega) (by omega)
  have g := (gn.mul gd).mul gs
  rw [F2_sub hAB.le]
  refine (g.congr' ?_).congr ?_
  · simp only [one_div]
  · ring

/-- Regular diagonal. -/
lemma TTCfg.good_Mn_diag_reg (C : TTCfg Fr p q o N k j) {A : ℕ} (hAN : A < N) (hAk : A < k) :
    Good p (Fr.Mn A A) ((red p Fr.norm)⁻¹ * E2 k A) := by
  rw [Mn_dg]
  have gn := (C.good_norm.inv C.hnm0).neg
  have gs : Good p (∑ t ∈ Icc 1 A, Fr.Dsq t)
      (∑ t ∈ Icc 1 A, ((((t : ZMod p))⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2)) :=
    Good.sum _ _ _ fun t ht => by
      have := mem_Icc.1 ht
      exact C.good_Dsq_reg this.1 (by omega) (by omega)
  have g := gn.mul gs
  refine (g.congr' ?_).congr ?_
  · simp only [one_div]
  · unfold E2
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

end CatalanCore.Uniform.Content.Smith
