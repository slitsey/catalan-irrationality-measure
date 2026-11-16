module

public import CatalanCore.Zeta5.Content.Normaliser
public import CatalanCore.Zeta5.Content.Count
public import CatalanCore.Zeta5.Content.Cells
public import CatalanCore.Zeta5.CostIn.Inner

@[expose] public section

/-!
# ZC32: the extended exponent band by band

With `K = 40 n` and `x = K/p`:

* `LpC_small` (`p M ≤ K`): `|L_p^C| ≤ 7 K ⌊log_p 5K⌋`;
* `LpC_inner` (`K/M < p ≤ K/3`): `-L_p^C ≤ p R(x) + 190 M³ + 30 M − [K < 200 p] p g_ref(x)`
  (ZC17 and ZC27);
* `LpC_outer` (`K/3 < p ≤ 2h`, `p ≥ 101`):
  `-L_p^C ≤ p E(x) − [p ≤ K] p [E(x) − R(x)]₊ + 86`, with `E(x) = x T₀(1/x)` (ZC19).
-/

namespace CatalanCore.Zeta5.Content

open Apery CatalanCore.Zeta5.CostOut CatalanCore.Zeta5.Profile CatalanCore.Zeta5.Sum

/-- Small primes: `|L_p^C| ≤ 7 K ⌊log_p 5K⌋`. -/
lemma LpC_small {M n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (h1 : p * M ≤ 40 * n) :
    |(LpC M n p : ℝ)| ≤ 7 * ((40 * n : ℕ) : ℝ) * (Nat.log p (5 * (40 * n)) : ℝ) := by
  have : Fact p.Prime := ⟨hp⟩
  have hL : LpC M n p = LsmallN n p := by unfold LpC; rw [if_pos h1]
  rw [hL]
  unfold LsmallN
  have hv : padicValNat p 24 ≤ Nat.log p (200 * n) :=
    (padicValNat_le_nat_log 24).trans (Nat.log_mono_right (by omega))
  have e5 : 5 * (40 * n) = 200 * n := by ring
  rw [e5]
  have hvR : (padicValNat p 24 : ℝ) ≤ (Nat.log p (200 * n) : ℝ) := by exact_mod_cast hv
  have hL0 : (0 : ℝ) ≤ (Nat.log p (200 * n) : ℝ) := Nat.cast_nonneg _
  have hv0 : (0 : ℝ) ≤ (padicValNat p 24 : ℝ) := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  generalize padicValNat p 24 = v at hvR hv0 ⊢
  generalize Nat.log p (200 * n) = L at hvR hL0 ⊢
  push_cast
  rw [abs_neg, abs_of_nonneg (by positivity)]
  have := mul_le_mul_of_nonneg_left hvR (by positivity : (0 : ℝ) ≤ 37 * n)
  nlinarith

/-- Inner primes (ZC17 with the parity gain ZC27). -/
lemma LpC_inner {M n p : ℕ} (hp : p.Prime) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n)
    (hpM : 40 * n < p * M) (hp3 : 3 * p ≤ 40 * n) :
    -(LpC M n p : ℝ) ≤ (p : ℝ) * Rg (((40 * n : ℕ) : ℝ) / p) + 190 * (M : ℝ) ^ 3 + 30 * M
      - (if 40 * n < 200 * p then (p : ℝ) * gref (((40 * n : ℕ) : ℝ) / p) else 0) := by
  have h17 := CostIn.zc17 hp hM hK hpM hp3
  have hL : (LpC M n p : ℝ) = (LpKM M n p : ℝ) +
      (if 40 * n ≤ 200 * p then (kpar p n (4 * M + 10) : ℝ) else 0) := by
    unfold LpC LpKM
    rw [if_neg (not_le.mpr hpM), if_pos hp3, if_neg (not_le.mpr hpM), if_pos hp3]
    split_ifs <;> push_cast <;> ring
  rw [abs_le] at h17
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  rw [hL]
  by_cases h200 : 40 * n < 200 * p
  · rw [if_pos h200.le, if_pos h200]
    have H : InnerHyp p n M (4 * M + 10) := ⟨hp, hM, hK, hpM, hp3, by omega, by omega⟩
    have hk := kpar_ge H
    linarith [h17.1]
  · rw [if_neg h200]
    have : (0 : ℝ) ≤ (if 40 * n ≤ 200 * p then (kpar p n (4 * M + 10) : ℝ) else 0) := by
      split_ifs
      · exact Nat.cast_nonneg _
      · exact le_rfl
    have : (0 : ℝ) ≤ 30 * M := by positivity
    linarith [h17.1]

/-- On the outer band the extended exponent is the best outer cost. -/
lemma LpC_outer_eq {M n p : ℕ} (hp : p.Prime) (h101 : 101 ≤ p) (hM : 3 ≤ M)
    (h1 : 40 * n < 3 * p) : -(LpC M n p : ℝ) = wBest n p := by
  have hs : ¬ p * M ≤ 40 * n := by
    intro h
    have : p * 3 ≤ p * M := Nat.mul_le_mul_left p hM
    omega
  have hi : ¬ 3 * p ≤ 40 * n := by omega
  by_cases hE : ExtHyp p n
  · have hL : LpC M n p = vSK n p + max (gammaOut n p) ⌊gammaExt hE⌋ := by
      unfold LpC; rw [if_neg hs, if_neg hi, dif_pos hE]
    obtain ⟨z, hz⟩ := Apery.ExtHyp.ext_gamma_int hE
    have hge : gammaExt hE = (z : ℚ) := by unfold gammaExt; exact hz
    rw [hL, wBest_eq hE, hge, Int.floor_intCast]
    push_cast
    ring
  · have hpK : ¬ p ≤ 40 * n := fun h => hE ⟨hp, h101, h1, h⟩
    have hL : LpC M n p = vSK n p := by
      unfold LpC LpKM; rw [if_neg hs, if_neg hi, dif_neg hE, if_neg hs, if_neg hi, if_neg hpK]
    rw [hL]
    unfold wBest wOut
    rw [dif_neg hE, if_neg hpK]
    push_cast
    ring

/-- `K W_out(p/K) = p E(K/p) − [p ≤ K] p [E(K/p) − R(K/p)]₊` on `K/3 < p`. -/
lemma K_Wout {n p : ℕ} (hn : 1 ≤ n) (hp0 : 0 < p) (h1 : 40 * n < 3 * p) :
    (40 * n : ℝ) * Wout ((p : ℝ) / (40 * n)) =
      (p : ℝ) * Ex (((40 * n : ℕ) : ℝ) / p)
        - (if p ≤ 40 * n then
            (p : ℝ) * max 0 (Ex (((40 * n : ℕ) : ℝ) / p) - Rg (((40 * n : ℕ) : ℝ) / p))
          else 0) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast hp0
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  set x : ℝ := ((40 * n : ℕ) : ℝ) / p with hxdef
  have hx0 : 0 < x := by rw [hxdef]; push_cast; positivity
  have hx3 : x < 3 := by
    rw [hxdef, div_lt_iff₀ hP]
    have : ((40 * n : ℕ) : ℝ) < ((3 * p : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; linarith
  have hθ : (p : ℝ) / (40 * n) = 1 / x := by rw [hxdef]; push_cast; field_simp
  have hK : (40 * n : ℝ) = p * x := by rw [hxdef]; push_cast; field_simp
  unfold Wout
  rw [hθ, one_div_one_div, T0_inv hx0 hx3]
  by_cases hpK : p ≤ 40 * n
  · have hle : 1 / x ≤ 1 := by
      rw [div_le_one hx0, hxdef, le_div_iff₀ hP, one_mul]; exact_mod_cast hpK
    rw [if_pos hle, if_pos hpK, hK]
    have hxi : 0 < 1 / x := by positivity
    rcases le_total (Ex x) (Rg x) with h | h
    · rw [min_eq_left (mul_le_mul_of_nonneg_left h hxi.le), max_eq_left (by linarith)]
      field_simp; ring
    · rw [min_eq_right (mul_le_mul_of_nonneg_left h hxi.le), max_eq_right (by linarith)]
      field_simp; ring
  · have hle : ¬ 1 / x ≤ 1 := by
      rw [div_le_one hx0, hxdef, le_div_iff₀ hP, one_mul]; exact_mod_cast hpK
    rw [if_neg hle, if_neg hpK, hK]
    field_simp; ring

/-- Outer primes (ZC19). -/
lemma LpC_outer {M n p : ℕ} (hp : p.Prime) (h101 : 101 ≤ p) (hn : 1 ≤ n) (hM : 3 ≤ M)
    (h1 : 40 * n < 3 * p) (h2 : p ≤ 2 * (37 * n)) :
    -(LpC M n p : ℝ) ≤ (p : ℝ) * Ex (((40 * n : ℕ) : ℝ) / p)
        - (if p ≤ 40 * n then
            (p : ℝ) * max 0 (Ex (((40 * n : ℕ) : ℝ) / p) - Rg (((40 * n : ℕ) : ℝ) / p))
          else 0) + 86 := by
  have h := zc19_outer_cost hp h101 hn h1 h2
  rw [K_Wout hn hp.pos h1, ← LpC_outer_eq hp h101 hM h1, abs_le] at h
  linarith [h.2]

end CatalanCore.Zeta5.Content
