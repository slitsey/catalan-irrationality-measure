module

public import CatalanCore.Lai.Construction
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Prime.Factorial
public import CatalanCore.Lai.Family
public import CatalanCore.Lai.NVCore

@[expose] public section

/-! # `CatalanCore.Lai.NV`: Theorem NV and Corollaries NV1, NV2 for Lai's `J_n` (ledger LN01-LN05). -/


/-!
# Lai's design: arithmetic of the weights and of the harmonic numbers at `ℓ = 9m + 1`
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai
open scoped Nat

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section Arith

theorem choose_high_mod {N0 μ : ℕ} (hN0 : N0 < ℓ) (hμ : μ < ℓ) :
    Nat.choose (ℓ + N0) (ℓ + μ) ≡ Nat.choose N0 μ [MOD ℓ] := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := ℓ + N0) (k := ℓ + μ) (p := ℓ)
  have e1 : (ℓ + N0) % ℓ = N0 := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hN0]
  have e2 : (ℓ + μ) % ℓ = μ := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hμ]
  have e3 : (ℓ + N0) / ℓ = 1 := by
    rw [Nat.add_div_left _ hℓ.out.pos, Nat.div_eq_of_lt hN0]
  have e4 : (ℓ + μ) / ℓ = 1 := by
    rw [Nat.add_div_left _ hℓ.out.pos, Nat.div_eq_of_lt hμ]
  rw [e1, e2, e3, e4, Nat.choose_self, mul_one] at h
  exact h

theorem not_dvd_choose_small {N0 μ : ℕ} (hN0 : N0 < ℓ) (hμ : μ ≤ N0) : ¬ ℓ ∣ Nat.choose N0 μ := by
  intro hd
  have hf : ℓ ∣ N0 ! := dvd_trans hd ⟨μ ! * (N0 - μ)!, by
    rw [← mul_assoc]; exact (Nat.choose_mul_factorial_mul_factorial hμ).symm⟩
  exact absurd ((Nat.Prime.dvd_factorial hℓ.out).1 hf) (not_le.2 hN0)

theorem dvd_choose_mid {N k : ℕ} (hk : k < ℓ) (hNk : N - k < ℓ) (hN : ℓ ≤ N) (hkN : k ≤ N) :
    ℓ ∣ Nat.choose N k := by
  have h1 : ℓ ∣ N ! := (Nat.Prime.dvd_factorial hℓ.out).2 hN
  rw [← Nat.choose_mul_factorial_mul_factorial hkN] at h1
  rcases (Nat.Prime.dvd_mul hℓ.out).1 h1 with h | h
  · rcases (Nat.Prime.dvd_mul hℓ.out).1 h with h | h
    · exact h
    · exact absurd ((Nat.Prime.dvd_factorial hℓ.out).1 h) (not_le.2 hk)
  · exact absurd ((Nat.Prime.dvd_factorial hℓ.out).1 h) (not_le.2 hNk)

variable {m : ℕ}

theorem laiCoef_mid (hℓ' : ℓ = 9 * m + 1) (hm : 1 ≤ m) {k : ℕ} (hk1 : 3 * m ≤ k) (hk2 : k < ℓ) :
    ℓ ^ 2 ∣ laiCoef (2 * m) k := by
  have h := dvd_choose_mid (ℓ := ℓ) (N := 6 * (2 * m)) (k := k) hk2 (by omega) (by omega) (by omega)
  unfold laiCoef
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h 2) _

theorem laiCoef_high (hℓ' : ℓ = 9 * m + 1) (hm : 1 ≤ m) {μ : ℕ} (hμ : μ < 3 * m) :
    ¬ ℓ ∣ laiCoef (2 * m) (ℓ + μ) := by
  unfold laiCoef
  intro hd
  rcases (Nat.Prime.dvd_mul hℓ.out).1 hd with h | h
  · have h1 := Nat.Prime.dvd_of_dvd_pow hℓ.out h
    have e : 6 * (2 * m) = ℓ + (3 * m - 1) := by omega
    rw [e] at h1
    have hm1 := choose_high_mod (ℓ := ℓ) (N0 := 3 * m - 1) (μ := μ) (by omega) (by omega)
    have h2 : ℓ ∣ Nat.choose (3 * m - 1) μ :=
      Nat.modEq_zero_iff_dvd.1 (hm1.symm.trans (Nat.modEq_zero_iff_dvd.2 h1))
    exact not_dvd_choose_small (by omega) (by omega) h2
  · have h1 := Nat.Prime.dvd_of_dvd_pow hℓ.out h
    have e : 2 * (2 * m) + (ℓ + μ) = ℓ + (4 * m + μ) := by omega
    rw [e] at h1
    have hm1 := choose_high_mod (ℓ := ℓ) (N0 := 4 * m + μ) (μ := μ) (by omega) (by omega)
    have h2 : ℓ ∣ Nat.choose (4 * m + μ) μ :=
      Nat.modEq_zero_iff_dvd.1 (hm1.symm.trans (Nat.modEq_zero_iff_dvd.2 h1))
    exact not_dvd_choose_small (by omega) (by omega) h2

end Arith

section Harmonic

variable (ℓ)

/-- `[ℓ ≤ j]` as an element of `ℤ_(ℓ)`. -/
def iota (j : ℕ) : LocRing ℓ := if ℓ ≤ j then 1 else 0

variable {ℓ}

theorem iota_of_lt {j : ℕ} (h : j < ℓ) : iota ℓ j = 0 := by simp [iota, not_le.2 h]

theorem iota_of_le {j : ℕ} (h : ℓ ≤ j) : iota ℓ j = 1 := by simp [iota, h]

/-- `H_k(r) = [ℓ ≤ k] ℓ^{-r} + (ℓ-integral)` for `k < 2ℓ`. -/
theorem Hq_decomp (r : ℕ) : ∀ k, k < 2 * ℓ →
    ∃ z : LocRing ℓ, Hq r k = ((iota ℓ k : LocRing ℓ) : ℚ) / (ℓ : ℚ) ^ r + (z : ℚ) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨0, by rw [iota_of_lt hℓ.out.pos]; simp [Hq]⟩
  | succ k ih =>
    intro hk
    obtain ⟨z, hz⟩ := ih (by omega)
    have hsucc : Hq r (k + 1) = Hq r k + 1 / ((k : ℚ) + 1) ^ r := by
      unfold Hq; rw [Finset.sum_range_succ]
    by_cases h : k + 1 = ℓ
    · refine ⟨z, ?_⟩
      have hk' : k < ℓ := by omega
      rw [hsucc, hz, iota_of_lt hk', iota_of_le (by omega)]
      have : ((k : ℚ) + 1) = (ℓ : ℚ) := by exact_mod_cast h
      rw [this]
      simp
      ring
    · have hnd : ¬ ℓ ∣ k + 1 := by
        intro hd
        obtain ⟨c, hc⟩ := hd
        have : c = 1 := by
          rcases c with _ | _ | c
          · omega
          · omega
          · exfalso; nlinarith
        subst this; omega
      have hmem : (1 / ((k : ℚ) + 1) ^ r) ∈ LocRing ℓ := by
        have := (LocRing ℓ).pow_mem (inv_natCast_mem_locRing (ℓ := ℓ) hnd) r
        convert this using 1
        push_cast
        rw [one_div, inv_pow]
      refine ⟨z + ⟨_, hmem⟩, ?_⟩
      have hi : iota ℓ (k + 1) = iota ℓ k := by
        unfold iota; split_ifs <;> first | rfl | omega
      rw [hsucc, hz, hi]
      push_cast
      ring

end Harmonic

end CatalanCore.Lai.NV


/-!
# Theorem NV for Lai's `J_n` (ledger LN01-LN03)

`ℓ = 9m + 1` prime, `n = 2m`.  For `(a, b, X) = (a'/ℓ, b, X'/ℓ³)` with `a', b, X' ∈ ℤ_(ℓ)` and
`ε = 3a' + 2b` a unit mod `ℓ`, `J_n(a, b, X) ≠ 0`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai
open scoped Nat

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section Eval

theorem eval_laiL (n : ℕ) (P : ℚ[X]) (a b x : ℚ) :
    MvPolynomial.eval ![a, b, x] (laiL n P) =
      nodeL (6 * n) (fun k => (laiCoef n k : ℚ)) (fun k => -3 * a * Hq 2 k - 2 * b * Hq 3 k)
        (fun k => laiH n k * (3 * a * Hq 2 k + 2 * b * Hq 3 k) +
          6 * (x - a * Hq 3 k - b * Hq 4 k)) P := by
  rw [nodeL_apply]
  unfold laiL laiU laiV
  simp only [map_sum, map_mul, map_add, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_succ]
  ring

theorem eval_laiJ (n : ℕ) (a b x : ℚ) :
    MvPolynomial.eval ![a, b, x] (laiJ n) =
      (∏ i ∈ range (3 * n), ((i ! : ℚ)) ^ 2)⁻¹ *
        (Matrix.of fun i j : Fin (3 * n) =>
          nodeL (6 * n) (fun k => (laiCoef n k : ℚ)) (fun k => -3 * a * Hq 2 k - 2 * b * Hq 3 k)
            (fun k => laiH n k * (3 * a * Hq 2 k + 2 * b * Hq 3 k) +
              6 * (x - a * Hq 3 k - b * Hq 4 k)) (X ^ ((i : ℕ) + j))).det := by
  unfold laiJ laiMat
  rw [map_mul, MvPolynomial.eval_C, RingHom.map_det]
  congr 2
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  exact eval_laiL n _ a b x

end Eval

section Data

variable {m : ℕ} (hℓ' : ℓ = 9 * m + 1) (hm : 1 ≤ m)

include hℓ' hm in
theorem lai_UE (a' b X' : LocRing ℓ) (k : ℕ) (hk : k ≤ 12 * m) :
    ∃ U E : LocRing ℓ,
      (ℓ : ℚ) ^ 3 * (-3 * ((a' : ℚ) / ℓ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) = (U : ℚ) ∧
      (ℓ : ℚ) ^ 4 * (laiH (2 * m) k * (3 * ((a' : ℚ) / ℓ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - ((a' : ℚ) / ℓ) * Hq 3 k - (b : ℚ) * Hq 4 k)) = (E : ℚ) ∧
      (k < ℓ → (ℓ : LocRing ℓ) ^ 2 ∣ U ∧ (ℓ : LocRing ℓ) ∣ E) ∧
      (ℓ ≤ k → (ℓ : LocRing ℓ) ^ 2 ∣ U + (3 * a' + 2 * b)) := by
  have hl := l_ne_zero ℓ
  have c2 : ((2 : LocRing ℓ) : ℚ) = 2 := rfl
  have c3 : ((3 : LocRing ℓ) : ℚ) = 3 := rfl
  have c5 : ((5 : LocRing ℓ) : ℚ) = 5 := rfl
  have c6 : ((6 : LocRing ℓ) : ℚ) = 6 := rfl
  obtain ⟨z1a, h1a⟩ := Hq_decomp (ℓ := ℓ) 1 (2 * (2 * m) + k) (by omega)
  obtain ⟨z1b, h1b⟩ := Hq_decomp (ℓ := ℓ) 1 (6 * (2 * m) - k) (by omega)
  obtain ⟨z1c, h1c⟩ := Hq_decomp (ℓ := ℓ) 1 k (by omega)
  obtain ⟨z2, h2⟩ := Hq_decomp (ℓ := ℓ) 2 k (by omega)
  obtain ⟨z3, h3⟩ := Hq_decomp (ℓ := ℓ) 3 k (by omega)
  obtain ⟨z4, h4⟩ := Hq_decomp (ℓ := ℓ) 4 k (by omega)
  set T : LocRing ℓ := 3 * a' * z2 + 2 * (ℓ : LocRing ℓ) * b * z3 with hT
  set U : LocRing ℓ := -(iota ℓ k) * (3 * a' + 2 * b) - (ℓ : LocRing ℓ) ^ 2 * T with hU
  set h' : LocRing ℓ := 3 * (iota ℓ (2 * (2 * m) + k) + (ℓ : LocRing ℓ) * z1a) +
      2 * (iota ℓ (6 * (2 * m) - k) + (ℓ : LocRing ℓ) * z1b) -
      5 * (iota ℓ k + (ℓ : LocRing ℓ) * z1c) with hh'
  set E : LocRing ℓ := -h' * U + 6 * (ℓ : LocRing ℓ) * X' -
      6 * a' * (iota ℓ k + (ℓ : LocRing ℓ) ^ 3 * z3) - 6 * b * (iota ℓ k + (ℓ : LocRing ℓ) ^ 4 * z4)
    with hE
  refine ⟨U, E, ?_, ?_, ?_, ?_⟩
  · rw [h2, h3, hU, hT]
    push_cast
    simp only [c2, c3, c5, c6]
    field_simp
    ring
  · unfold laiH
    rw [h1a, h1b, h1c, h2, h3, h4, hE, hh', hU, hT]
    push_cast
    simp only [c2, c3, c5, c6]
    field_simp
    ring
  · intro hkℓ
    have hi : iota ℓ k = 0 := iota_of_lt hkℓ
    refine ⟨⟨-T, ?_⟩, ⟨h' * (ℓ : LocRing ℓ) * T + 6 * X' - 6 * a' * (ℓ : LocRing ℓ) ^ 2 * z3 -
      6 * b * (ℓ : LocRing ℓ) ^ 3 * z4, ?_⟩⟩
    · rw [hU, hi]; ring
    · rw [hE, hU, hi]; ring
  · intro hkℓ
    have hi : iota ℓ k = 1 := iota_of_le hkℓ
    exact ⟨-T, by rw [hU, hi]; ring⟩

include hℓ' hm in
/-- The node data of Lai's `J_{2m}` at `(a'/ℓ, b, X'/ℓ³)` satisfy the hypotheses of the node-block theorem. -/
theorem lai_nodeData (a' b X' : LocRing ℓ) (hε : redQ ℓ (3 * a' + 2 * b) ≠ 0) :
    ∃ D : NodeData ℓ (3 * m),
      D.w = (fun k => (laiCoef (2 * m) k : LocRing ℓ)) ∧
      D.u = (fun k => -3 * ((a' : ℚ) / ℓ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) ∧
      D.e = (fun k => laiH (2 * m) k * (3 * ((a' : ℚ) / ℓ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - ((a' : ℚ) / ℓ) * Hq 3 k - (b : ℚ) * Hq 4 k)) := by
  have hex : ∀ k, ∃ U E : LocRing ℓ, k ≤ 12 * m →
      ((ℓ : ℚ) ^ 3 * (-3 * ((a' : ℚ) / ℓ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) = (U : ℚ) ∧
      (ℓ : ℚ) ^ 4 * (laiH (2 * m) k * (3 * ((a' : ℚ) / ℓ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - ((a' : ℚ) / ℓ) * Hq 3 k - (b : ℚ) * Hq 4 k)) = (E : ℚ) ∧
      (k < ℓ → (ℓ : LocRing ℓ) ^ 2 ∣ U ∧ (ℓ : LocRing ℓ) ∣ E) ∧
      (ℓ ≤ k → (ℓ : LocRing ℓ) ^ 2 ∣ U + (3 * a' + 2 * b))) := by
    intro k
    by_cases hk : k ≤ 12 * m
    · obtain ⟨U, E, h⟩ := lai_UE hℓ' hm a' b X' k hk
      exact ⟨U, E, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hk⟩
  choose U E hUE using hex
  exact
    ⟨{ w := fun k => (laiCoef (2 * m) k : LocRing ℓ)
       u := fun k => -3 * ((a' : ℚ) / ℓ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k
       e := fun k => laiH (2 * m) k * (3 * ((a' : ℚ) / ℓ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - ((a' : ℚ) / ℓ) * Hq 3 k - (b : ℚ) * Hq 4 k)
       U := U
       E := E
       ε := 3 * a' + 2 * b
       hs1 := by omega
       hsℓ := by omega
       hU := fun k hk => (hUE k (by omega)).1
       hE := fun k hk => (hUE k (by omega)).2.1
       low := fun k hk => (hUE k (by omega)).2.2.1 (by omega)
       mid := fun k hk1 hk2 => by
         refine ⟨?_, ((hUE k (by omega)).2.2.1 hk2).1, ((hUE k (by omega)).2.2.1 hk2).2⟩
         have h := laiCoef_mid (ℓ := ℓ) hℓ' hm hk1 hk2
         obtain ⟨c, hc⟩ := h
         exact ⟨(c : LocRing ℓ), by
           apply Subtype.ext
           simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow]
           exact_mod_cast hc⟩
       high := fun μ hμ => by
         refine ⟨?_, (hUE (ℓ + μ) (by omega)).2.2.2 (by omega)⟩
         have h := laiCoef_high (ℓ := ℓ) hℓ' hm hμ
         intro h0
         apply h
         have : ((laiCoef (2 * m) (ℓ + μ) : ℕ) : ZMod ℓ) = 0 := by
           have := h0
           simpa using this
         exact (ZMod.natCast_eq_zero_iff _ _).1 this
       hε := hε }, rfl, rfl, rfl⟩

include hℓ' hm in
/-- **Theorem NV (normalised form), ledger LN03.**  Let `ℓ = 9m + 1` be prime and `n = 2m`.  For
`a', b, X' ∈ ℤ_(ℓ)` with `3a' + 2b` a unit mod `ℓ`, the Hankel determinant `J_n(a, b, X)` at
`(a, b, X) = (a'/ℓ, b, X'/ℓ³)` does not vanish. -/
theorem lai_nv_core (a' b X' : LocRing ℓ) (hε : redQ ℓ (3 * a' + 2 * b) ≠ 0) :
    MvPolynomial.eval ![(a' : ℚ) / ℓ, (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3] (laiJ (2 * m)) ≠ 0 := by
  obtain ⟨D, hDw, hDu, hDe⟩ := lai_nodeData hℓ' hm a' b X' hε
  have key := NodeData.hankel_det_ne_zero D (N := 3 * (2 * m)) (by omega)
  have e : ℓ + 3 * m - 1 = 6 * (2 * m) := by omega
  rw [e, hDw, hDu, hDe] at key
  rw [eval_laiJ]
  refine mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero 2 (by positivity))) ?_
  exact key

include hℓ' hm in
/-- **Theorem NV, exact valuation (normalised form).**  Under the hypotheses of `lai_nv_core`,
`J_n(a, b, X) · ℓ^{18m} · t = g` with `t, g` units of `ℤ_(ℓ)`; hence `v_ℓ(J_n) = -18m = -9n`
(`n = 2m`), i.e. `3nκ` with `κ = -3`. -/
theorem lai_nv_val (a' b X' : LocRing ℓ) (hε : redQ ℓ (3 * a' + 2 * b) ≠ 0) :
    ∃ t g : LocRing ℓ, redQ ℓ t ≠ 0 ∧ redQ ℓ g ≠ 0 ∧
      MvPolynomial.eval ![(a' : ℚ) / ℓ, (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3] (laiJ (2 * m)) *
        ((ℓ : ℚ) ^ (18 * m) * (t : ℚ)) = (g : ℚ) := by
  obtain ⟨D, hDw, hDu, hDe⟩ := lai_nodeData hℓ' hm a' b X' hε
  obtain ⟨t, g, ht, hg, hrel⟩ := NodeData.hankel_det_val D (N := 3 * (2 * m)) (by omega)
  have e : ℓ + 3 * m - 1 = 6 * (2 * m) := by omega
  rw [e, hDw, hDu, hDe] at hrel
  have e2 : 6 * (3 * m) = 18 * m := by omega
  rw [e2] at hrel
  set P : LocRing ℓ := ((∏ i ∈ range (3 * (2 * m)), (i ! : ℕ) ^ 2 : ℕ) : LocRing ℓ) with hP
  have hPq : (P : ℚ) = ∏ i ∈ range (3 * (2 * m)), ((i ! : ℚ)) ^ 2 := by
    rw [hP]; push_cast; rfl
  have hPr : redQ ℓ P ≠ 0 := by
    rw [hP, map_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finset_prod_iff hℓ.out.prime _).1 hd
    have := (Nat.Prime.dvd_factorial hℓ.out).1 (hℓ.out.dvd_of_dvd_pow hdi)
    have := Finset.mem_range.1 hi
    omega
  refine ⟨t ^ 2 * P, g, ?_, hg, ?_⟩
  · rw [map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ ht) hPr
  · rw [eval_laiJ]
    push_cast
    rw [hPq]
    have hP0 : (∏ i ∈ range (3 * (2 * m)), ((i ! : ℚ)) ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero 2 (by positivity)
    rw [← hrel]
    field_simp
    exact (by intro x y z; ring : ∀ x y z : ℚ, x * y * z = y * z * x) _ _ _

include hℓ' hm in
/-- `v_ℓ(J_{2m}(a'/ℓ, b, X'/ℓ³)) = -9n = -18m`. -/
theorem lai_nv_padicVal (a' b X' : LocRing ℓ) (hε : redQ ℓ (3 * a' + 2 * b) ≠ 0) :
    padicValRat ℓ (MvPolynomial.eval ![(a' : ℚ) / ℓ, (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3]
      (laiJ (2 * m))) = -((18 * m : ℕ) : ℤ) := by
  obtain ⟨t, g, ht, hg, h⟩ := lai_nv_val hℓ' hm a' b X' hε
  exact padicValRat_of_unit_rel _ _ t g ht hg h

include hℓ' hm in
/-- **Theorem NV, general scaling (the form `κ`).**  For a nonzero rational `r`, the point
`r · (a'/ℓ, b, X'/ℓ³)` has `v_ℓ(J_n) = 3n(v_ℓ(r) - 3)`, `n = 2m`; in particular `J_n ≠ 0`. -/
theorem lai_nv_scaled (a' b X' : LocRing ℓ) (hε : redQ ℓ (3 * a' + 2 * b) ≠ 0) (r : ℚ) (hr : r ≠ 0) :
    MvPolynomial.eval ![r * ((a' : ℚ) / ℓ), r * (b : ℚ), r * ((X' : ℚ) / (ℓ : ℚ) ^ 3)] (laiJ (2 * m)) ≠ 0 ∧
    padicValRat ℓ (MvPolynomial.eval ![r * ((a' : ℚ) / ℓ), r * (b : ℚ), r * ((X' : ℚ) / (ℓ : ℚ) ^ 3)]
      (laiJ (2 * m))) = (6 * m : ℕ) * padicValRat ℓ r - ((18 * m : ℕ) : ℤ) := by
  have h := eval_smul_of_isHomogeneous (isHomogeneous_laiJ (2 * m)) r
    ![(a' : ℚ) / ℓ, (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3]
  have hv : (fun i => r * (![(a' : ℚ) / ℓ, (b : ℚ), (X' : ℚ) / (ℓ : ℚ) ^ 3] : Fin 3 → ℚ) i) =
      ![r * ((a' : ℚ) / ℓ), r * (b : ℚ), r * ((X' : ℚ) / (ℓ : ℚ) ^ 3)] := by
    funext i; fin_cases i <;> rfl
  rw [hv] at h
  have h0 := lai_nv_core hℓ' hm a' b X' hε
  have hpow : r ^ (3 * (2 * m)) ≠ 0 := pow_ne_zero _ hr
  refine ⟨by rw [h]; exact mul_ne_zero hpow h0, ?_⟩
  rw [h, padicValRat.mul hpow h0, padicValRat.pow r, lai_nv_padicVal hℓ' hm a' b X' hε]
  push_cast
  ring

end Data

end CatalanCore.Lai.NV


/-!
# Corollaries NV1 and NV2 (ledger LN04, LN05) on the Lai families
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai
open scoped Nat

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem mem_locRing_scaled {j : ℕ} (z : ℤ) {q : ℕ} (hq : 0 < q) (h : ¬ ℓ ^ (j + 1) ∣ q) :
    (((ℓ : ℚ) ^ j * z) / (q : ℚ)) ∈ LocRing ℓ := by
  have hfac : q.factorization ℓ ≤ j := by
    by_contra hc
    exact h ((hℓ.out.pow_dvd_iff_le_factorization hq.ne').2 (by omega))
  have hdvd : ℓ ^ (q.factorization ℓ) ∣ ℓ ^ j * z.natAbs :=
    (pow_dvd_pow ℓ hfac).trans (dvd_mul_right _ _)
  have h1 := div_mem_locRing (p := ℓ) hq hdvd
  rcases Int.natAbs_eq z with hz | hz
  · have : (((ℓ : ℚ) ^ j * z) / (q : ℚ)) = (((ℓ ^ j * z.natAbs : ℕ) : ℚ) / (q : ℚ)) := by
      rw [hz]; push_cast; simp
    rw [this]; exact h1
  · have : (((ℓ : ℚ) ^ j * z) / (q : ℚ)) = -(((ℓ ^ j * z.natAbs : ℕ) : ℚ) / (q : ℚ)) := by
      rw [hz]; push_cast; simp; ring
    rw [this]; exact (LocRing ℓ).neg_mem h1

theorem two_ne_zero_zmod (hℓ' : ℓ ≠ 2) : (2 : ZMod ℓ) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := (Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).1 this
  exact hℓ' this

variable {m : ℕ} (hℓ' : ℓ = 9 * m + 1) (hm : 1 ≤ m)

include hℓ' hm in
theorem ne_two : ℓ ≠ 2 := by omega

include hℓ' hm in
/-- **Corollary NV1 (ledger LN04), plane.**  `ℓ = 9m + 1` prime, `n = 2m`, `a, b ∈ ℤ` with `ℓ ∤ b`:
`J_n(a, b, p/q) ≠ 0` unless `ℓ⁴ ∣ q`. -/
theorem lai_nv_plane (a b p : ℤ) (q : ℕ) (hb : ¬ (ℓ : ℤ) ∣ b) (hq : 0 < q) (hq4 : ¬ ℓ ^ 4 ∣ q) :
    (laiPlaneFam a b).evalQ (2 * m) ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  intro h0
  have hmem : ((ℓ : ℚ) ^ 3 * (p : ℤ) / (q : ℚ)) ∈ LocRing ℓ := mem_locRing_scaled p hq hq4
  have hε : redQ ℓ (3 * ((ℓ * a : ℤ) : LocRing ℓ) + 2 * (b : LocRing ℓ)) ≠ 0 := by
    have : redQ ℓ (3 * ((ℓ * a : ℤ) : LocRing ℓ) + 2 * (b : LocRing ℓ)) = 2 * (b : ZMod ℓ) := by
      simp only [map_add, map_mul, map_intCast, map_ofNat]
      push_cast
      simp
    rw [this]
    refine mul_ne_zero (two_ne_zero_zmod (ne_two hℓ' hm)) ?_
    intro h0
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0)
  have key := lai_nv_core hℓ' hm ((ℓ * a : ℤ) : LocRing ℓ) (b : LocRing ℓ) ⟨_, hmem⟩ hε
  have hl := l_ne_zero ℓ
  have hv : (![(((ℓ * a : ℤ) : LocRing ℓ) : ℚ) / ℓ, ((b : LocRing ℓ) : ℚ),
      ((⟨_, hmem⟩ : LocRing ℓ) : ℚ) / (ℓ : ℚ) ^ 3] : Fin 3 → ℚ) = ![(a : ℚ), (b : ℚ), (p : ℚ) / (q : ℚ)] := by
    funext i
    fin_cases i
    · simp; field_simp
    · simp
    · simp; field_simp
  rw [hv] at key
  exact key ((plane_evalQ a b (2 * m) ((p : ℚ) / (q : ℚ))).symm.trans h0)

include hℓ' hm in
/-- **Corollary NV2 (ledger LN05), ratio.**  `ℓ = 9m + 1` prime, `n = 2m`, `q ≠ 0`, `ℓ ∤ p`:
`J_n(1, -p/q, 0) ≠ 0`. -/
theorem lai_nv_ratio (p q : ℤ) (hq : q ≠ 0) (hp : ¬ (ℓ : ℤ) ∣ p) :
    laiRatioFam.evalQ (2 * m) ((p : ℚ) / (q : ℚ)) ≠ 0 := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  intro h0
  have hs := ratio_scaled (2 * m) p q hq'
  have hε : redQ ℓ (3 * ((ℓ * q : ℤ) : LocRing ℓ) + 2 * ((-p : ℤ) : LocRing ℓ)) ≠ 0 := by
    have : redQ ℓ (3 * ((ℓ * q : ℤ) : LocRing ℓ) + 2 * ((-p : ℤ) : LocRing ℓ)) = -(2 * (p : ZMod ℓ)) := by
      simp only [map_add, map_mul, map_intCast, map_ofNat]
      push_cast
      simp
    rw [this]
    refine neg_ne_zero.2 (mul_ne_zero (two_ne_zero_zmod (ne_two hℓ' hm)) ?_)
    intro h0
    exact hp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0)
  have key := lai_nv_core hℓ' hm ((ℓ * q : ℤ) : LocRing ℓ) ((-p : ℤ) : LocRing ℓ) 0 hε
  have hl := l_ne_zero ℓ
  have hv : (![(((ℓ * q : ℤ) : LocRing ℓ) : ℚ) / ℓ, (((-p : ℤ) : LocRing ℓ) : ℚ),
      ((0 : LocRing ℓ) : ℚ) / (ℓ : ℚ) ^ 3] : Fin 3 → ℚ) = ![(q : ℚ), -(p : ℚ), 0] := by
    funext i
    fin_cases i
    · simp; field_simp
    · simp
    · simp
  rw [hv] at key
  exact key (hs.symm.trans (mul_eq_zero_of_right _ h0))

end CatalanCore.Lai.NV
