module

public import CatalanCore.Lai.Construction
public import CatalanCore.Content.GaussMv
public import CatalanCore.Content.ContentLaw
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Data.Nat.Factorial.BigOperators
public import CatalanCore.Content.WeightedDet
public import CatalanCore.Content.CrtBasis

@[expose] public section

/-!
# `CatalanCore.Lai.ContentLaw`: the Lai-specific content law (theorem side), parts

* `LaiN34`   Lemma N items 3-4: harmonic digit splitting, `U_k`, `V_k` expansions in the Gauss valuation;
* `LaiNcoef` Lemma N items 1-2: `c_k = p^{sig} u`, `u = kappa * chat` (mod p), any prime `p >= 3`, `8n < p^2`;
* `LaiNode`  Lemma N node sums: `laiNd`, `node_lead`, `node_ge`, `node0_ge`, `laiL_ge_except`;
* `LaiGram`  the Gram matrix of `L_n` in an arbitrary basis; `GV_laiJ_of_det` (normalisation of `J_n`);
* `LaiOunit` Theorem O unit parts (content Lemma 2.3 (iii)), reflection `x!(p-1-x)! = (-1)^{x+1}`;
* `LaiO`     Theorem O (`thmO`): `3n < p <= 7n/2` gives `v_p(J_n) >= -6(p-2n)`.

Papers: `N9-LAI-CONTENT-2026-11-16.md` (Lemma 2.1-2.4, Theorem O), `N9-LAI-CONTENT-EXACT-2026-11-16.md`
(Lemma N).  Generic ingredients: `Content.GaussMv`, `Content.WeightedDet`, `Content.ContentLaw`,
`Content.CrtBasis`.
-/

section PartLaiN34
/-!
# Lemma N, items 3 and 4 (harmonic digit counts), content note `N9-LAI-CONTENT-EXACT-2026-11-16.md`

For `k = s + ℓ p` (`0 ≤ s < p`, `8n < p²`, `k ≤ 6n`) the harmonic numbers of Lai's coefficients split as
`H_m(j) = p^{-j} H_{⌊m/p⌋}(j) + (p-integral)` (`Hq_split`).  Consequently, in the Gauss valuation `GV`:

* `laiU_expand`  : `U_k = p⁻³ u_ℓ b + O(p⁻²)`, `u_ℓ = -2 H_ℓ(3)`;
* `laiV_expand`  : `V_k = p⁻⁴ v_{ℓ} b + O(p⁻³)`, `v_ℓ = -2 (H_ℓ(3) δ + 3 H_ℓ(4))`,
  `δ = 5 H_ℓ - 3 H_{⌊(2n+k)/p⌋} - 2 H_{⌊(6n-k)/p⌋}` (`laiDelta`);
* `laiU_zero`, `laiV_zero` (item 4, `ℓ = 0`): `v(U_s) ≥ 0`, `v(V_s) ≥ -1`.

All statements are for an arbitrary prime `p`; the integrality of `δ`, `H_ℓ(j)` needs only `8n < p²`.
-/

open Finset MvPolynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Harm

variable {p : ℕ} [hp : Fact p.Prime]

lemma l2 {p : ℕ} [Fact p.Prime] : (2 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 2
lemma l3 {p : ℕ} [Fact p.Prime] : (3 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 3
lemma l5 {p : ℕ} [Fact p.Prime] : (5 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) 5
lemma lm2 {p : ℕ} [Fact p.Prime] : (-2 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (-2)
lemma lm3 {p : ℕ} [Fact p.Prime] : (-3 : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (-3)

lemma lp {p : ℕ} [Fact p.Prime] : (p : ℚ) ∈ LocRing p := by simpa using natPow_mem (p := p) 1

lemma Hq_zero (j : ℕ) : Hq j 0 = 0 := by simp [Hq]

lemma Hq_succ (j m : ℕ) : Hq j (m + 1) = Hq j m + 1 / ((m : ℚ) + 1) ^ j := by
  simp [Hq, Finset.sum_range_succ]

lemma p_ne_zero' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

lemma inv_pow_mem {m : ℕ} (hm : ¬ p ∣ m) (j : ℕ) : 1 / (m : ℚ) ^ j ∈ LocRing p := by
  have := (LocRing p).pow_mem (inv_natCast_mem_locRing (ℓ := p) hm) j
  simpa [one_div, inv_pow] using this

lemma Hq_mem (j m : ℕ) (hm : m < p) : Hq j m ∈ LocRing p := by
  unfold Hq
  refine (LocRing p).sum_mem fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hnd : ¬ p ∣ (i + 1) := fun h => by
    have := Nat.le_of_dvd (by omega) h; omega
  have := inv_pow_mem (p := p) hnd j
  simpa using this

/-- **Harmonic splitting**: `H_m(j) = p^{-j} H_{⌊m/p⌋}(j) + (p-integral)`. -/
lemma Hq_split (j m : ℕ) : Hq j m - ((p : ℚ) ^ j)⁻¹ * Hq j (m / p) ∈ LocRing p := by
  induction m with
  | zero => simp [Hq_zero]
  | succ m ih =>
    by_cases hd : p ∣ m + 1
    · obtain ⟨t, ht⟩ := hd
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; omega
        · exact h
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hm : m = (p - 1) + p * t' := by
        have := hp.out.pos
        have h2 : m + 1 = p * t' + p := by rw [ht]; ring
        omega
      have hdiv : m / p = t' := by
        rw [hm, Nat.add_mul_div_left _ _ hp.out.pos, Nat.div_eq_of_lt (by have := hp.out.pos; omega)]
        simp
      have hdiv1 : (m + 1) / p = t' + 1 := by
        rw [ht]; exact Nat.mul_div_cancel_left _ hp.out.pos
      rw [hdiv1, Hq_succ, Hq_succ]
      rw [hdiv] at ih
      have hcast : ((m : ℚ) + 1) = p * ((t' : ℚ) + 1) := by exact_mod_cast ht
      have hp0 := p_ne_zero' (p := p)
      have hq : 1 / ((m : ℚ) + 1) ^ j = ((p : ℚ) ^ j)⁻¹ * (1 / ((t' : ℚ) + 1) ^ j) := by
        rw [hcast, mul_pow]
        have : ((t' : ℚ) + 1) ≠ 0 := by positivity
        field_simp
      have key : Hq j m + 1 / ((m : ℚ) + 1) ^ j - ((p : ℚ) ^ j)⁻¹ * (Hq j t' + 1 / ((t' : ℚ) + 1) ^ j)
          = Hq j m - ((p : ℚ) ^ j)⁻¹ * Hq j t' := by
        rw [hq]; ring
      rw [key]; exact ih
    · have hdiv : (m + 1) / p = m / p := Nat.succ_div_of_not_dvd hd
      rw [hdiv, Hq_succ]
      have : Hq j m + 1 / ((m : ℚ) + 1) ^ j - ((p : ℚ) ^ j)⁻¹ * Hq j (m / p)
          = (Hq j m - ((p : ℚ) ^ j)⁻¹ * Hq j (m / p)) + 1 / ((m + 1 : ℕ) : ℚ) ^ j := by
        push_cast; ring
      rw [this]
      exact (LocRing p).add_mem ih (inv_pow_mem hd j)

/-- `δ` of Lemma N: `5 H_ℓ - 3 H_{⌊(2n+k)/p⌋} - 2 H_{⌊(6n-k)/p⌋}`. -/
noncomputable def laiDelta (n p k : ℕ) : ℚ :=
  5 * Hq 1 (k / p) - 3 * Hq 1 ((2 * n + k) / p) - 2 * Hq 1 ((6 * n - k) / p)

lemma laiH_split (n k : ℕ) :
    laiH n k + (p : ℚ)⁻¹ * laiDelta n p k ∈ LocRing p := by
  have h1 := Hq_split (p := p) 1 (2 * n + k)
  have h2 := Hq_split (p := p) 1 (6 * n - k)
  have h3 := Hq_split (p := p) 1 k
  simp only [pow_one] at h1 h2 h3
  have := (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).mul_mem l3 h1)
    ((LocRing p).mul_mem l2 h2))
    ((LocRing p).mul_mem l5 h3)
  convert this using 1
  unfold laiH laiDelta
  ring

variable (n k : ℕ)

lemma delta_mem (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) : laiDelta n p k ∈ LocRing p := by
  have hlt : ∀ m, m < p ^ 2 → m / p < p := fun m hm => by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using hm
  unfold laiDelta
  have a1 := Hq_mem (p := p) 1 (k / p) (hlt k (by omega))
  have a2 := Hq_mem (p := p) 1 ((2 * n + k) / p) (hlt _ (by omega))
  have a3 := Hq_mem (p := p) 1 ((6 * n - k) / p) (hlt _ (by omega))
  refine (LocRing p).sub_mem ((LocRing p).sub_mem ((LocRing p).mul_mem l5 a1)
    ((LocRing p).mul_mem l3 a2))
    ((LocRing p).mul_mem l2 a3)

end Harm

section Expand

variable {p : ℕ} [hp : Fact p.Prime]

lemma GV_CX_nat (e : ℕ) (x : ℚ) (i : Fin 3) (h : (p : ℚ) ^ e * x ∈ LocRing p) :
    GV p (-(e : ℤ)) (C x * X i : MvPolynomial (Fin 3) ℚ) := by
  have := GV.const_mul (p := p) (e := -(e : ℤ)) (e' := 0) (x := x) (f := X i)
    (by simpa [zpow_natCast] using h) (GV.var i)
  simpa using this

lemma pmul_mem (e : ℕ) (x : ℚ) (hx : (p : ℚ) ^ e * x ∈ LocRing p) (y : ℚ) (hy : y ∈ LocRing p) :
    (p : ℚ) ^ e * (x * y) ∈ LocRing p := by
  rw [← mul_assoc]; exact (LocRing p).mul_mem hx hy

lemma harm_pole_mem (j m : ℕ) (hm : m / p < p) : (p : ℚ) ^ j * Hq j m ∈ LocRing p := by
  have h := Hq_split (p := p) j m
  have hh := Hq_mem (p := p) j (m / p) hm
  have : (p : ℚ) ^ j * Hq j m = (p : ℚ) ^ j * (Hq j m - ((p : ℚ) ^ j)⁻¹ * Hq j (m / p)) + Hq j (m / p) := by
    have hp0 := p_ne_zero' (p := p)
    field_simp
    ring
  rw [this]
  exact (LocRing p).add_mem ((LocRing p).mul_mem (natPow_mem j) h) hh

/-- **Lemma N, item 3 (`U`).** `k = s + ℓ p`; `U_k = p⁻³ (-2 H_ℓ(3)) b + O(p⁻²)`. -/
theorem laiU_expand (k : ℕ) (hk : k / p < p) :
    GV p (-2) (laiU k - C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * X 1) := by
  have hp0 := p_ne_zero' (p := p)
  have h2 := harm_pole_mem (p := p) 2 k hk
  have h3 := Hq_split (p := p) 3 k
  have e : laiU k - C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * X 1 =
      C (-3 * Hq 2 k) * X 0 + C (-2 * (Hq 3 k - ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p))) * X 1 := by
    unfold laiU
    rw [show (-2 * (Hq 3 k - ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p))) =
      (-2 * Hq 3 k) - (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) by ring, C_sub]
    ring
  rw [e]
  have a : GV p (-2) (C (-3 * Hq 2 k) * X 0 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 2 (-3 * Hq 2 k) 0 (by
      have := (LocRing p).mul_mem lm3 h2
      convert this using 1; ring)
    simpa using this
  have b : GV p (-2) (C (-2 * (Hq 3 k - ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p))) * X 1 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 0 (-2 * (Hq 3 k - ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p))) 1 (by
      simpa using (LocRing p).mul_mem lm2 h3)
    exact (by simpa using this : GV p 0 _).mono (by norm_num)
  exact a.add b

lemma pH_mem (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) : (p : ℚ) * laiH n k ∈ LocRing p := by
  have h := laiH_split (p := p) n k
  have hd := delta_mem (p := p) n k h8 hk
  have hp0 := p_ne_zero' (p := p)
  have : (p : ℚ) * laiH n k = (p : ℚ) * (laiH n k + (p : ℚ)⁻¹ * laiDelta n p k) - laiDelta n p k := by
    field_simp; ring
  rw [this]
  exact (LocRing p).sub_mem ((LocRing p).mul_mem lp h) hd

/-- **Lemma N, item 3 (`V`).**  `V_k = p⁻⁴ v_ℓ b + O(p⁻³)`, `v_ℓ = -2 (H_ℓ(3) δ + 3 H_ℓ(4))`. -/
theorem laiV_expand (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) :
    GV p (-3) (laiV n k - C (((p : ℚ) ^ 4)⁻¹ *
      (-2 * (Hq 3 (k / p) * laiDelta n p k + 3 * Hq 4 (k / p)))) * X 1) := by
  have hp0 := p_ne_zero' (p := p)
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by omega)
  obtain ⟨I1, hI1, eH⟩ : ∃ I1 ∈ LocRing p, laiH n k = I1 - (p : ℚ)⁻¹ * laiDelta n p k :=
    ⟨_, laiH_split (p := p) n k, by ring⟩
  obtain ⟨I3, hI3, e3⟩ : ∃ I3 ∈ LocRing p, Hq 3 k = I3 + ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p) :=
    ⟨_, Hq_split (p := p) 3 k, by ring⟩
  obtain ⟨I4, hI4, e4⟩ : ∃ I4 ∈ LocRing p, Hq 4 k = I4 + ((p : ℚ) ^ 4)⁻¹ * Hq 4 (k / p) :=
    ⟨_, Hq_split (p := p) 4 k, by ring⟩
  have hd := delta_mem (p := p) n k h8 hk
  have hB3 := Hq_mem (p := p) 3 (k / p) hkp
  have hpH := pH_mem (p := p) n k h8 hk
  have hH2 := harm_pole_mem (p := p) 2 k hkp
  have hH3 := harm_pole_mem (p := p) 3 k hkp
  set δ := laiDelta n p k
  set B3 := Hq 3 (k / p)
  set B4 := Hq 4 (k / p)
  have e : laiV n k - C (((p : ℚ) ^ 4)⁻¹ * (-2 * (B3 * δ + 3 * B4))) * X 1 =
      C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * X 0 +
      C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k - ((p : ℚ) ^ 4)⁻¹ * (-2 * (B3 * δ + 3 * B4))) * X 1 +
      C 6 * X 2 := by
    unfold laiV
    simp only [map_sub, map_add, map_mul, map_neg, map_ofNat]
    ring
  rw [e]
  have a : GV p (-3) (C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * X 0 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 3 (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) 0 (by
      have : (p : ℚ) ^ 3 * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) =
          3 * ((p : ℚ) * laiH n k) * ((p : ℚ) ^ 2 * Hq 2 k) - 6 * ((p : ℚ) ^ 3 * Hq 3 k) := by ring
      rw [this]
      exact (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hpH) hH2)
        ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) hH3))
    simpa using this
  have b : GV p (-3) (C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k -
      ((p : ℚ) ^ 4)⁻¹ * (-2 * (B3 * δ + 3 * B4))) * X 1 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 3 _ 1 (by
      have : (p : ℚ) ^ 3 * (2 * laiH n k * Hq 3 k - 6 * Hq 4 k -
          ((p : ℚ) ^ 4)⁻¹ * (-2 * (B3 * δ + 3 * B4))) =
          -2 * (p : ℚ) ^ 2 * δ * I3 + 2 * I1 * B3 + 2 * (p : ℚ) ^ 3 * I1 * I3 - 6 * (p : ℚ) ^ 3 * I4 := by
        rw [eH, e3, e4]
        field_simp
        ring
      rw [this]
      refine (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).add_mem ?_ ?_) ?_) ?_
      · have := (LocRing p).mul_mem ((LocRing p).mul_mem (natPow_mem (p := p) 2) hd) hI3
        convert (LocRing p).mul_mem lm2 this using 1; ring
      · exact (LocRing p).mul_mem ((LocRing p).mul_mem l2 hI1) hB3
      · have := (LocRing p).mul_mem ((LocRing p).mul_mem (natPow_mem (p := p) 3) hI1) hI3
        convert (LocRing p).mul_mem l2 this using 1; ring
      · have := (LocRing p).mul_mem (natPow_mem (p := p) 3) hI4
        convert (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) this using 1; ring)
    simpa using this
  have c : GV p (-3) (C 6 * X 2 : MvPolynomial (Fin 3) ℚ) :=
    (GV_CX_nat (p := p) 0 6 2 (by simpa using (by exact_mod_cast int_mem_locRing (ℓ := p) 6 : (6 : ℚ) ∈ LocRing p))).mono
      (by norm_num)
  exact (a.add b).add c

/-- **Lemma N, item 4 (`ℓ = 0`).** For `k < p`: `v(U_k) ≥ 0`. -/
theorem laiU_zero (k : ℕ) (hk : k < p) : GV p 0 (laiU k) := by
  unfold laiU
  have h2 := Hq_mem (p := p) 2 k hk
  have h3 := Hq_mem (p := p) 3 k hk
  have a := GV_CX_nat (p := p) 0 (-3 * Hq 2 k) 0 (by simpa using (LocRing p).mul_mem lm3 h2)
  have b := GV_CX_nat (p := p) 0 (-2 * Hq 3 k) 1 (by simpa using (LocRing p).mul_mem lm2 h3)
  simpa using a.add b

/-- **Lemma N, item 4 (`ℓ = 0`).** For `k < p`: `v(V_k) ≥ -1`. -/
theorem laiV_zero (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk6 : k ≤ 6 * n) (hk : k < p) :
    GV p (-1) (laiV n k) := by
  have hpH := pH_mem (p := p) n k h8 hk6
  have h2 := Hq_mem (p := p) 2 k hk
  have h3 := Hq_mem (p := p) 3 k hk
  have h4 := Hq_mem (p := p) 4 k hk
  have hp0 := p_ne_zero' (p := p)
  have e : laiV n k = C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * X 0 +
      C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * X 1 + C 6 * X 2 := by
    unfold laiV
    simp only [map_sub, map_add, map_mul, map_neg, map_ofNat]
    ring
  rw [e]
  have a : GV p (-1) (C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * X 0 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 1 (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) 0 (by
      have : (p : ℚ) ^ 1 * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) =
          3 * ((p : ℚ) * laiH n k) * Hq 2 k - 6 * ((p : ℚ) * Hq 3 k) := by ring
      rw [this]
      exact (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hpH) h2)
        ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6)
          ((LocRing p).mul_mem lp h3)))
    simpa using this
  have b : GV p (-1) (C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * X 1 : MvPolynomial (Fin 3) ℚ) := by
    have := GV_CX_nat (p := p) 1 (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) 1 (by
      have : (p : ℚ) ^ 1 * (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) =
          2 * ((p : ℚ) * laiH n k) * Hq 3 k - 6 * ((p : ℚ) * Hq 4 k) := by ring
      rw [this]
      exact (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l2 hpH) h3)
        ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6)
          ((LocRing p).mul_mem lp h4)))
    simpa using this
  have c : GV p (-1) (C 6 * X 2 : MvPolynomial (Fin 3) ℚ) :=
    (GV_CX_nat (p := p) 0 6 2 (by simpa using (by exact_mod_cast int_mem_locRing (ℓ := p) 6 : (6 : ℚ) ∈ LocRing p))).mono
      (by norm_num)
  exact (a.add b).add c

end Expand

end CatalanCore.Lai
end PartLaiN34

section PartLaiNcoef
/-!
# Lemma N, items 1 and 2 for Lai's coefficients `c_k = C(6n,k)² C(2n+k,k)³`

For `k = ℓ p + s` (`s < p`, `8n < p²`, `k ≤ 6n`): `c_k = p^{σ(s)} u` with `u` a natural number and
`u ≡ κ_c(ℓ) ĉ_s (mod p)` (`laiCoef_unit`), where `σ(s) = 2[s > r₆] + 3[s ≥ p - r₂]` is
`Content.sig`, `ĉ_s` is the product of the low-digit factorial ratios (`chat`) and `κ_c(ℓ)` the
high-digit ratios (`kappa`).  Kummer's theorem for two digits, with the Anton–Granville unit parts
`Content.choose_unit_part`.
-/

open Finset CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

/-- subtraction digits: `(a - k)/p` and `(a - k) % p` in terms of those of `a` and `k`. -/
lemma sub_div_mod (p a k : ℕ) (hp : 0 < p) (hk : k ≤ a) :
    k / p + (if a % p < k % p then 1 else 0) ≤ a / p ∧
    (a - k) / p = a / p - k / p - (if a % p < k % p then 1 else 0) ∧
    (a - k) % p = if a % p < k % p then a % p + p - k % p else a % p - k % p := by
  obtain ⟨q, r, hr, ha⟩ : ∃ q r, r < p ∧ a = p * q + r := ⟨a / p, a % p, Nat.mod_lt _ hp, (Nat.div_add_mod a p).symm⟩
  obtain ⟨l, s, hs, hkk⟩ : ∃ l s, s < p ∧ k = p * l + s := ⟨k / p, k % p, Nat.mod_lt _ hp, (Nat.div_add_mod k p).symm⟩
  have hqa : a / p = q := by
    rw [ha, Nat.mul_add_div hp, Nat.div_eq_of_lt hr]; simp
  have hqa' : a % p = r := by
    rw [ha, Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt hr
  have hlk : k / p = l := by
    rw [hkk, Nat.mul_add_div hp, Nat.div_eq_of_lt hs]; simp
  have hlk' : k % p = s := by
    rw [hkk, Nat.mul_add_mod_self_left]; exact Nat.mod_eq_of_lt hs
  rw [hqa, hqa', hlk, hlk']
  have hle : p * l ≤ p * q + r := by omega
  by_cases hb : r < s
  · have hlq : l + 1 ≤ q := by
      by_contra hc
      have : q ≤ l := by omega
      have := Nat.mul_le_mul_left p this
      omega
    obtain ⟨t, ht⟩ : ∃ t, q = l + 1 + t := ⟨q - (l + 1), by omega⟩
    subst ht
    simp only [if_pos hb]
    have e1 : a - k = (r + p - s) + p * t := by
      rw [ha, hkk]; simp only [Nat.mul_add, Nat.mul_one]; omega
    have hu : (a - k) / p = t ∧ (a - k) % p = r + p - s := by
      rw [Nat.div_mod_unique hp]
      refine ⟨by rw [e1]; try ring, by omega⟩
    refine ⟨by omega, by omega, hu.2⟩
  · have hlq : l ≤ q := by
      by_contra hc
      have : q + 1 ≤ l := by omega
      have := Nat.mul_le_mul_left p this
      simp only [Nat.mul_add, Nat.mul_one] at this
      omega
    obtain ⟨t, ht⟩ : ∃ t, q = l + t := ⟨q - l, by omega⟩
    subst ht
    simp only [if_neg hb]
    have e1 : a - k = (r - s) + p * t := by
      rw [ha, hkk]; simp only [Nat.mul_add]; omega
    have hu : (a - k) / p = t ∧ (a - k) % p = r - s := by
      rw [Nat.div_mod_unique hp]
      refine ⟨by rw [e1]; try ring, by omega⟩
    refine ⟨by omega, by omega, hu.2⟩

/-- addition digits. -/
lemma add_div_mod (p a b : ℕ) (hp : 0 < p) :
    (a + b) / p = a / p + b / p + (if p ≤ a % p + b % p then 1 else 0) ∧
    (a + b) % p = if p ≤ a % p + b % p then a % p + b % p - p else a % p + b % p := by
  have h1 := Nat.add_div hp (a := a) (b := b)
  have h2 : (a + b) % p = (a % p + b % p) % p := Nat.add_mod _ _ _
  have ha := Nat.mod_lt a hp
  have hb := Nat.mod_lt b hp
  refine ⟨by rw [h1], ?_⟩
  rw [h2]
  split_ifs with h
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

section Coef

variable {p : ℕ} [hp : Fact p.Prime]

/-- carry flag of `6n - k`: `b = [r₆ < s]`. -/
def bflag (n p s : ℕ) : ℕ := if r6 n p < s then 1 else 0
/-- carry flag of `2n + k`: `ε = [p - r₂ ≤ s]`. -/
def eflag (n p s : ℕ) : ℕ := if p - r2 n p ≤ s then 1 else 0

lemma sig_eq_flags (n p s : ℕ) : sig n p s = 2 * bflag n p s + 3 * eflag n p s := by
  unfold sig bflag eflag
  split_ifs <;> omega

/-- factorial in `ZMod p`. -/
def fz (p m : ℕ) : ZMod p := (m.factorial : ZMod p)

/-- `ĉ_s`: low-digit factorial ratios. -/
def chat (p : ℕ) [Fact p.Prime] (r6 r2 b ε s : ℕ) : ZMod p :=
  (fz p r6 / (fz p s * fz p (r6 + b * p - s))) ^ 2 *
    (fz p (r2 + s - ε * p) / (fz p r2 * fz p s)) ^ 3

/-- `κ_c(ℓ)`: high-digit factorial ratios (a function of the class flags and of `ℓ`). -/
def kappa (p : ℕ) [Fact p.Prime] (q6 q2 b ε l : ℕ) : ZMod p :=
  (((-1) ^ q6 * fz p q6) / (((-1) ^ l * fz p l) * ((-1) ^ (q6 - l - b) * fz p (q6 - l - b)))) ^ 2 *
    (((-1) ^ (q2 + l + ε) * fz p (q2 + l + ε)) / (((-1) ^ l * fz p l) * ((-1) ^ q2 * fz p q2))) ^ 3

/-- **Lemma N, items 1 and 2.**  `c_k = p^{σ(s)} u`, `u ≡ κ_c(ℓ) ĉ_s (mod p)`, `u` a unit. -/
theorem laiCoef_unit {n : ℕ} (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (k : ℕ) (hk : k ≤ 6 * n) :
    ∃ u : ℕ, laiCoef n k = p ^ sig n p (k % p) * u ∧
      (u : ZMod p) = kappa p (q6 n p) (q2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k / p) *
        chat p (r6 n p) (r2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k % p) ∧
      (u : ZMod p) ≠ 0 := by
  have hpp := hp.out.pos
  have h6 : 6 * n < p ^ 2 := by omega
  -- the two choose factorisations
  obtain ⟨u1, hu1, hu1c⟩ := choose_unit_part (p := p) h3 k (6 * n - k) (by omega)
  obtain ⟨u2, hu2, hu2c⟩ := choose_unit_part (p := p) h3 k (2 * n) (by omega)
  have e6 : k + (6 * n - k) = 6 * n := by omega
  rw [e6] at hu1 hu1c
  have hk2 : (k + 2 * n).choose k = (2 * n + k).choose k := by rw [add_comm]
  rw [hk2] at hu2
  -- digits
  obtain ⟨hsd1, hsd2, hsd3⟩ := sub_div_mod p (6 * n) k hpp hk
  obtain ⟨had1, had2⟩ := add_div_mod p k (2 * n) hpp
  have hpk := Nat.mod_lt k hpp
  have hp6 := Nat.mod_lt (6 * n) hpp
  have hp2 := Nat.mod_lt (2 * n) hpp
  have hb : bflag n p (k % p) = if 6 * n % p < k % p then 1 else 0 := rfl
  have he : eflag n p (k % p) = if p - 2 * n % p ≤ k % p then 1 else 0 := rfl
  have d1 : (6 * n - k) / p = q6 n p - k / p - bflag n p (k % p) := by
    rw [hsd2, hb]; rfl
  have d2 : (6 * n - k) % p = r6 n p + bflag n p (k % p) * p - k % p := by
    rw [hsd3, hb]; unfold r6; split_ifs <;> omega
  have d3 : (k + 2 * n) / p = q2 n p + k / p + eflag n p (k % p) := by
    rw [had1, he]; unfold q2; split_ifs with h1 h2 h2 <;> omega
  have d4 : (k + 2 * n) % p = r2 n p + k % p - eflag n p (k % p) * p := by
    rw [had2, he]; unfold r2; split_ifs with h1 h2 h2 <;> omega
  have ex1 : 6 * n / p - k / p - (6 * n - k) / p = bflag n p (k % p) := by
    rw [← hb] at hsd1 hsd2; omega
  have ex2 : (k + 2 * n) / p - k / p - 2 * n / p = eflag n p (k % p) := by
    rw [d3]; unfold q2; omega
  rw [ex1] at hu1
  rw [ex2] at hu2
  refine ⟨u1 ^ 2 * u2 ^ 3, ?_, ?_, ?_⟩
  · unfold laiCoef
    rw [hu1, hu2, sig_eq_flags]; ring
  · -- unit parts
    have hf1 : fu p k ≠ 0 := fu_ne_zero k (by omega)
    have hf2 : fu p (6 * n - k) ≠ 0 := fu_ne_zero _ (by omega)
    have hf3 : fu p (2 * n) ≠ 0 := fu_ne_zero _ (by omega)
    have hu1' : (u1 : ZMod p) = fu p (6 * n) / (fu p k * fu p (6 * n - k)) := by
      rw [eq_div_iff (mul_ne_zero hf1 hf2), ← hu1c]; ring
    have hu2' : (u2 : ZMod p) = fu p (k + 2 * n) / (fu p k * fu p (2 * n)) := by
      rw [eq_div_iff (mul_ne_zero hf1 hf3), ← hu2c]; ring
    have f6 : fu p (6 * n - k) = (-1) ^ (q6 n p - k / p - bflag n p (k % p)) *
        fz p (q6 n p - k / p - bflag n p (k % p)) * fz p (r6 n p + bflag n p (k % p) * p - k % p) := by
      unfold fu fz; rw [d1, d2]
    have f7 : fu p (k + 2 * n) = (-1) ^ (q2 n p + k / p + eflag n p (k % p)) *
        fz p (q2 n p + k / p + eflag n p (k % p)) * fz p (r2 n p + k % p - eflag n p (k % p) * p) := by
      unfold fu fz; rw [d3, d4]
    have f8 : fu p (6 * n) = (-1) ^ q6 n p * fz p (q6 n p) * fz p (r6 n p) := by
      unfold fu fz q6 r6; rfl
    have f9 : fu p (2 * n) = (-1) ^ q2 n p * fz p (q2 n p) * fz p (r2 n p) := by
      unfold fu fz q2 r2; rfl
    have f10 : fu p k = (-1) ^ (k / p) * fz p (k / p) * fz p (k % p) := by
      unfold fu fz; rfl
    push_cast
    rw [hu1', hu2', f6, f7, f8, f9, f10]
    unfold kappa chat
    ring
  · have hf1 : fu p k ≠ 0 := fu_ne_zero k (by omega)
    have hf2 : fu p (6 * n - k) ≠ 0 := fu_ne_zero _ (by omega)
    have hf3 : fu p (2 * n) ≠ 0 := fu_ne_zero _ (by omega)
    have hf6 : fu p (6 * n) ≠ 0 := fu_ne_zero _ h6
    have hf7 : fu p (k + 2 * n) ≠ 0 := fu_ne_zero _ (by omega)
    have hu1' : (u1 : ZMod p) = fu p (6 * n) / (fu p k * fu p (6 * n - k)) := by
      rw [eq_div_iff (mul_ne_zero hf1 hf2), ← hu1c]; ring
    have hu2' : (u2 : ZMod p) = fu p (k + 2 * n) / (fu p k * fu p (2 * n)) := by
      rw [eq_div_iff (mul_ne_zero hf1 hf3), ← hu2c]; ring
    push_cast
    rw [hu1', hu2']
    exact mul_ne_zero (pow_ne_zero _ (div_ne_zero hf6 (mul_ne_zero hf1 hf2)))
      (pow_ne_zero _ (div_ne_zero hf7 (mul_ne_zero hf1 hf3)))

end Coef

end CatalanCore.Lai
end PartLaiNcoef

section PartLaiNode
/-!
# Lemma N: node sums of `L_n` on a polynomial vanishing at `-s` to order `m`

`laiNd n k F = c_k (U_k F'(-k) + V_k F(-k))` is the `k`-th summand of `laiL n F`.  For
`F = (X + s)^m R` with `R` `p`-integral and `k = s + ℓ p`:

* `node_lead` (`ℓ ≥ 1`): `laiNd = p^{σ+m-4} u ρ [m(-ℓ)^{m-1} u_ℓ + (-ℓ)^m v_ℓ] b + O(p^{σ+m-3})`,
  where `c_k = p^σ u` and `ρ = R(-s)`;
* `node_ge` (`ℓ ≥ 1`): hence `v ≥ σ - 4 + m`;
* `node0_ge` (`ℓ = 0`): `v ≥ σ - 1 + min(m, 1)`, and the node is `0` for `m ≥ 2`;
* `laiL_ge`: the sum over `k ≤ 6n`.
-/

open Finset MvPolynomial Polynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

noncomputable section

/-- The `k`-th node term of `laiL`. -/
def laiNd (n k : ℕ) (F : ℚ[X]) : MP :=
  MvPolynomial.C (laiCoef n k : ℚ) *
    (laiU k * MvPolynomial.C (F.derivative.eval (-(k : ℚ))) +
      laiV n k * MvPolynomial.C (F.eval (-(k : ℚ))))

theorem laiL_eq_sum (n : ℕ) (F : ℚ[X]) : laiL n F = ∑ k ∈ range (6 * n + 1), laiNd n k F := rfl

end

section IntPoly

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p`-integral polynomial: all coefficients in `ℤ_(p)`. -/
def IntPoly (p : ℕ) [Fact p.Prime] (R : ℚ[X]) : Prop := ∀ i, R.coeff i ∈ LocRing p

lemma IntPoly.eval_mem {R : ℚ[X]} (hR : IntPoly p R) {x : ℚ} (hx : x ∈ LocRing p) :
    R.eval x ∈ LocRing p := by
  rw [Polynomial.eval_eq_sum_range]
  exact (LocRing p).sum_mem fun i _ => (LocRing p).mul_mem (hR i) ((LocRing p).pow_mem hx i)

lemma IntPoly.derivative {R : ℚ[X]} (hR : IntPoly p R) : IntPoly p (Polynomial.derivative R) := by
  intro i
  rw [Polynomial.coeff_derivative]
  exact (LocRing p).mul_mem (hR _) (by exact_mod_cast int_mem_locRing (ℓ := p) ((i + 1 : ℕ) : ℤ))

lemma IntPoly.eval_sub {R : ℚ[X]} (hR : IntPoly p R) (a b : ℤ) (h : (p : ℤ) ∣ a - b) :
    ((p : ℚ))⁻¹ * (R.eval (a : ℚ) - R.eval (b : ℚ)) ∈ LocRing p := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range (p := R) (x := (b : ℚ)), ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine (LocRing p).sum_mem fun i _ => ?_
  obtain ⟨z, hz⟩ := dvd_trans h (sub_dvd_pow_sub_pow a b i)
  have hz' : (a : ℚ) ^ i - (b : ℚ) ^ i = (p : ℚ) * z := by exact_mod_cast hz
  have : (p : ℚ)⁻¹ * (R.coeff i * (a : ℚ) ^ i - R.coeff i * (b : ℚ) ^ i) = R.coeff i * z := by
    rw [← mul_sub, hz']; field_simp
  rw [this]
  exact (LocRing p).mul_mem (hR i) (int_mem_locRing z)

lemma IntPoly.mul {R S : ℚ[X]} (hR : IntPoly p R) (hS : IntPoly p S) : IntPoly p (R * S) := by
  intro i
  rw [Polynomial.coeff_mul]
  exact (LocRing p).sum_mem fun x _ => (LocRing p).mul_mem (hR _) (hS _)

lemma IntPoly.X_add_C (s : ℤ) : IntPoly p (Polynomial.X + Polynomial.C (s : ℚ)) := by
  intro i
  rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
  split_ifs <;> simp [int_mem_locRing, (LocRing p).one_mem, (LocRing p).add_mem, (LocRing p).zero_mem] <;>
    first | exact int_mem_locRing s | exact (LocRing p).one_mem

lemma IntPoly.pow {R : ℚ[X]} (hR : IntPoly p R) (m : ℕ) : IntPoly p (R ^ m) := by
  induction m with
  | zero =>
    intro i; rw [pow_zero, Polynomial.coeff_one]; split_ifs
    · exact (LocRing p).one_mem
    · exact (LocRing p).zero_mem
  | succ m ih => rw [pow_succ]; exact ih.mul hR

end IntPoly

section Lead

variable {p : ℕ} [hp : Fact p.Prime]

/-- `u_ℓ = -2 H_ℓ(3)`. -/
noncomputable def uL (l : ℕ) : ℚ := -2 * Hq 3 l

/-- `v_ℓ = -2 (H_ℓ(3) δ + 3 H_ℓ(4))`. -/
noncomputable def vL (n p k l : ℕ) : ℚ := -2 * (Hq 3 l * laiDelta n p k + 3 * Hq 4 l)

/-- `m(-ℓ)^{m-1} u + (-ℓ)^m v`: the `p^{σ+m-4}` coefficient of a node (up to the unit `ρ`). -/
noncomputable def leadF (m l : ℕ) (u v : ℚ) : ℚ := (m : ℚ) * (-(l : ℚ)) ^ (m - 1) * u + (-(l : ℚ)) ^ m * v

lemma GV_C_zpow (e : ℤ) (x y : ℚ) (hx : x = (p : ℚ) ^ e * y) (hy : y ∈ LocRing p) :
    GV p e (MvPolynomial.C x : MP) := by
  apply GV.const
  rw [hx, ← mul_assoc, ← zpow_add₀ p_ne_zero', neg_add_cancel, zpow_zero, one_mul]
  exact hy

lemma GV_CX_three (a b c : ℕ) (x y : ℚ) (hx : x = (p : ℚ) ^ a * (p : ℚ) ^ b * ((p : ℚ) ^ c)⁻¹ * y)
    (hy : y ∈ LocRing p) (i : Fin 3) :
    GV p ((a : ℤ) + b - c) (MvPolynomial.C x * MvPolynomial.X i : MP) := by
  have := GV.const_mul (p := p) (e := (a : ℤ) + b - c) (e' := 0) (x := x) (f := MvPolynomial.X i)
    (by
      rw [hx]
      have hp0 := p_ne_zero' (p := p)
      have : (p : ℚ) ^ (-((a : ℤ) + b - c)) * ((p : ℚ) ^ a * (p : ℚ) ^ b * ((p : ℚ) ^ c)⁻¹ * y) = y := by
        rw [neg_sub, zpow_sub₀ hp0, zpow_add₀ hp0, zpow_natCast, zpow_natCast, zpow_natCast]
        field_simp
      rw [this]; exact hy) (GV.var i)
  simpa using this

lemma uL_mem (l : ℕ) (hl : l < p) : uL l ∈ LocRing p := by
  unfold uL; exact (LocRing p).mul_mem lm2 (Hq_mem (p := p) 3 l hl)

lemma vL_mem (n k l : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) (hl : l < p) : vL n p k l ∈ LocRing p := by
  unfold vL
  have h1 := Hq_mem (p := p) 3 l hl
  have h2 := Hq_mem (p := p) 4 l hl
  have h3 := delta_mem (p := p) n k h8 hk
  exact (LocRing p).mul_mem lm2 ((LocRing p).add_mem ((LocRing p).mul_mem h1 h3) ((LocRing p).mul_mem l3 h2))

lemma natq_mem (m : ℕ) : (m : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (m : ℤ)

lemma leadF_mem (m l : ℕ) (u v : ℚ) (hl : (l : ℚ) ∈ LocRing p) (hu : u ∈ LocRing p) (hv : v ∈ LocRing p) :
    leadF m l u v ∈ LocRing p := by
  unfold leadF
  have hn : (-(l : ℚ)) ∈ LocRing p := (LocRing p).neg_mem hl
  exact (LocRing p).add_mem
    ((LocRing p).mul_mem ((LocRing p).mul_mem (natq_mem m) ((LocRing p).pow_mem hn _)) hu)
    ((LocRing p).mul_mem ((LocRing p).pow_mem hn _) hv)

theorem node_lead (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (u : ℕ) (hu : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u)
    (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) :
    GV p ((sig n p (k % p) : ℤ) - 3 + m)
      (laiNd n k ((Polynomial.X + Polynomial.C ((k % p : ℕ) : ℚ)) ^ m * R) -
        MvPolynomial.C ((p : ℚ) ^ (sig n p (k % p)) * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * u *
          R.eval (-((k % p : ℕ) : ℚ)) * leadF m (k / p) (uL (k / p)) (vL n p k (k / p))) *
          MvPolynomial.X (1 : Fin 3)) := by
  have hp0 := p_ne_zero' (p := p)
  set s := k % p with hs
  set l := k / p with hlk
  set σ := sig n p s with hσ
  have hkl : k = p * l + s := (Nat.div_add_mod k p).symm
  have hkp : l < p := by
    rw [hlk, Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hkq : (k : ℚ) = p * l + s := by exact_mod_cast hkl
  -- the polynomial
  set F : ℚ[X] := (Polynomial.X + Polynomial.C (s : ℚ)) ^ m * R with hF
  have hFe : F.eval (-(k : ℚ)) = (-((l : ℚ) * p)) ^ m * R.eval (-(k : ℚ)) := by
    rw [hF, Polynomial.eval_mul, Polynomial.eval_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    congr 2; rw [hkq]; ring
  have hFd : F.derivative.eval (-(k : ℚ)) = (m : ℚ) * (-((l : ℚ) * p)) ^ (m - 1) * R.eval (-(k : ℚ)) +
      (-((l : ℚ) * p)) ^ m * (Polynomial.derivative R).eval (-(k : ℚ)) := by
    rw [hF, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      mul_one, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_natCast]
    have : -(k : ℚ) + s = -((l : ℚ) * p) := by rw [hkq]; ring
    rw [this]
  -- integrality data
  have hρ' : (Polynomial.derivative R).eval (-(k : ℚ)) ∈ LocRing p :=
    hR.derivative.eval_mem ((LocRing p).neg_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (k : ℤ)))
  obtain ⟨e1, he1, hRk⟩ : ∃ e1 ∈ LocRing p, R.eval (-(k : ℚ)) = R.eval (-(s : ℚ)) + (p : ℚ) * e1 := by
    have := hR.eval_sub (-(k : ℤ)) (-(s : ℤ)) (by
      have : (-(k : ℤ)) - (-(s : ℤ)) = -((p : ℤ) * l) := by omega
      rw [this]; exact (dvd_neg.2 (dvd_mul_right _ _)))
    refine ⟨_, this, ?_⟩
    push_cast at this ⊢
    field_simp
    ring
  have hρ : R.eval (-(s : ℚ)) ∈ LocRing p :=
    hR.eval_mem ((LocRing p).neg_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (s : ℤ)))
  set ρ := R.eval (-(s : ℚ)) with hρdef
  set ρ' := (Polynomial.derivative R).eval (-(k : ℚ)) with hρ'def
  have huq : (u : ℚ) ∈ LocRing p := natq_mem u
  have hlq : (l : ℚ) ∈ LocRing p := natq_mem l
  have huL := uL_mem (p := p) l hkp
  have hvL := vL_mem (p := p) n k l h8 hk hkp
  -- expansions of U, V
  have hU := laiU_expand (p := p) k hkp
  have hV := laiV_expand (p := p) n k h8 hk
  set Us := laiU k - MvPolynomial.C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * MvPolynomial.X (1 : Fin 3) with hUs
  set Vs := laiV n k - MvPolynomial.C (((p : ℚ) ^ 4)⁻¹ *
    (-2 * (Hq 3 (k / p) * laiDelta n p k + 3 * Hq 4 (k / p)))) * MvPolynomial.X (1 : Fin 3) with hVs
  -- A and B
  set A := F.derivative.eval (-(k : ℚ)) with hA
  set B := F.eval (-(k : ℚ)) with hB
  set yA : ℚ := (m : ℚ) * (-(l : ℚ)) ^ (m - 1) * R.eval (-(k : ℚ)) + (p : ℚ) * (-(l : ℚ)) ^ m * ρ' with hyA
  set yB : ℚ := (-(l : ℚ)) ^ m * R.eval (-(k : ℚ)) with hyB
  have hAy : (p : ℚ) * A = (p : ℚ) ^ m * yA := by
    rw [hFd, hyA]
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]; rw [neg_mul_eq_neg_mul]; ring
  have hBy : B = (p : ℚ) ^ m * yB := by
    rw [hFe, hyB]; ring
  have hlkm : R.eval (-(k : ℚ)) ∈ LocRing p := by
    rw [hRk]; exact (LocRing p).add_mem hρ ((LocRing p).mul_mem lp he1)
  have hyAm : yA ∈ LocRing p := by
    rw [hyA]
    exact (LocRing p).add_mem
      ((LocRing p).mul_mem ((LocRing p).mul_mem (natq_mem m)
        ((LocRing p).pow_mem ((LocRing p).neg_mem hlq) _)) hlkm)
      ((LocRing p).mul_mem ((LocRing p).mul_mem lp ((LocRing p).pow_mem ((LocRing p).neg_mem hlq) _)) hρ')
  have hyBm : yB ∈ LocRing p := (LocRing p).mul_mem ((LocRing p).pow_mem ((LocRing p).neg_mem hlq) _) hlkm
  -- the identity
  set x : ℚ := (laiCoef n k : ℚ) * ((-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * A +
      (((p : ℚ) ^ 4)⁻¹ * (-2 * (Hq 3 (k / p) * laiDelta n p k + 3 * Hq 4 (k / p)))) * B) -
    (p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * u * ρ * leadF m l (uL l) (vL n p k l) with hx
  have hid : laiNd n k F - MvPolynomial.C ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * u * ρ *
        leadF m l (uL l) (vL n p k l)) * MvPolynomial.X (1 : Fin 3) =
      MvPolynomial.C (laiCoef n k : ℚ) * Us * MvPolynomial.C A +
      MvPolynomial.C (laiCoef n k : ℚ) * Vs * MvPolynomial.C B + MvPolynomial.C x * MvPolynomial.X (1 : Fin 3) := by
    have e1' : laiU k = Us + MvPolynomial.C (-2 * ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p)) * MvPolynomial.X (1 : Fin 3) := by
      rw [hUs]; ring
    have e2' : laiV n k = Vs + MvPolynomial.C (((p : ℚ) ^ 4)⁻¹ *
        (-2 * (Hq 3 (k / p) * laiDelta n p k + 3 * Hq 4 (k / p)))) * MvPolynomial.X (1 : Fin 3) := by
      rw [hVs]; ring
    unfold laiNd
    rw [e1', e2', hx]
    simp only [map_sub, map_add, map_mul]
    ring
  rw [hid]
  -- three pieces
  have hcσ : GV p (σ : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MP) :=
    GV_C_zpow (σ : ℤ) _ (u : ℚ) (by rw [hu, zpow_natCast]) huq
  have hAz : GV p ((m : ℤ) - 1) (MvPolynomial.C A : MP) := by
    refine GV_C_zpow _ _ yA ?_ hyAm
    have : A = (p : ℚ)⁻¹ * ((p : ℚ) ^ m * yA) := by rw [← hAy]; field_simp
    rw [this, zpow_sub₀ hp0, zpow_natCast, zpow_one]; ring
  have hBz : GV p (m : ℤ) (MvPolynomial.C B : MP) :=
    GV_C_zpow _ _ yB (by rw [hBy, zpow_natCast]) hyBm
  have p2 : GV p ((σ : ℤ) - 3 + m)
      (MvPolynomial.C (laiCoef n k : ℚ) * Us * MvPolynomial.C A) := by
    have := (hcσ.mul hU).mul hAz
    refine this.mono (le_of_eq ?_); ring
  have p3 : GV p ((σ : ℤ) - 3 + m)
      (MvPolynomial.C (laiCoef n k : ℚ) * Vs * MvPolynomial.C B) := by
    have := (hcσ.mul hV).mul hBz
    refine this.mono (le_of_eq ?_); ring
  have p1 : GV p ((σ : ℤ) - 3 + m) (MvPolynomial.C x * MvPolynomial.X (1 : Fin 3) : MP) := by
    have key : x = (p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 3)⁻¹ *
        ((u : ℚ) * (uL l * ((m : ℚ) * (-(l : ℚ)) ^ (m - 1) * e1 + (-(l : ℚ)) ^ m * ρ') +
          vL n p k l * ((-(l : ℚ)) ^ m * e1))) := by
      have hAeq : A = (p : ℚ)⁻¹ * ((p : ℚ) ^ m * yA) := by rw [← hAy]; field_simp
      rw [hx, hu, hAeq, hBy, hyA, hyB, hRk]
      unfold leadF uL vL
      field_simp
      ring
    have hy : (u : ℚ) * (uL l * ((m : ℚ) * (-(l : ℚ)) ^ (m - 1) * e1 + (-(l : ℚ)) ^ m * ρ') +
          vL n p k l * ((-(l : ℚ)) ^ m * e1)) ∈ LocRing p := by
      have hn : (-(l : ℚ)) ∈ LocRing p := (LocRing p).neg_mem hlq
      exact (LocRing p).mul_mem huq ((LocRing p).add_mem
        ((LocRing p).mul_mem huL ((LocRing p).add_mem
          ((LocRing p).mul_mem ((LocRing p).mul_mem (natq_mem m) ((LocRing p).pow_mem hn _)) he1)
          ((LocRing p).mul_mem ((LocRing p).pow_mem hn _) hρ')))
        ((LocRing p).mul_mem hvL ((LocRing p).mul_mem ((LocRing p).pow_mem hn _) he1)))
    have := GV_CX_three (p := p) σ m 3 x _ key hy 1
    exact this.mono (le_of_eq (by push_cast; ring))
  exact (p2.add p3).add p1

end Lead

section Ge

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Lemma N / 2.1 (node valuation, `ℓ ≥ 1`).**  `F = (X + s)^m R`, `R` integral:
`v(node) ≥ σ(s) - 4 + m`. -/
theorem node_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) :
    GV p ((sig n p (k % p) : ℤ) - 4 + m)
      (laiNd n k ((Polynomial.X + Polynomial.C ((k % p : ℕ) : ℚ)) ^ m * R)) := by
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u := by exact_mod_cast hu
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have h1 := node_lead n k h8 h3 hk hl u hu' m R hR
  set σ := sig n p (k % p)
  have hρ : R.eval (-((k % p : ℕ) : ℚ)) ∈ LocRing p :=
    hR.eval_mem ((LocRing p).neg_mem (natq_mem _))
  have hL := leadF_mem (p := p) m (k / p) (uL (k / p)) (vL n p k (k / p)) (natq_mem _)
    (uL_mem (p := p) _ hkp) (vL_mem (p := p) n k _ h8 hk hkp)
  have h2 : GV p ((σ : ℤ) - 4 + m) (MvPolynomial.C ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * u *
          R.eval (-((k % p : ℕ) : ℚ)) * leadF m (k / p) (uL (k / p)) (vL n p k (k / p))) *
          MvPolynomial.X (1 : Fin 3) : MP) := by
    have := GV_CX_three (p := p) σ m 4 ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * u *
          R.eval (-((k % p : ℕ) : ℚ)) * leadF m (k / p) (uL (k / p)) (vL n p k (k / p)))
      ((u : ℚ) * R.eval (-((k % p : ℕ) : ℚ)) *
        leadF m (k / p) (uL (k / p)) (vL n p k (k / p))) (by ring)
      ((LocRing p).mul_mem ((LocRing p).mul_mem (natq_mem u) hρ) hL) 1
    exact this.mono (le_of_eq (by push_cast; ring))
  have := (h1.mono (show (σ : ℤ) - 4 + m ≤ (σ : ℤ) - 3 + m by omega)).add h2
  simpa using this

/-- `ℓ = 0` (`k < p`): `v(node) ≥ σ - 1 + min(m, 1)`, and the node is `0` if `m ≥ 2`. -/
theorem node0_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hkp : k < p)
    (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) :
    GV p ((sig n p k : ℤ) - 1 + (min m 1 : ℕ))
      (laiNd n k ((Polynomial.X + Polynomial.C (k : ℚ)) ^ m * R)) := by
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  have hmod : k % p = k := Nat.mod_eq_of_lt hkp
  rw [hmod] at hu
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p k) * u := by exact_mod_cast hu
  have huq : (u : ℚ) ∈ LocRing p := natq_mem u
  have hcσ : GV p (sig n p k : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MP) :=
    GV_C_zpow _ _ (u : ℚ) (by rw [hu', zpow_natCast]) huq
  have hkq : (-(k : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem _)
  have hU := laiU_zero (p := p) k hkp
  have hV := laiV_zero (p := p) n k h8 hk hkp
  have hR0 : R.eval (-(k : ℚ)) ∈ LocRing p := hR.eval_mem hkq
  have hR1 : (Polynomial.derivative R).eval (-(k : ℚ)) ∈ LocRing p := hR.derivative.eval_mem hkq
  have hevl : ∀ x : ℚ, x ∈ LocRing p → GV p 0 (MvPolynomial.C x : MP) := fun x hx => GV.const_loc hx
  rcases m with _ | _ | m
  · -- m = 0
    unfold laiNd
    simp only [pow_zero, one_mul, min_self, Nat.zero_min, Nat.cast_zero, add_zero]
    have := hcσ.mul (((hU.mul (hevl _ hR1)).mono (show (-1 : ℤ) + 0 ≤ 0 + 0 by norm_num)).add (hV.mul (hevl _ hR0)))
    refine this.mono ?_
    omega
  · -- m = 1
    unfold laiNd
    have e1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (0 + 1) * R).eval (-(k : ℚ)) = 0 := by
      simp
    have e2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (0 + 1) * R).derivative.eval (-(k : ℚ)) =
        R.eval (-(k : ℚ)) := by
      simp [Polynomial.derivative_mul]
    rw [e1, e2]
    simp only [map_zero, mul_zero, add_zero]
    have := hcσ.mul (hU.mul (hevl _ hR0))
    refine this.mono ?_
    simp
  · -- m ≥ 2
    have e1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m + 1 + 1) * R).eval (-(k : ℚ)) = 0 := by
      simp
    have e2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m + 1 + 1) * R).derivative.eval (-(k : ℚ)) = 0 := by
      simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
    unfold laiNd
    rw [e1, e2]
    simp only [map_zero, mul_zero, add_zero]
    exact GV.zero _

/-- **The sum over nodes, with an exceptional set `E` removed.** -/
theorem laiL_ge_except (n : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (F : ℚ[X]) (mm : ℕ → ℕ) (RR : ℕ → ℚ[X])
    (hR : ∀ s, s < p → IntPoly p (RR s))
    (hF : ∀ s, s < p → F = (Polynomial.X + Polynomial.C (s : ℚ)) ^ (mm s) * RR s) (e : ℤ)
    (E : Finset ℕ) (hE : E ⊆ range (6 * n + 1))
    (h1 : ∀ k, k ≤ 6 * n → k ∉ E → 1 ≤ k / p → e ≤ (sig n p (k % p) : ℤ) - 4 + mm (k % p))
    (h0 : ∀ k, k ≤ 6 * n → k ∉ E → k < p →
      e ≤ (sig n p k : ℤ) - 1 + (min (mm k) 1 : ℕ) ∨ 2 ≤ mm k) :
    GV p e (laiL n F - ∑ k ∈ E, laiNd n k F) := by
  rw [laiL_eq_sum, ← Finset.sum_sdiff hE]
  rw [add_sub_cancel_right]
  refine GV.sum fun k hk => ?_
  have hk' := Finset.mem_sdiff.1 hk
  have hk6 : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk'.1
  by_cases hl : 1 ≤ k / p
  · have hs : k % p < p := Nat.mod_lt _ hp.out.pos
    rw [hF (k % p) hs]
    exact (node_ge n k h8 h3 hk6 hl _ _ (hR _ hs)).mono (h1 k hk6 hk'.2 hl)
  · have hkp : k < p := by
      by_contra hc
      exact hl (Nat.div_pos (by omega) hp.out.pos)
    rw [hF k hkp]
    rcases h0 k hk6 hk'.2 hkp with h | h
    · exact (node0_ge n k h8 h3 hk6 hkp _ _ (hR _ hkp)).mono h
    · obtain ⟨m', hm'⟩ : ∃ m', mm k = m' + 2 := ⟨mm k - 2, by omega⟩
      rw [hm']
      have e1 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m' + 2) * RR k).eval (-(k : ℚ)) = 0 := by simp
      have e2 : ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (m' + 2) * RR k).derivative.eval (-(k : ℚ)) = 0 := by
        simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
      unfold laiNd
      rw [e1, e2]
      simp only [map_zero, mul_zero, add_zero]
      exact GV.zero _

end Ge
end CatalanCore.Lai
end PartLaiNode

section PartLaiGram
/-!
# The Gram matrix of `L_n` in an arbitrary basis, and the normalisation of `J_n`

* `laiL_add`, `laiL_C_mul`, `laiL_sum`: `L_n` is `ℚ`-linear in `P`;
* `gram_eq`: `(L_n(f_x f_y))_{x,y} = B · (L_n(t^{i+j})) · Bᵀ`, `B_{x i} = [t^i] f_x`
  (`natDegree f_x < 3n`);
* `gram_det`: `det Gram = (det B)² det (laiMat n)` for a basis indexed by `ι ≃ Fin (3n)`;
* `GV_laiJ_of_det`: `v_p(J_n) ≥ v_p(det L_n(t^{i+j})) - ν_p`, `ν_p = v_p(∏_{i<3n} i!²)`.
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Linear

lemma laiL_add (n : ℕ) (P Q : ℚ[X]) : laiL n (P + Q) = laiL n P + laiL n Q := by
  unfold laiL
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.derivative_add, Polynomial.eval_add, map_add]
  ring

lemma laiL_zero (n : ℕ) : laiL n 0 = 0 := by
  unfold laiL
  simp

lemma laiL_C_mul (n : ℕ) (a : ℚ) (P : ℚ[X]) :
    laiL n (Polynomial.C a * P) = MvPolynomial.C a * laiL n P := by
  unfold laiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, map_mul]
  ring

lemma laiL_sum {κ : Type*} (s : Finset κ) (n : ℕ) (P : κ → ℚ[X]) :
    laiL n (∑ k ∈ s, P k) = ∑ k ∈ s, laiL n (P k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [laiL_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, laiL_add, ih]

/-- `L_n(f g)` for polynomials of degree `< N` in terms of the Hankel values. -/
lemma laiL_mul_expand (n N : ℕ) (f g : ℚ[X]) (hf : f.natDegree < N) (hg : g.natDegree < N) :
    laiL n (f * g) = ∑ i ∈ range N, ∑ j ∈ range N,
      MvPolynomial.C (f.coeff i) * MvPolynomial.C (g.coeff j) * laiL n (Polynomial.X ^ (i + j)) := by
  have hf' : f = ∑ i ∈ range N, Polynomial.C (f.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' f N hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have hg' : g = ∑ j ∈ range N, Polynomial.C (g.coeff j) * Polynomial.X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range' g N hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have : f * g = ∑ i ∈ range N, ∑ j ∈ range N,
      Polynomial.C (f.coeff i * g.coeff j) * Polynomial.X ^ (i + j) := by
    conv_lhs => rw [hf', hg']
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.C_mul, pow_add]; ring
  rw [this, laiL_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [laiL_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [laiL_C_mul, map_mul]

end Linear

lemma sum_range_fin2 {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → ℕ → M) :
    ∑ i ∈ range N, ∑ j ∈ range N, g i j = ∑ i : Fin N, ∑ j : Fin N, g i j := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]

section Gram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of coefficients of the basis `f`. -/
noncomputable def coeffMat (n : ℕ) (f : ι → ℚ[X]) : Matrix ι (Fin (3 * n)) MP :=
  Matrix.of fun x i => MvPolynomial.C ((f x).coeff i)

theorem gram_eq (n : ℕ) (f : ι → ℚ[X]) (hf : ∀ x, (f x).natDegree < 3 * n) :
    (Matrix.of fun x y => laiL n (f x * f y)) = coeffMat n f * laiMat n * (coeffMat n f).transpose := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.of_apply, laiL_mul_expand n (3 * n) _ _ (hf x) (hf y), Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coeffMat, Matrix.of_apply, laiMat, Finset.sum_mul]
  rw [sum_range_fin2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `det Gram = (det B)² det laiMat` for a basis indexed by `Fin (3n)`. -/
theorem gram_det_fin (n : ℕ) (f : Fin (3 * n) → ℚ[X]) (hf : ∀ x, (f x).natDegree < 3 * n) :
    (Matrix.of fun x y => laiL n (f x * f y)).det = (coeffMat n f).det ^ 2 * (laiMat n).det := by
  rw [gram_eq n f hf, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Same for a basis indexed by `ι` with `e : ι ≃ Fin (3n)`. -/
theorem gram_det (n : ℕ) (e : ι ≃ Fin (3 * n)) (f : ι → ℚ[X]) (hf : ∀ x, (f x).natDegree < 3 * n) :
    (Matrix.of fun x y => laiL n (f x * f y)).det =
      (coeffMat n (fun z => f (e.symm z))).det ^ 2 * (laiMat n).det := by
  have h := gram_det_fin n (fun z => f (e.symm z)) (fun z => hf _)
  rw [← h]
  rw [← Matrix.det_submatrix_equiv_self e.symm (Matrix.of fun x y => laiL n (f x * f y))]
  rfl

end Gram

section Norm

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ν_p = v_p(∏_{i<3n} i!²)`. -/
noncomputable def nuP (n p : ℕ) : ℕ := padicValNat p (∏ i ∈ range (3 * n), (i ! : ℕ) ^ 2)

/-- `v_p(J_n) ≥ v_p(det L_n(t^{i+j})) - ν_p`. -/
theorem GV_laiJ_of_det (n : ℕ) (e : ℤ) (h : GV p e (laiMat n).det) :
    GV p (e - nuP n p) (laiJ n) := by
  set c : ℕ := ∏ i ∈ range (3 * n), (i ! : ℕ) ^ 2 with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Nat.factorial_ne_zero i)
  obtain ⟨w, hw, hpw⟩ : ∃ w : ℕ, c = p ^ nuP n p * w ∧ ¬ p ∣ w := by
    have hnu : nuP n p = c.factorization p := (Nat.factorization_def c hp.out).symm
    refine ⟨c / p ^ (c.factorization p), ?_, Nat.not_dvd_ordCompl hp.out hc0⟩
    rw [hnu]
    exact (Nat.ordProj_mul_ordCompl_eq_self c p).symm
  have hq : ((∏ i ∈ range (3 * n), ((i ! : ℚ)) ^ 2)⁻¹) = (p : ℚ) ^ (-(nuP n p : ℤ)) * ((w : ℚ))⁻¹ := by
    have : (∏ i ∈ range (3 * n), ((i ! : ℚ)) ^ 2) = (c : ℚ) := by rw [hc]; push_cast; rfl
    rw [this, hw]
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [zpow_neg, zpow_natCast]
    push_cast
    rw [mul_inv]
  unfold laiJ
  rw [hq]
  have hc1 : GV p (-(nuP n p : ℤ)) (MvPolynomial.C ((p : ℚ) ^ (-(nuP n p : ℤ)) * ((w : ℚ))⁻¹) : MP) := by
    apply GV.const
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [neg_neg, show ((p : ℚ) ^ (nuP n p : ℤ)) * ((p : ℚ) ^ (-(nuP n p : ℤ)) * ((w : ℚ))⁻¹) = (w : ℚ)⁻¹ by
      rw [← mul_assoc, ← zpow_add₀ hp0]; simp]
    exact inv_natCast_mem_locRing hpw
  have := hc1.mul h
  refine this.mono (le_of_eq ?_)
  ring

end Norm
end CatalanCore.Lai
end PartLaiGram

section PartLaiOunit
/-!
# Theorem O, unit parts (content note Lemma 2.3 (iii))

For `3n < p ≤ 7n/2`, `a = p - 2n`, `A = 6n - p`, `c = p - 1 - A = 2p - 6n - 1` and a residue
`a ≤ s ≤ A` (class `M`), the unit part `u` of `c_{s+p} = p³ u` satisfies in `𝔽_p`

  `u · ∏_{r<a} (r - s)⁴ = -8 · (A!²/(2n)!³) · D_a(s) · (∏_{j=1}^{c} (s+j))²`,

`D_a(s) = ∏_{r<a} (s - r)`: the reflection `x!(p-1-x)! ≡ (-1)^{x+1}` removes `(A-s)!²`.
-/

open Finset CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Refl

variable {p : ℕ} [hp : Fact p.Prime]

/-- Reflection `x!(p-1-x)! ≡ (-1)^{x+1}` (mod `p`). -/
theorem fact_reflect (x : ℕ) (hx : x < p) :
    ((x ! : ℕ) : ZMod p) * (((p - 1 - x) ! : ℕ) : ZMod p) = (-1) ^ (x + 1) := by
  induction x with
  | zero =>
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.sub_zero, zero_add, pow_one]
    exact wilson p
  | succ x ih =>
    have ih' := ih (by omega)
    have hcast : (((p - 1 - x : ℕ)) : ZMod p) = -((x : ZMod p) + 1) := by
      have h1 : p - 1 - x + (x + 1) = p := by omega
      have h2 := congrArg (fun z : ℕ => (z : ZMod p)) h1
      simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h2
      linear_combination h2
    have hfac : ((p - 1 - x) ! : ℕ) = (p - 1 - x) * (p - 1 - (x + 1)) ! := by
      have : p - 1 - x = (p - 1 - (x + 1)) + 1 := by omega
      conv_lhs => rw [this]
      rw [Nat.factorial_succ]; rw [← this]
    rw [hfac, Nat.cast_mul, hcast] at ih'
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast at ih' ⊢
    linear_combination (-1 : ZMod p) * ih'

end Refl

section Arith

variable {n p : ℕ}

lemma mod6_O (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) : 6 * n % p = 6 * n - p := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma mod2_O (h1 : 3 * n < p) : 2 * n % p = 2 * n := Nat.mod_eq_of_lt (by omega)

lemma div6_O (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) : 6 * n / p = 1 := by
  rw [Nat.div_eq_iff (by omega)]
  omega

lemma div2_O (h1 : 3 * n < p) : 2 * n / p = 0 := Nat.div_eq_of_lt (by omega)

end Arith

section Unit

variable {p : ℕ} [hp : Fact p.Prime]

lemma fz_ne_zero {m : ℕ} (hm : m < p) : fz p m ≠ 0 := by
  unfold fz
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial hp.out]; omega

/-- `κ` at the class `M`, node `ℓ = 1`: `-8`. -/
lemma kappa_O : kappa p 1 0 0 1 1 = -8 := by
  unfold kappa fz
  have h2 : ((2 ! : ℕ) : ZMod p) = 2 := by norm_num [Nat.factorial]
  simp [Nat.factorial, h2]
  norm_num

end Unit

theorem unit_alg {F : Type*} [Field F] (K1 K2 Ff B L D W : F) (hF : Ff ≠ 0) (hB : B ≠ 0) (hK : K2 ≠ 0)
    (hL : L ≠ 0) (h1 : Ff = L * D) (h2 : (B * (Ff * W)) ^ 2 = 1) :
    (K1 / (Ff * B)) ^ 2 * (L / (K2 * Ff)) ^ 3 * D ^ 4 = K1 ^ 2 / K2 ^ 3 * D * W ^ 2 := by
  have hD : D ≠ 0 := by rintro rfl; apply hF; rw [h1]; ring
  field_simp
  subst h1
  linear_combination (-(K1 ^ 2 * L ^ 3 * D ^ 3)) * h2

section UnitId

variable {n p : ℕ} [hp : Fact p.Prime]

/-- **Lemma 2.3 (iii), unit part on the class `M` of `3n < p ≤ 7n/2`.** -/
theorem unit_O (hn : 1 ≤ n) (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (s : ℕ) (hs1 : p - 2 * n ≤ s)
    (hs2 : s ≤ 6 * n - p) :
    ∃ u : ℕ, laiCoef n (s + p) = p ^ 3 * u ∧
      (u : ZMod p) * ∏ r ∈ range (p - 2 * n), ((r : ZMod p) - (s : ZMod p)) ^ 4 =
        -8 * ((fz p (6 * n - p)) ^ 2 / (fz p (2 * n)) ^ 3) *
          ((s.descFactorial (p - 2 * n) : ℕ) : ZMod p) *
          (∏ j ∈ range (2 * p - 6 * n - 1), (((s + 1 + j : ℕ)) : ZMod p)) ^ 2 := by
  have h8 : 8 * n < p ^ 2 := by nlinarith
  have h3 : 3 ≤ p := by omega
  have hpos : 0 < p := hp.out.pos
  have hk : s + p ≤ 6 * n := by omega
  obtain ⟨u, hu, hu2, -⟩ := laiCoef_unit (p := p) h8 h3 (s + p) hk
  have hsp : s < p := by omega
  have hsmod : (s + p) % p = s := by rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hsp
  have hsdiv : (s + p) / p = 1 := by
    rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt hsp]
  have h6 := mod6_O h1 h2
  have h2' := mod2_O (n := n) (p := p) h1
  have hsig : sig n p s = 3 := by
    unfold sig r6 r2
    rw [h6, h2']
    split_ifs <;> omega
  have hb : bflag n p s = 0 := by
    unfold bflag r6; rw [h6]; split_ifs <;> omega
  have he : eflag n p s = 1 := by
    unfold eflag r2; rw [h2']; split_ifs <;> omega
  rw [hsmod, hsig] at hu
  rw [hsmod, hsdiv, hb, he] at hu2
  refine ⟨u, hu, ?_⟩
  have hq6 : q6 n p = 1 := div6_O h1 h2
  have hq2 : q2 n p = 0 := div2_O h1
  have hr6 : r6 n p = 6 * n - p := h6
  have hr2 : r2 n p = 2 * n := h2'
  rw [hq6, hq2, hr6, hr2, kappa_O] at hu2
  rw [hu2]
  -- factorial data
  have hA : 6 * n - p < p := by omega
  have hFf : fz p s ≠ 0 := fz_ne_zero hsp
  have hB : fz p (6 * n - p - s) ≠ 0 := fz_ne_zero (by omega)
  have hK : fz p (2 * n) ≠ 0 := fz_ne_zero (by omega)
  have hL : fz p (s - (p - 2 * n)) ≠ 0 := fz_ne_zero (by omega)
  set a := p - 2 * n with ha
  set c := 2 * p - 6 * n - 1 with hc
  have hdesc : fz p s = fz p (s - a) * ((s.descFactorial a : ℕ) : ZMod p) := by
    unfold fz
    rw [← Nat.cast_mul, Nat.factorial_mul_descFactorial (by omega)]
  have hasc : fz p (s + c) = fz p s * ∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p) := by
    unfold fz
    rw [← Nat.factorial_mul_ascFactorial s c, Nat.cast_mul, Nat.ascFactorial_eq_prod_range]
    push_cast; rfl
  have hrefl : fz p (6 * n - p - s) * fz p (s + c) = (-1) ^ (6 * n - p - s + 1) := by
    have := fact_reflect (p := p) (6 * n - p - s) (by omega)
    have e : p - 1 - (6 * n - p - s) = s + c := by omega
    rw [e] at this
    exact this
  have hsq : (fz p (6 * n - p - s) * (fz p s * ∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p))) ^ 2 = 1 := by
    rw [← hasc, hrefl, ← pow_mul, mul_comm, pow_mul]; simp
  -- the product of (r - s)^4
  have hprod : ∏ r ∈ range a, ((r : ZMod p) - (s : ZMod p)) ^ 4 = ((s.descFactorial a : ℕ) : ZMod p) ^ 4 := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun r hr => ?_
    have hra : r < a := Finset.mem_range.1 hr
    rw [Nat.cast_sub (by omega)]
    have : ((r : ZMod p) - (s : ZMod p)) ^ 4 = ((s : ZMod p) - (r : ZMod p)) ^ 4 := by ring
    rw [this]
  rw [hprod]
  have e1 : 6 * n - p + 0 * p - s = 6 * n - p - s := by omega
  have e2 : 2 * n + s - 1 * p = s - a := by omega
  unfold chat
  rw [e1, e2]
  have := unit_alg (fz p (6 * n - p)) (fz p (2 * n)) (fz p s) (fz p (6 * n - p - s)) (fz p (s - a))
    ((s.descFactorial a : ℕ) : ZMod p) (∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p)) hFf hB hK hL hdesc hsq
  linear_combination (-8 : ZMod p) * this

end UnitId
end CatalanCore.Lai
end PartLaiOunit

section PartLaiO
/-!
# Theorem O (content note, §3): `3n < p ≤ 7n/2 ⟹ v_p(J_n) ≥ -6(p - 2n)`

Basis (outer CRT): `Π = ∏_{r<a} (t + r)²`, `a = p - 2n`;
`e_{r,0} = Π/(t+r)²` (`π = -2`), `e_{r,1} = Π/(t+r)` (`π = -1`), `g_j = t^j Π`, `j < 7n - 2p`
(`π = 0`).  Entries satisfy `v ≥ π + π'` by the node lemmas (`laiL_ge_except`), except `g × g`, whose
`M`-nodes `(ℓ = 1)` have `p⁻¹`-coefficient `-7 · Σ u_s F(-s)` ≡ `-7 · Σ_{s ∈ F_p} H(s)` = 0
(`unit_O`, content Lemma 2.4).
-/

open Finset Polynomial MvPolynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Poly

variable {p : ℕ} [hp : Fact p.Prime]

lemma IntPoly.X : IntPoly p (Polynomial.X : ℚ[X]) := by
  intro i
  rw [Polynomial.coeff_X]
  split_ifs
  · exact (LocRing p).one_mem
  · exact (LocRing p).zero_mem

lemma IntPoly.X_add_C_nat (r : ℕ) : IntPoly p (Polynomial.X + Polynomial.C (r : ℚ)) := by
  have := IntPoly.X_add_C (p := p) (r : ℤ)
  simpa using this

lemma IntPoly.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, IntPoly p (f i)) :
    IntPoly p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro i; rw [Finset.prod_empty, Polynomial.coeff_one]; split_ifs
    · exact (LocRing p).one_mem
    · exact (LocRing p).zero_mem
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Poly

section Data

/-- `X^w ∏_{r<a} (X + r)^{ν r}`. -/
noncomputable def Pd (a w : ℕ) (ν : Fin a → ℕ) : ℚ[X] :=
  Polynomial.X ^ w * ∏ r : Fin a, (Polynomial.X + Polynomial.C ((r : ℕ) : ℚ)) ^ ν r

lemma Pd_mul (a w1 w2 : ℕ) (ν1 ν2 : Fin a → ℕ) :
    Pd a w1 ν1 * Pd a w2 ν2 = Pd a (w1 + w2) (fun r => ν1 r + ν2 r) := by
  unfold Pd
  rw [pow_add, show ∏ r : Fin a, (Polynomial.X + Polynomial.C ((r : ℕ) : ℚ)) ^ (ν1 r + ν2 r) =
    (∏ r : Fin a, (Polynomial.X + Polynomial.C ((r : ℕ) : ℚ)) ^ ν1 r) *
      ∏ r : Fin a, (Polynomial.X + Polynomial.C ((r : ℕ) : ℚ)) ^ ν2 r by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun r _ => pow_add _ _ _]
  ring

/-- exponent of `(X + s)` in `Pd a w ν`. -/
def mmF (a : ℕ) (ν : Fin a → ℕ) (s : ℕ) : ℕ := if h : s < a then ν ⟨s, h⟩ else 0

/-- the cofactor. -/
noncomputable def RRF (a w : ℕ) (ν : Fin a → ℕ) (s : ℕ) : ℚ[X] :=
  if h : s < a then
    Polynomial.X ^ w * ∏ r ∈ (Finset.univ : Finset (Fin a)).erase ⟨s, h⟩,
      (Polynomial.X + Polynomial.C ((r : ℕ) : ℚ)) ^ ν r
  else Pd a w ν

lemma Pd_decomp (a w : ℕ) (ν : Fin a → ℕ) (s : ℕ) :
    Pd a w ν = (Polynomial.X + Polynomial.C (s : ℚ)) ^ (mmF a ν s) * RRF a w ν s := by
  unfold mmF RRF
  by_cases h : s < a
  · simp only [h, dite_true]
    unfold Pd
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin a)) _ (Finset.mem_univ ⟨s, h⟩)]
    simp only
    ring
  · simp [h]

lemma RRF_int {p : ℕ} [Fact p.Prime] (a w : ℕ) (ν : Fin a → ℕ) (s : ℕ) : IntPoly p (RRF a w ν s) := by
  unfold RRF
  by_cases h : s < a
  · simp only [h, dite_true]
    exact (IntPoly.X.pow w).mul (IntPoly.prod _ _ fun r _ => (IntPoly.X_add_C_nat _).pow _)
  · simp only [h, dite_false]
    unfold Pd
    exact (IntPoly.X.pow w).mul (IntPoly.prod _ _ fun r _ => (IntPoly.X_add_C_nat _).pow _)

end Data

section OFam

/-- Index type of the basis of Theorem O. -/
abbrev OIdx (a g : ℕ) : Type := (Σ _r : Fin a, Fin 2) ⊕ Fin g

/-- The basis, over `ℚ`. -/
noncomputable def fO (a g : ℕ) : OIdx a g → ℚ[X] :=
  crtFam (fun r : Fin a => -(((r : ℕ)) : ℚ)) (fun _ => 2) g

/-- exponents of `(X + r)`. -/
def nuO {a g : ℕ} : OIdx a g → Fin a → ℕ
  | Sum.inl ⟨r0, i⟩ => fun r => if r = r0 then (i : ℕ) else 2
  | Sum.inr _ => fun _ => 2

/-- power of `X`. -/
def wO {a g : ℕ} : OIdx a g → ℕ
  | Sum.inl _ => 0
  | Sum.inr j => (j : ℕ)

/-- potentials `π`. -/
def piO {a g : ℕ} : OIdx a g → ℤ
  | Sum.inl ⟨_, i⟩ => (i : ℤ) - 2
  | Sum.inr _ => 0

lemma fO_eq {a g : ℕ} (x : OIdx a g) : fO a g x = Pd a (wO x) (nuO x) := by
  have hX : ∀ r : Fin a, (Polynomial.X - Polynomial.C (-(((r : ℕ)) : ℚ)) : ℚ[X]) =
      Polynomial.X + Polynomial.C ((r : ℕ) : ℚ) := by
    intro r; rw [Polynomial.C_neg, sub_neg_eq_add]
  rcases x with ⟨r0, i⟩ | j
  · simp only [fO, crtFam, Sum.elim_inl, crtE, wO, nuO, Pd, pow_zero, one_mul]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin a)) _ (Finset.mem_univ r0)]
    simp only [hX, if_true]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    have : r ≠ r0 := (Finset.mem_erase.1 hr).1
    simp [this]
  · simp only [fO, crtFam, Sum.elim_inr, crtG, wO, nuO, Pd, hX]

lemma nuO_ge {a g : ℕ} (x : OIdx a g) (r : Fin a) : piO x + 2 ≤ (nuO x r : ℤ) := by
  rcases x with ⟨r0, i⟩ | j
  · have hi := i.2
    simp only [piO, nuO]
    split_ifs with h
    · omega
    · omega
  · simp [piO, nuO]

lemma piO_le {a g : ℕ} (x : OIdx a g) : piO x ≤ 0 := by
  rcases x with ⟨r0, i⟩ | j
  · have hi := i.2; simp only [piO]; omega
  · simp [piO]

lemma piO_inl_le {a g : ℕ} (r0 : Fin a) (i : Fin 2) : piO (Sum.inl ⟨r0, i⟩ : OIdx a g) ≤ -1 := by
  have hi := i.2; simp only [piO]; omega

lemma piO_pair_le {a g : ℕ} (x y : OIdx a g) (h : ¬ (∃ i j, x = Sum.inr i ∧ y = Sum.inr j)) :
    piO x + piO y ≤ -1 := by
  rcases x with ⟨r0, i⟩ | j <;> rcases y with ⟨r1, i1⟩ | j1
  · have := piO_inl_le (g := g) r0 i; have := piO_le (Sum.inl ⟨r1, i1⟩ : OIdx a g); omega
  · have := piO_inl_le (g := g) r0 i; have := piO_le (Sum.inr j1 : OIdx a g); omega
  · have := piO_inl_le (g := g) r1 i1; have := piO_le (Sum.inr j : OIdx a g); omega
  · exact absurd ⟨j, j1, rfl, rfl⟩ h

end OFam

section Entries

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

lemma sig_O (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (s : ℕ) :
    sig n p s = (if s ≤ 6 * n - p then 0 else 2) + (if p - 2 * n ≤ s then 3 else 0) := by
  unfold sig r6 r2
  rw [mod6_O h1 h2, mod2_O h1]

lemma mod_O (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (k : ℕ) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p) :
    k % p = k - p ∧ p ≤ k := by
  have hpk : p ≤ k := by
    by_contra hc
    have : k / p = 0 := Nat.div_eq_of_lt (by omega)
    omega
  refine ⟨?_, hpk⟩
  rw [Nat.mod_eq_sub_mod hpk, Nat.mod_eq_of_lt (by omega)]

/-- **Entry bounds** for the pairs other than `g × g`. -/
theorem entry_nongg (hn : 1 ≤ n) (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (x y : OIdx (p - 2 * n) (7 * n - 2 * p))
    (hxy : ¬ (∃ i j, x = Sum.inr i ∧ y = Sum.inr j)) :
    GV p (piO x + piO y) (laiL n (fO _ _ x * fO _ _ y)) := by
  have h8 : 8 * n < p ^ 2 := by nlinarith
  have h3 : 3 ≤ p := by omega
  have hneg := piO_pair_le x y hxy
  rw [fO_eq, fO_eq, Pd_mul]
  have key := laiL_ge_except (p := p) n h8 h3 (Pd (p - 2 * n) (wO x + wO y) (fun r => nuO x r + nuO y r))
    (mmF (p - 2 * n) (fun r => nuO x r + nuO y r))
    (RRF (p - 2 * n) (wO x + wO y) (fun r => nuO x r + nuO y r))
    (fun s _ => RRF_int _ _ _ s) (fun s _ => Pd_decomp _ _ _ s) (piO x + piO y) ∅
    (Finset.empty_subset _) ?_ ?_
  · simpa using key
  · intro k hk _ hl
    obtain ⟨hmod, hpk⟩ := mod_O h1 h2 k hk hl
    rw [hmod, sig_O h1 h2]
    by_cases hs : k - p < p - 2 * n
    · have hle : k - p ≤ 6 * n - p := by omega
      simp only [hle, hs, if_true, not_le.2 hs, if_false, mmF, dite_true]
      have := nuO_ge x ⟨k - p, hs⟩
      have := nuO_ge y ⟨k - p, hs⟩
      omega
    · have hle : k - p ≤ 6 * n - p := by omega
      have hs' : p - 2 * n ≤ k - p := by omega
      simp only [hle, hs, hs', if_true, if_false, mmF, dite_false]
      omega
  · intro k hk _ hkp
    rw [sig_O h1 h2]
    by_cases hs : k < p - 2 * n
    · have hle : k ≤ 6 * n - p := by omega
      left
      simp only [hle, hs, if_true, not_le.2 hs, if_false]
      omega
    · have hs' : p - 2 * n ≤ k := by omega
      left
      simp only [hs, hs', if_true, if_false, mmF, dite_false]
      split_ifs <;> omega

end Entries

section ModSum

variable {p : ℕ} [hp : Fact p.Prime]

lemma sum_range_zmod {K : Type*} [AddCommMonoid K] (f : ZMod p → K) :
    ∑ s : ZMod p, f s = ∑ s ∈ range p, f (s : ZMod p) := by
  rw [Finset.sum_range]
  symm
  refine Fintype.sum_bijective (fun i : Fin p => ((i : ℕ) : ZMod p)) ?_ _ _ (fun _ => rfl)
  constructor
  · intro i j hij
    have hi := i.2; have hj := j.2
    have := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
    exact Fin.ext this
  · intro z
    refine ⟨⟨z.val, ZMod.val_lt z⟩, ?_⟩
    simp

/-- **The vanishing power sum behind Theorem O (content Lemma 2.4).** -/
theorem modsum_zero (a A c w : ℕ) (hA : A < p) (hc : c = p - 1 - A) (hdeg : a + 2 * c + w ≤ p - 2)
    (K' : ZMod p) :
    ∑ s ∈ Finset.Icc a A, (-8 * K' * (∏ r ∈ range a, ((s : ZMod p) - (r : ZMod p))) *
      (∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p)) ^ 2 * (-(s : ZMod p)) ^ w) = 0 := by
  classical
  set H : (ZMod p)[X] := Polynomial.C (-8 * K') * (∏ r ∈ range a, (Polynomial.X - Polynomial.C (r : ZMod p))) *
    (∏ j ∈ range c, (Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p))) ^ 2 * (-Polynomial.X) ^ w with hH
  have hHe : ∀ s : ℕ, H.eval (s : ZMod p) = -8 * K' * (∏ r ∈ range a, ((s : ZMod p) - (r : ZMod p))) *
      (∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p)) ^ 2 * (-(s : ZMod p)) ^ w := by
    intro s
    rw [hH]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_neg]
    congr 3
    refine Finset.prod_congr rfl fun j _ => ?_
    push_cast; ring
  have hlin : ∀ (s : Finset ℕ) (f : ℕ → (ZMod p)[X]), (∀ i ∈ s, (f i).natDegree ≤ 1) →
      (∏ i ∈ s, f i).natDegree ≤ s.card := fun s f h =>
    (Polynomial.natDegree_prod_le s f).trans (by simpa using Finset.sum_le_card_nsmul s _ 1 h)
  have hP1 : (∏ r ∈ range a, (Polynomial.X - Polynomial.C (r : ZMod p)) : (ZMod p)[X]).natDegree ≤ a := by
    have := hlin (range a) (fun r => Polynomial.X - Polynomial.C (r : ZMod p))
      (fun i _ => (Polynomial.natDegree_X_sub_C _).le)
    simpa using this
  have hP2 : (∏ j ∈ range c, (Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p)) : (ZMod p)[X]).natDegree ≤ c := by
    have := hlin (range c) (fun j => Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p))
      (fun i _ => (Polynomial.natDegree_X_add_C _).le)
    simpa using this
  have hdegH : H.natDegree ≤ p - 2 := by
    refine le_trans ?_ hdeg
    rw [hH]
    have h1 := Polynomial.natDegree_mul_le (p := Polynomial.C (-8 * K') * (∏ r ∈ range a, (Polynomial.X - Polynomial.C (r : ZMod p))) *
      (∏ j ∈ range c, (Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p))) ^ 2) (q := (-Polynomial.X) ^ w)
    have h2 := Polynomial.natDegree_mul_le (p := Polynomial.C (-8 * K') * (∏ r ∈ range a, (Polynomial.X - Polynomial.C (r : ZMod p))))
      (q := (∏ j ∈ range c, (Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p))) ^ 2)
    have h3 := Polynomial.natDegree_mul_le (p := Polynomial.C (-8 * K')) (q := (∏ r ∈ range a, (Polynomial.X - Polynomial.C (r : ZMod p))))
    have h4 : ((∏ j ∈ range c, (Polynomial.X + Polynomial.C ((1 + j : ℕ) : ZMod p))) ^ 2).natDegree ≤ 2 * c :=
      Polynomial.natDegree_pow_le.trans (by omega)
    have h5 : ((-Polynomial.X : (ZMod p)[X]) ^ w).natDegree ≤ w :=
      Polynomial.natDegree_pow_le.trans (by simp)
    rw [Polynomial.natDegree_C] at h3
    omega
  have hzero := CatalanCore.Content.sum_zmod_eval_eq_zero (p := p) (K := ZMod p) H hdegH
  simp only [ZMod.castHom_self, RingHom.id_apply] at hzero
  rw [sum_range_zmod (fun s => H.eval s)] at hzero
  have hsub : ∑ s ∈ Finset.Icc a A, H.eval (s : ZMod p) = ∑ s ∈ range p, H.eval (s : ZMod p) := by
    refine Finset.sum_subset (fun s hs => Finset.mem_range.2 (by have := (Finset.mem_Icc.1 hs).2; omega)) ?_
    intro s hs hns
    have hsp : s < p := Finset.mem_range.1 hs
    rw [hHe]
    have : s < a ∨ A < s := by
      by_contra hcon; push_neg at hcon
      exact hns (Finset.mem_Icc.2 ⟨hcon.1, hcon.2⟩)
    rcases this with h | h
    · have : (∏ r ∈ range a, ((s : ZMod p) - (r : ZMod p))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 h) (sub_self _)
      rw [this]; ring
    · have : (∏ j ∈ range c, (((s + 1 + j : ℕ)) : ZMod p)) = 0 := by
        refine Finset.prod_eq_zero (i := p - s - 1) (Finset.mem_range.2 (by omega)) ?_
        have : s + 1 + (p - s - 1) = p := by omega
        rw [this, ZMod.natCast_self]
      rw [this]; ring
  rw [← hzero, ← hsub]
  exact Finset.sum_congr rfl fun s _ => (hHe s).symm

end ModSum

section GG

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

lemma eval_Pd4 (a w s : ℕ) :
    (Pd a w (fun _ => 4)).eval (-(s : ℚ)) =
      (((-(s : ℤ)) ^ w * ∏ r ∈ range a, ((r : ℤ) - s) ^ 4 : ℤ) : ℚ) := by
  unfold Pd
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_prod,
    Polynomial.eval_add, Polynomial.eval_C]
  rw [Fin.prod_univ_eq_prod_range (fun r => (-(s : ℚ) + (r : ℚ)) ^ 4) a]
  push_cast
  congr 1
  refine Finset.prod_congr rfl fun r _ => ?_
  ring

lemma desc_cast (a s : ℕ) (hs : a ≤ s) :
    ((s.descFactorial a : ℕ) : ZMod p) = ∏ r ∈ range a, ((s : ZMod p) - (r : ZMod p)) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun r hr => ?_
  have hra : r < a := Finset.mem_range.1 hr
  rw [Nat.cast_sub (by omega)]

lemma vL_O (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (s : ℕ) (hs1 : p - 2 * n ≤ s) (hs2 : s ≤ 6 * n - p) :
    vL n p (s + p) 1 = -7 := by
  have hpos : 0 < p := hp.out.pos
  have e1 : (s + p) / p = 1 := by
    rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt (by omega)]
  have e2 : (2 * n + (s + p)) / p = 2 := by
    rw [Nat.div_eq_iff (by omega)]; omega
  have e3 : (6 * n - (s + p)) / p = 0 := Nat.div_eq_of_lt (by omega)
  unfold vL laiDelta
  rw [e1, e2, e3]
  norm_num [Hq, Finset.sum_range_succ]

end GG

section GG2

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- **The `g × g` entries of Theorem O** have `v ≥ 0` (no loss): the `M`-nodes with `ℓ = 1` cancel. -/
theorem entry_gg (hn : 1 ≤ n) (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) (i j : Fin (7 * n - 2 * p)) :
    GV p 0 (laiL n (fO (p - 2 * n) (7 * n - 2 * p) (Sum.inr i) * fO (p - 2 * n) (7 * n - 2 * p) (Sum.inr j))) := by
  have h8 : 8 * n < p ^ 2 := by nlinarith
  have h3 : 3 ≤ p := by omega
  have hpos : 0 < p := hp.out.pos
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  set a := p - 2 * n with ha
  set A := 6 * n - p with hA
  set c := 2 * p - 6 * n - 1 with hc
  set w : ℕ := (i : ℕ) + j with hw
  have hi := i.2
  have hj := j.2
  have hFeq : fO a (7 * n - 2 * p) (Sum.inr i) * fO a (7 * n - 2 * p) (Sum.inr j) = Pd a w (fun _ => 4) := by
    rw [fO_eq, fO_eq, Pd_mul]; simp [nuO, wO, hw]
  rw [hFeq]
  have hFint : IntPoly p (Pd a w (fun _ => 4)) := by
    unfold Pd
    exact (IntPoly.X.pow w).mul (IntPoly.prod _ _ fun r _ => (IntPoly.X_add_C_nat _).pow _)
  set F := Pd a w (fun _ => 4) with hFdef
  set E : Finset ℕ := (Finset.Icc a A).image (· + p) with hE
  have hEsub : E ⊆ range (6 * n + 1) := by
    intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hk
    have := (Finset.mem_Icc.1 hs).2
    exact Finset.mem_range.2 (by omega)
  have key := laiL_ge_except (p := p) n h8 h3 F (mmF a fun _ => 4) (RRF a w fun _ => 4)
    (fun s _ => RRF_int _ _ _ s) (fun s _ => Pd_decomp _ _ _ s) 0 E hEsub ?_ ?_
  rotate_left
  · intro k hk hkE hl
    obtain ⟨hmod, hpk⟩ := mod_O h1 h2 k hk hl
    rw [hmod, sig_O h1 h2]
    by_cases hs : k - p < a
    · have hle : k - p ≤ A := by omega
      simp only [hle, hs, if_true, not_le.2 hs, if_false, mmF, dite_true]
      omega
    · exfalso
      exact hkE (Finset.mem_image.2 ⟨k - p, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩)
  · intro k hk _ hkp
    rw [sig_O h1 h2]
    by_cases hs : k < a
    · right
      simp only [mmF, hs, dite_true]
      omega
    · left
      simp only [mmF, hs, dite_false]
      split_ifs <;> omega
  -- the nodes of `M`
  choose! u hu1 hu2 using (fun s (hs : s ∈ Finset.Icc a A) =>
    unit_O (p := p) hn h1 h2 s (Finset.mem_Icc.1 hs).1 (Finset.mem_Icc.1 hs).2)
  have hnode : ∀ s ∈ Finset.Icc a A, GV p 0 (laiNd n (s + p) F -
      MvPolynomial.C ((p : ℚ) ^ 3 * ((p : ℚ) ^ 4)⁻¹ * (u s : ℚ) * F.eval (-(s : ℚ)) * (-7)) * MvPolynomial.X (1 : Fin 3)) := by
    intro s hs
    have hs1 := (Finset.mem_Icc.1 hs).1
    have hs2 := (Finset.mem_Icc.1 hs).2
    have hsp : s < p := by omega
    have hmod : (s + p) % p = s := by rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt hsp
    have hdiv : (s + p) / p = 1 := by rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt hsp]
    have hsig : sig n p s = 3 := by rw [sig_O h1 h2]; split_ifs <;> omega
    have hcoef : (laiCoef n (s + p) : ℚ) = (p : ℚ) ^ (sig n p ((s + p) % p)) * (u s : ℚ) := by
      rw [hmod, hsig]; exact_mod_cast hu1 s hs
    have hl : 1 ≤ (s + p) / p := by omega
    have := node_lead (p := p) n (s + p) h8 h3 (by omega) hl (u s) hcoef 0 F hFint
    rw [hmod, hsig, hdiv, pow_zero, one_mul] at this
    have hv := vL_O h1 h2 s hs1 hs2
    simp only [leadF, Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul, hv] at this
    have e : (p : ℚ) ^ 3 * ((p : ℚ) ^ 4)⁻¹ * (u s : ℚ) * F.eval (-(s : ℚ)) * (-7) =
        (p : ℚ) ^ 3 * 1 * ((p : ℚ) ^ 4)⁻¹ * (u s : ℚ) * F.eval (-(s : ℚ)) * (-7) := by ring
    rw [e]
    exact this
  -- reorganise the exceptional sum
  have hsumE : ∑ k ∈ E, laiNd n k F = ∑ s ∈ Finset.Icc a A, laiNd n (s + p) F := by
    rw [hE, Finset.sum_image]
    intro x _ y _ hxy
    simpa using hxy
  set lead : ℕ → ℚ := fun s => (p : ℚ) ^ 3 * ((p : ℚ) ^ 4)⁻¹ * (u s : ℚ) * F.eval (-(s : ℚ)) * (-7) with hlead
  have hsplit : laiL n F = (laiL n F - ∑ k ∈ E, laiNd n k F) +
      (∑ s ∈ Finset.Icc a A, (laiNd n (s + p) F - MvPolynomial.C (lead s) * MvPolynomial.X (1 : Fin 3))) +
      MvPolynomial.C (∑ s ∈ Finset.Icc a A, lead s) * MvPolynomial.X (1 : Fin 3) := by
    rw [hsumE, Finset.sum_sub_distrib, ← Finset.sum_mul, ← map_sum]; ring
  -- the leading coefficients sum to an element of `ℤ_(p)`
  set N0 : ℤ := ∑ s ∈ Finset.Icc a A, (u s : ℤ) * ((-(s : ℤ)) ^ w * ∏ r ∈ range a, ((r : ℤ) - s) ^ 4) with hN0
  have hN0z : (N0 : ZMod p) = 0 := by
    have hdeg : a + 2 * c + w ≤ p - 2 := by omega
    have hmod := modsum_zero (p := p) a A c w (by omega) (by omega) hdeg
      ((fz p A) ^ 2 / (fz p (2 * n)) ^ 3)
    rw [hN0]
    push_cast
    rw [← hmod]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hu2 s hs
    rw [desc_cast a s (Finset.mem_Icc.1 hs).1] at this
    calc (u s : ZMod p) * ((-(s : ZMod p)) ^ w * ∏ r ∈ range a, ((r : ZMod p) - (s : ZMod p)) ^ 4)
        = ((u s : ZMod p) * ∏ r ∈ range a, ((r : ZMod p) - (s : ZMod p)) ^ 4) * (-(s : ZMod p)) ^ w := by ring
      _ = _ := by rw [this]
  have hdvd : (p : ℤ) ∣ N0 := (ZMod.intCast_zmod_eq_zero_iff_dvd N0 p).1 hN0z
  obtain ⟨q, hq⟩ := hdvd
  have hleadsum : ∑ s ∈ Finset.Icc a A, lead s = ((-7 * q : ℤ) : ℚ) := by
    have h1' : ∀ s : ℕ, F.eval (-(s : ℚ)) = (((-(s : ℤ)) ^ w * ∏ r ∈ range a, ((r : ℤ) - s) ^ 4 : ℤ) : ℚ) :=
      fun s => eval_Pd4 a w s
    have : ∑ s ∈ Finset.Icc a A, lead s = (p : ℚ) ^ 3 * ((p : ℚ) ^ 4)⁻¹ * (-7) * (N0 : ℚ) := by
      rw [hN0]; push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hlead]; simp only []
      rw [h1' s]; push_cast; ring
    rw [this, hq]
    push_cast
    field_simp
  have hmem : ∑ s ∈ Finset.Icc a A, lead s ∈ LocRing p := by
    rw [hleadsum]; exact_mod_cast int_mem_locRing (ℓ := p) (-7 * q)
  rw [hsplit]
  refine (key.add (GV.sum hnode)).add ?_
  have := GV_CX_nat (p := p) 0 (∑ s ∈ Finset.Icc a A, lead s) 1 (by simpa using hmem)
  simpa using this

end GG2

section ThmO

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

lemma nuP_zero (h : 3 * n ≤ p) : nuP n p = 0 := by
  unfold nuP
  rw [← Nat.factorization_def _ hp.out]
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have := (Prime.dvd_finset_prod_iff hp.out.prime _).1 hd
  obtain ⟨i, hi, hdi⟩ := this
  have hi' := Finset.mem_range.1 hi
  have := hp.out.prime.dvd_of_dvd_pow hdi
  rw [Nat.Prime.dvd_factorial hp.out] at this
  omega

lemma inv_intCast_mem (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : ((z : ℚ))⁻¹ ∈ LocRing p := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, z = m ∨ z = -(m : ℤ) := ⟨z.natAbs, Int.natAbs_eq z⟩
  rcases hm with rfl | rfl
  · have hna : ¬ p ∣ m := fun h => hz (Int.natCast_dvd_natCast.2 h)
    simpa using inv_natCast_mem_locRing (ℓ := p) hna
  · have hna : ¬ p ∣ m := fun h => hz ((dvd_neg).2 (Int.natCast_dvd_natCast.2 h))
    have := (LocRing p).neg_mem (inv_natCast_mem_locRing (ℓ := p) hna)
    simpa [inv_neg] using this

lemma sum_piO (a g : ℕ) : ∑ x : OIdx a g, piO x = -3 * (a : ℤ) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  simp only [piO, Finset.sum_const_zero, add_zero, Fin.sum_univ_two]
  simp
  ring

/-- **Theorem O (content note §3).**  For `3n < p ≤ 7n/2`: `v_p(J_n) ≥ -6(p - 2n)`. -/
theorem thmO (hn : 1 ≤ n) (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) :
    GV p (-6 * ((p - 2 * n : ℕ) : ℤ)) (laiJ n) := by
  have h8 : 8 * n < p ^ 2 := by nlinarith
  set a := p - 2 * n with ha
  set g := 7 * n - 2 * p with hg
  have hN : ∑ _r : Fin a, 2 + g = 3 * n := by simp; omega
  have hcard : Fintype.card (OIdx a g) = 3 * n := by simp [Fintype.card_sigma]; omega
  let e : OIdx a g ≃ Fin (3 * n) := Fintype.equivFinOfCardEq hcard
  have hf : ∀ x, (fO a g x).natDegree < 3 * n := fun x =>
    crtFam_natDegree_lt (fun r : Fin a => -(((r : ℕ)) : ℚ)) (fun _ => 2) g (3 * n) hN x
  -- the Gram determinant has valuation `≥ -6a`
  have hGram : GV p (-6 * (a : ℤ)) (Matrix.of fun x y : OIdx a g => laiL n (fO a g x * fO a g y)).det := by
    have := GV.det (p := p) (Matrix.of fun x y : OIdx a g => laiL n (fO a g x * fO a g y)) piO piO (by
      intro x y
      simp only [Matrix.of_apply]
      by_cases hxy : ∃ i j, x = Sum.inr i ∧ y = Sum.inr j
      · obtain ⟨i, j, rfl, rfl⟩ := hxy
        simpa [piO] using entry_gg hn h1 h2 i j
      · exact entry_nongg hn h1 h2 x y hxy)
    rw [sum_piO] at this
    refine this.mono (le_of_eq ?_); ring
  rw [gram_det n e (fO a g) hf] at hGram
  -- the change of basis is a `p`-adic unit
  set aZ : Fin a → ℤ := fun r => -((r : ℕ) : ℤ) with haZ
  set Bz : Matrix (Fin (3 * n)) (Fin (3 * n)) ℤ :=
    Matrix.of fun (z : Fin (3 * n)) (i : Fin (3 * n)) => (crtFam aZ (fun _ => 2) g (e.symm z)).coeff i with hBz
  have hmapf : ∀ x, fO a g x = (crtFam aZ (fun _ => 2) g x).map (Int.castRingHom ℚ) := by
    intro x
    rw [crtFam_map]
    unfold fO
    congr 1
  have hcoef : coeffMat n (fun z => fO a g (e.symm z)) =
      Bz.map ((MvPolynomial.C : ℚ →+* MP).comp (Int.castRingHom ℚ)) := by
    refine Matrix.ext fun z i => ?_
    simp only [coeffMat, Matrix.of_apply, Matrix.map_apply, hBz, RingHom.comp_apply]
    rw [hmapf, Polynomial.coeff_map]
  have hdetC : (coeffMat n (fun z => fO a g (e.symm z))).det =
      MvPolynomial.C (((Bz.det : ℤ) : ℚ)) := by
    rw [hcoef]
    have := RingHom.map_det ((MvPolynomial.C : ℚ →+* MP).comp (Int.castRingHom ℚ)) Bz
    simpa using this.symm
  have hnd : ¬ (p : ℤ) ∣ Bz.det := by
    refine crt_det_not_dvd p aZ ?_ (fun _ => 2) g (3 * n) hN e
    intro r r' hrr
    simp only [haZ, eq_intCast, Int.cast_neg, Int.cast_natCast, neg_inj] at hrr
    have := (ZMod.natCast_eq_natCast_iff' (r : ℕ) (r' : ℕ) p).1 hrr
    rw [Nat.mod_eq_of_lt (by have := r.2; omega), Nat.mod_eq_of_lt (by have := r'.2; omega)] at this
    exact Fin.ext this
  have hβ : ((Bz.det : ℤ) : ℚ) ≠ 0 := by
    intro h0
    apply hnd
    have : Bz.det = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  have hβi := inv_intCast_mem (p := p) Bz.det hnd
  have hβm : ((Bz.det : ℤ) : ℚ) ∈ LocRing p := int_mem_locRing _
  rw [hdetC] at hGram
  have hdet : GV p (-6 * (a : ℤ)) (laiMat n).det := by
    have hc : GV p 0 (MvPolynomial.C ((((Bz.det : ℤ) : ℚ))⁻¹ ^ 2) : MP) :=
      GV.const_loc ((LocRing p).pow_mem hβi 2)
    have := hc.mul hGram
    rw [← mul_assoc, ← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ hβ] at this
    simpa using this
  have := GV_laiJ_of_det (p := p) n _ hdet
  rw [nuP_zero (by omega)] at this
  simpa using this

end ThmO
end CatalanCore.Lai
end PartLaiO

#print axioms CatalanCore.Lai.laiU_expand
#print axioms CatalanCore.Lai.laiV_expand
#print axioms CatalanCore.Lai.laiV_zero
#print axioms CatalanCore.Lai.laiU_zero
#print axioms CatalanCore.Lai.laiCoef_unit
#print axioms CatalanCore.Lai.node_ge
#print axioms CatalanCore.Lai.node0_ge
#print axioms CatalanCore.Lai.laiL_ge_except
#print axioms CatalanCore.Lai.gram_det
#print axioms CatalanCore.Lai.GV_laiJ_of_det
#print axioms CatalanCore.Lai.unit_O
#print axioms CatalanCore.Lai.thmO
#print axioms CatalanCore.Lai.node_lead
#print axioms CatalanCore.Lai.fact_reflect
#print axioms CatalanCore.Lai.entry_nongg
#print axioms CatalanCore.Lai.entry_gg
#print axioms CatalanCore.Content.crt_indep
