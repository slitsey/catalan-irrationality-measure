module

public import CatalanCore.Arith.Hybrid.LemmaE.BTable

@[expose] public section

/-!
# Lemma E, class 1: evaluation of the residue table on the label classes

`U = [r-p, k)` (weight `0`), `P = [0, r) \ U` (weight `1`; `P₀ = [0, r-p)`, `B₁ = [k, p)`,
`B₂ = [p, r)`), zone `≥ r` (weight `2`).  `tauN` is the partner map `a ↔ a + p` on `P`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {r m j k : ℕ}

lemma TEo_big {w : ℕ} (hw : 3 ≤ w) (A B : ℕ) : TEo p j k w A B = 0 := by
  unfold TEo
  by_cases h : B - A = p
  · simp [h, show w ≠ 0 by omega, show w ≠ 2 by omega]
  · simp [h, show w ≠ 0 by omega, show w ≠ 1 by omega]

lemma TEo_two (A B : ℕ) : TEo p j k 2 A B =
    if B - A = p then (16 : ZMod p)⁻¹ * singE p j k A B else 0 := by
  unfold TEo
  by_cases h : B - A = p <;> simp [h]

lemma TEo_one {A B : ℕ} (h : B - A ≠ p) :
    TEo p j k 1 A B = (16 * ((B : ZMod p) - A))⁻¹ * singE p j k A B := by
  unfold TEo; simp [h]

lemma TE_symm' (A B : ℕ) : TE p j r k A B = TE p j r k B A := by
  by_cases h1 : A < B
  · have h2 : ¬ B < A := by omega
    simp only [TE, h1, h2, if_true, if_false, Nat.add_comm]
  · by_cases h2 : B < A
    · simp only [TE, h1, h2, if_true, if_false, Nat.add_comm]
    · have : A = B := by omega
      subst this; rfl

lemma TE_big {A B : ℕ} (hAB : A ≠ B) (h3 : 3 ≤ wE p r k A + wE p r k B) :
    TE p j r k A B = 0 := by
  rcases lt_or_gt_of_ne hAB with h | h
  · simp only [TE, h, if_true]; exact TEo_big h3 _ _
  · have h' : ¬ A < B := by omega
    simp only [TE, h', h, if_true, if_false]; exact TEo_big h3 _ _

lemma wE_U {a : ℕ} (h1 : r - p ≤ a) (h2 : a < k) (h3 : a < r) : wE p r k a = 0 := by
  unfold wE; simp [h3, h1, h2]

lemma wE_P {a : ℕ} (h : ¬ (r - p ≤ a ∧ a < k)) (h3 : a < r) : wE p r k a = 1 := by
  unfold wE; rw [if_pos h3, if_neg h]

lemma wE_Z {a : ℕ} (h : r ≤ a) : wE p r k a = 2 := by
  unfold wE; simp [Nat.not_lt.2 h]

lemma singE_full {A B : ℕ} (h1 : A < k) (h2 : k ≤ B) (h3 : A < p) (h4 : p ≤ B) :
    singE p j k A B = -(4 * ((j : ℕ) : ZMod p)⁻¹) + 1 := by
  simp [singE, h1, h2, h3, h4]

lemma singE_k {A B : ℕ} (h1 : A < k) (h2 : k ≤ B) (h4 : B < p) :
    singE p j k A B = -(4 * ((j : ℕ) : ZMod p)⁻¹) := by
  have : ¬ p ≤ B := by omega
  simp [singE, h1, h2, this]

lemma singE_zero {A B : ℕ} (hk : k < p) (h : B < k) : singE p j k A B = 0 := by
  have h1 : ¬ k ≤ B := by omega
  have h2 : ¬ p ≤ B := by omega
  simp [singE, h1, h2]

/-- `U × P` entries. -/
lemma TE_UP (S : ESetup p r m j k) {u c : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hc : c < r)
    (hcP : ¬ (r - p ≤ c ∧ c < k)) :
    TE p j r k u c = if u < c then (16 * ((c : ZMod p) - u))⁻¹ * singE p j k u c
      else (16 * ((u : ZMod p) - c))⁻¹ * singE p j k c u := by
  have hkp := S.hkp
  have hw : wE p r k u + wE p r k c = 1 := by
    rw [wE_U hu1 hu2 (by omega), wE_P hcP hc]
  by_cases h : u < c
  · simp only [TE, h, if_true, hw]
    rw [TEo_one (by omega)]
  · have h2 : c < u := by omega
    have h3 : ¬ u < c := h
    simp only [TE, h3, h2, if_true, if_false, hw, if_neg h]
    rw [TEo_one (by omega)]

/-- `U × zone` entries. -/
lemma TE_UZ (S : ESetup p r m j k) {u z : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hz : r ≤ z) :
    TE p j r k u z = if z - u = p then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1)
      else 0 := by
  have hkp := S.hkp
  have hpr := S.hpr
  have hw : wE p r k u + wE p r k z = 2 := by
    rw [wE_U hu1 hu2 (by omega), wE_Z hz]
  have h : u < z := by omega
  simp only [TE, h, if_true, hw]
  rw [TEo_two]
  by_cases hd : z - u = p
  · rw [if_pos hd, if_pos hd, singE_full hu2 (by omega) (by omega) (by omega)]
  · rw [if_neg hd, if_neg hd]

end

end CatalanCore.Arith.Hybrid
