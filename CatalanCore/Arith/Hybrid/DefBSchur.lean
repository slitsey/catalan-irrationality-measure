module

public import CatalanCore.Arith.Hybrid.DefBLam

@[expose] public section

/-!
# Theorem B: the scalar Schur complement in `𝔽_p`

`schur_Z`: for `u, w < k`, with `S̄ = Ā00 - π⁻¹ V Vᵀ` computed from the table `Tfull`,

  `S̄_{uw} = [u = w] H^{(2)}_{k-1}/16 + (1/16) ∑_{i=1}^{d} E_{ui} E_{wi}`,   `E_{ui} = 1/(u+i)`,

(the `X`-part is carried separately).  This is the harmonic-reflection identity `harm_off/harm_diag`
transported along `4k ≡ 1`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime]

lemma conv4 (hp5 : 5 ≤ p) {k : ℕ} (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (t : ZMod p) :
    4 * (4 * t - 1)⁻¹ = (t - (k : ZMod p))⁻¹ := by
  have h4 := four_ne_zmod p hp5
  have : 4 * t - 1 = 4 * (t - (k : ZMod p)) := by linear_combination hk4
  rw [this, mul_inv]
  field_simp

lemma conv4sq (hp5 : 5 ≤ p) {k : ℕ} (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (t : ZMod p) :
    16 * ((4 * t - 1)⁻¹) ^ 2 = ((t - (k : ZMod p))⁻¹) ^ 2 := by
  have h4 := four_ne_zmod p hp5
  have : 4 * t - 1 = 4 * (t - (k : ZMod p)) := by linear_combination hk4
  rw [this, mul_inv]
  field_simp
  ring

variable {j k : ℕ}

lemma Tfull_lh {u c : ℕ} (hu : u < k) (hc : k ≤ c) (hcp : c < p) :
    Tfull p j k u c = (16 * ((c : ZMod p) - u))⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  unfold Tfull TB
  rw [if_pos (by omega), if_neg (by omega), if_pos hu, if_pos hcp]

lemma Tfull_ll {u w : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (huw : u < w)
    (hw : w < k) :
    Tfull p j k u w = (16 * ((w : ZMod p) - u))⁻¹ *
      ∑ t ∈ Ioc u w, (((t : ℕ) : ZMod p)⁻¹ - ((t : ZMod p) - (k : ZMod p))⁻¹) := by
  unfold Tfull TB
  rw [if_pos huw, if_pos hw]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [conv4 hp5 hk4]

lemma Tfull_dd {u : ℕ} (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1) (hu : u < k) :
    Tfull p j k u u = -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 u,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - (((t : ZMod p) - (k : ZMod p))⁻¹) ^ 2) := by
  unfold Tfull TD
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), if_pos hu]
  congr 1
  exact Finset.sum_congr rfl fun t _ => by rw [conv4sq hp5 hk4]

/-- **The scalar Schur complement.**  -/
theorem schur_Z (hp5 : 5 ≤ p) (hk4 : (4 : ZMod p) * (k : ZMod p) = 1)
    (hj : ((j : ℕ) : ZMod p) ≠ 0) {r d : ℕ} (hrd : r + d = p) (hkr : k ≤ r) {u w : ℕ}
    (hu : u < k) (hw : w < k) :
    Tfull p j k u w - ((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹ *
        ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
      (if u = w then hm2 p (k - 1) / 16 else 0) +
        (1 / 16) * ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ := by
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have hp3 : 3 ≤ p := by omega
  -- the sum over the high block
  have hS : ∀ u w : ℕ, u < k → w < k →
      ((((j : ℕ) : ZMod p)⁻¹) ^ 2)⁻¹ * ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
        (1 / 16) * ∑ c ∈ Ico k r, (((c : ℕ) : ZMod p) - u)⁻¹ * (((c : ℕ) : ZMod p) - w)⁻¹ := by
    intro u w hu hw
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    rw [Tfull_lh hu hc'.1 (by omega), Tfull_lh hw hc'.1 (by omega)]
    field_simp
    ring
  rcases lt_trichotomy u w with huw | huw | huw
  · rw [if_neg huw.ne, hS u w hu hw, Tfull_ll hp5 hk4 huw hw]
    have := harm_off hp3 hrd hkr huw hw
    rw [zero_add]
    linear_combination this
  · subst huw
    rw [if_pos rfl, hS u u hu hu, Tfull_dd hp5 hk4 hu]
    have := harm_diag hp5 hrd hkr hu
    simp only [← sq] at this ⊢
    linear_combination this
  · rw [if_neg huw.ne', Tfull_symm p j k u w]
    have hS' := hS w u hw hu
    rw [show ∑ c ∈ Ico k r, Tfull p j k u c * Tfull p j k w c =
        ∑ c ∈ Ico k r, Tfull p j k w c * Tfull p j k u c from
          Finset.sum_congr rfl fun c _ => mul_comm _ _, hS', Tfull_ll hp5 hk4 huw hu]
    have := harm_off hp3 hrd hkr huw hu
    rw [zero_add]
    have e : ∑ i ∈ Icc 1 d, ((u : ZMod p) + (i : ℕ))⁻¹ * ((w : ZMod p) + (i : ℕ))⁻¹ =
        ∑ i ∈ Icc 1 d, ((w : ZMod p) + (i : ℕ))⁻¹ * ((u : ZMod p) + (i : ℕ))⁻¹ :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    linear_combination this

end

end CatalanCore.Arith.Hybrid
