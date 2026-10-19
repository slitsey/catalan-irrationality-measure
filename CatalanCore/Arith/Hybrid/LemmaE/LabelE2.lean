module

public import CatalanCore.Arith.Hybrid.LemmaE.LabelE

@[expose] public section

/-!
# Lemma E, class 1: the pair block `Mp` and the partner map

`tauN a` is `a + p` on `P₀ = [0, r-p)`, `a - p` on `B₂ = [p, r)` and `a` on `B₁ = [k, p)`.
`TE_P` evaluates the table on `P × P`: diagonal `0 / j⁻² / j⁻² - 1/16`, partners `e`, else `0`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m j k : ℕ}

/-- The partner map. -/
def tauN (p r a : ℕ) : ℕ := if a < r - p then a + p else if p ≤ a then a - p else a

lemma TE_P (S : ESetup o p r m j k) {a b : ℕ} (ha : a < r) (haP : ¬ (r - p ≤ a ∧ a < k))
    (hb : b < r) (hbP : ¬ (r - p ≤ b ∧ b < k)) :
    TE p j r k a b =
      if b = a then (if a < r - p then 0 else if tauN p r a = a then ((j : ZMod p)⁻¹) ^ 2
        else ((j : ZMod p)⁻¹) ^ 2 - (16 : ZMod p)⁻¹)
      else if b = tauN p r a then (16 : ZMod p)⁻¹ * (-(4 * ((j : ℕ) : ZMod p)⁻¹) + 1) else 0 := by
  have hkp := S.hkp
  have hpr := S.hpr
  have hrk := S.hrk
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hw : wE p r k a + wE p r k b = 2 := by
    rw [wE_P haP ha, wE_P hbP hb]
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p S.p5) (four_ne_zmod p S.p5)
  by_cases hab : b = a
  · subst hab
    have hT : TE p j r k b b = TEd p j k 2 b := by
      unfold TE; simp [wE_P hbP hb]
    rw [hT, if_pos rfl]
    unfold TEd
    simp only [show (2 : ℕ) ≠ 0 by norm_num, if_false, if_true]
    by_cases h1 : b < r - p
    · rw [if_pos h1]
      have : singE2 p j k b = 0 := by
        have h2 : ¬ k ≤ b := by omega
        have h3 : ¬ p ≤ b := by omega
        simp [singE2, h2, h3]
      rw [this]; simp
    · rw [if_neg h1]
      by_cases h2 : p ≤ b
      · have ht : tauN p r b = b - p := by
          unfold tauN; rw [if_neg h1, if_pos h2]
        rw [if_neg (by omega)]
        have : singE2 p j k b = -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) + 1 := by
          simp [singE2, show k ≤ b by omega, h2]
        rw [this]
        field_simp
        ring
      · have ht : tauN p r b = b := by
          unfold tauN; rw [if_neg h1, if_neg h2]
        rw [if_pos ht]
        have : singE2 p j k b = -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) := by
          have h3 : k ≤ b := by omega
          simp [singE2, h3, h2]
        rw [this]
        field_simp
  · rw [if_neg hab]
    rcases lt_or_gt_of_ne hab with h | h
    · -- b < a
      have h' : ¬ a < b := by omega
      have hT : TE p j r k a b = TEo p j k 2 b a := by
        simp only [TE, h', h, if_true, if_false, hw]
      rw [hT, TEo_two]
      by_cases hd : a - b = p
      · have ht : tauN p r a = a - p := by
          unfold tauN; rw [if_neg (by omega), if_pos (by omega)]
        rw [if_pos hd, if_pos (by omega),
          singE_full (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg hd, if_neg]
        intro hh
        unfold tauN at hh
        split_ifs at hh <;> omega
    · -- a < b
      have hT : TE p j r k a b = TEo p j k 2 a b := by
        simp only [TE, h, if_true, hw]
      rw [hT, TEo_two]
      by_cases hd : b - a = p
      · have ht : tauN p r a = a + p := by
          unfold tauN; rw [if_pos (by omega)]
        rw [if_pos hd, if_pos (by omega),
          singE_full (by omega) (by omega) (by omega) (by omega)]
      · rw [if_neg hd, if_neg]
        intro hh
        unfold tauN at hh
        split_ifs at hh <;> omega

/-! ### The index types -/

/-- The unpaired low block `U = [r-p, k)` and its complement `P`. -/
abbrev UE (p r k : ℕ) := {c : Fin r // r - p ≤ (c : ℕ) ∧ (c : ℕ) < k}
abbrev PE (p r k : ℕ) := {c : Fin r // ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)}

lemma tauN_lt (S : ESetup o p r m j k) {a : ℕ} (ha : a < r) (haP : ¬ (r - p ≤ a ∧ a < k)) :
    tauN p r a < r ∧ ¬ (r - p ≤ tauN p r a ∧ tauN p r a < k) := by
  have := S.hkp; have := S.hpr; have := S.hrk
  unfold tauN
  split_ifs <;> omega

/-- The partner map on `P`. -/
def tauP (S : ESetup o p r m j k) (c : PE p r k) : PE p r k :=
  ⟨⟨tauN p r c.1.val, (tauN_lt S c.1.2 c.2).1⟩, (tauN_lt S c.1.2 c.2).2⟩

lemma tauP_val (S : ESetup o p r m j k) (c : PE p r k) :
    ((tauP S c).1 : ℕ) = tauN p r c.1.val := rfl

lemma tauP_invol (S : ESetup o p r m j k) (c : PE p r k) : tauP S (tauP S c) = c := by
  have := S.hkp; have := S.hpr; have := S.hrk; have := c.2; have := c.1.2
  apply Subtype.ext; apply Fin.ext
  show tauN p r (tauN p r c.1.val) = c.1.val
  unfold tauN
  split_ifs <;> omega

lemma tauP_lo (S : ESetup o p r m j k) (c : PE p r k) (h : (c.1 : ℕ) < r - p) :
    tauP S c ≠ c ∧ ¬ ((tauP S c).1 : ℕ) < r - p := by
  have := S.hkp; have := S.hpr; have := S.hrk
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · intro hh
    have := congrArg (fun t : PE p r k => (t.1 : ℕ)) hh
    simp only [tauP_val] at this
    unfold tauN at this
    split_ifs at this <;> omega
  · rw [tauP_val]; unfold tauN; split_ifs <;> omega

lemma tauP_hi (S : ESetup o p r m j k) (c : PE p r k) (h1 : ¬ (c.1 : ℕ) < r - p)
    (h2 : tauP S c ≠ c) : ((tauP S c).1 : ℕ) < r - p := by
  have := S.hkp; have := S.hpr; have := S.hrk; have := c.2; have := c.1.2
  by_contra hh
  apply h2
  apply Subtype.ext; apply Fin.ext
  rw [tauP_val] at hh ⊢; unfold tauN at hh ⊢
  split_ifs at hh ⊢ <;> omega

lemma tauP_fix (S : ESetup o p r m j k) (c : PE p r k) :
    tauP S c = c ↔ k ≤ (c.1 : ℕ) ∧ (c.1 : ℕ) < p := by
  have := S.hkp; have := S.hpr; have := S.hrk; have := c.2; have := c.1.2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · intro hh
    have := congrArg (fun t : PE p r k => (t.1 : ℕ)) hh
    simp only [tauP_val] at this
    unfold tauN at this
    split_ifs at this <;> omega
  · intro hh
    apply Subtype.ext; apply Fin.ext
    rw [tauP_val]; unfold tauN
    split_ifs <;> omega

/-- Sum over the fixed points of the partner map. -/
lemma sum_fixed (S : ESetup o p r m j k) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ c : PE p r k, (if tauP S c = c then F (c.1 : ℕ) else 0) = ∑ i ∈ Ico k p, F i := by
  have := S.hkp; have := S.hpr; have := S.hrk
  have h1 : ∀ c : PE p r k, (if tauP S c = c then F (c.1 : ℕ) else 0) =
      (fun i : ℕ => if k ≤ i ∧ i < p then F i else 0) (c.1 : ℕ) := by
    intro c
    simp only [tauP_fix S c]
  simp_rw [h1]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Fin r => ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k)))
    (by intro x; simp) (fun c : Fin r => (fun i : ℕ => if k ≤ i ∧ i < p then F i else 0) (c : ℕ))]
  rw [Finset.sum_filter]
  have h2 : ∀ c : Fin r, (if ¬ (r - p ≤ (c : ℕ) ∧ (c : ℕ) < k) then
      (fun i : ℕ => if k ≤ i ∧ i < p then F i else 0) (c : ℕ) else 0) =
      (fun i : ℕ => if k ≤ i ∧ i < p then F i else 0) (c : ℕ) := by
    intro c
    by_cases hc : k ≤ (c : ℕ) ∧ (c : ℕ) < p
    · rw [if_pos (by omega)]
    · simp only [hc, if_false, ite_self]
  simp_rw [h2]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if k ≤ i ∧ i < p then F i else 0) r]
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

end

end CatalanCore.Arith.Hybrid
