module

public import CatalanCore.Arith.Hybrid.DefC7Red

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4): the block `𝒫` and its explicit inverse

On `𝒫 = C ∖ U` (labels `P0 = [0, r-p)`, `B1 = [k, p)`, `B2 = [p, r)`), `Mp57` is `1` on the
diagonal of `B1`, `15/16` on that of `B2`, `0` on that of `P0`, and `e = -3/16` on the pairs
`(a, a + p)`, `a ∈ P0`.  `Minv57` (label formulas `Ival7`) is its inverse: `1` on `B1`, `0` on `B2`,
`-π₂/e²` on `P0`, `1/e` on the pairs.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Vals7

variable (p : ℕ) [Fact p.Prime]

noncomputable def eC7 : ZMod p := (16 : ZMod p)⁻¹ * (-(3 : ZMod p)⁻¹)
noncomputable def piC7 : ZMod p := -(1 / 16 : ZMod p) * (-(16 * ((3 : ZMod p)⁻¹) ^ 2) + 1)
/-- The `B1` diagonal entry `j⁻²`, `j = 3`. -/
noncomputable def b1C7 : ZMod p := ((3 : ZMod p)⁻¹) ^ 2

/-- The residues of `Mp57` on labels. -/
noncomputable def Mval7 (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then 0 else if A < p then b1C7 p else piC7 p)
  else if A + p = B ∧ A < r - p then eC7 p else if B + p = A ∧ B < r - p then eC7 p else 0

/-- The residues of the inverse of `Mp57`. -/
noncomputable def Ival7 (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then -(piC7 p) * ((eC7 p)⁻¹) ^ 2 else if A < p then (b1C7 p)⁻¹ else 0)
  else if A + p = B ∧ A < r - p then (eC7 p)⁻¹ else if B + p = A ∧ B < r - p then (eC7 p)⁻¹ else 0

variable {p}

lemma eC7_ne (hp5 : 5 ≤ p) : eC7 p ≠ 0 := by
  unfold eC7
  exact mul_ne_zero (inv_ne_zero (h16 hp5)) (neg_ne_zero.2 (inv_ne_zero (three_ne hp5)))

lemma b1C7_ne (hp5 : 5 ≤ p) : b1C7 p ≠ 0 := pow_ne_zero 2 (inv_ne_zero (three_ne hp5))

variable {r m k : ℕ} (S : CSetup7 p r m k)
include S

lemma Mval7_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    Mval7 p r C D = if D = C + p then eC7 p else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval7; split_ifs <;> first | rfl | (exfalso; omega)

lemma Mval7_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    Mval7 p r C D = if D = C then b1C7 p else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval7; split_ifs <;> first | rfl | (exfalso; omega)

lemma Mval7_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    Mval7 p r C D = if D = C then piC7 p else if D + p = C then eC7 p else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval7; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival7_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    Ival7 p r C D = if D = C then -(piC7 p) * ((eC7 p)⁻¹) ^ 2 else if D = C + p then (eC7 p)⁻¹ else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival7; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival7_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    Ival7 p r C D = if D = C then (b1C7 p)⁻¹ else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival7; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival7_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    Ival7 p r C D = if D + p = C then (eC7 p)⁻¹ else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival7; split_ifs <;> first | rfl | (exfalso; omega)

omit S in
lemma Mval7_symm (A B : ℕ) : Mval7 p r A B = Mval7 p r B A := by
  unfold Mval7; split_ifs <;> first | rfl | (exfalso; omega)

/-- `TcF7` on `𝒫 × 𝒫` for `A < B`. -/
lemma TcF7_PP_lt {A B : ℕ} (hAB : A < B) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcF7 p r k A B = Mval7 p r A B := by
  have hkp := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  rw [TcF7_lt hAB, wC7_P S (by omega) hAP, wC7_P S hB hBP]
  have h2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
  have h1 : ¬ ((1 : ℕ) + 1 = 1) := by norm_num
  unfold TCgen7
  rw [if_neg h2, if_neg h1]
  by_cases hd : B - A = p
  · have hs : sing7 p k A B = -(3 : ZMod p)⁻¹ := by
      have h3 := three_ne S.p5
      unfold sing7; split_ifs <;> first | (exfalso; omega) | (field_simp; try ring)
    rw [if_pos ⟨rfl, hd⟩, hs]
    unfold Mval7
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rfl
  · rw [if_neg (fun h => hd h.2)]
    unfold Mval7
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma TcF7_PP {A B : ℕ} (hA : A < r) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcF7 p r k A B = Mval7 p r A B := by
  have hkp := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  have h16' := h16 S.p5
  rcases lt_trichotomy A B with h | h | h
  · exact TcF7_PP_lt S h hB hAP hBP
  · subst h
    rw [TcF7_diag, wC7_P S hA hAP]
    have e2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
    unfold TCDgen7
    rw [if_neg e2, if_pos rfl]
    unfold Mval7
    rw [if_pos rfl]
    have h3 := three_ne S.p5
    unfold singD7 piC7 b1C7
    split_ifs <;> first | (exfalso; omega) | (field_simp; try ring)
  · rw [TcF7_symm, Mval7_symm]
    exact TcF7_PP_lt S h hA hBP hAP

end Vals7

section Inv7

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup7 p r m k)

lemma sum_ite_BP7 {α : Type*} [AddCommMonoid α] (F : BP7 p r k → α) (d0 : BP7 p r k)
    (h : ∀ d, d ≠ d0 → F d = 0) : ∑ d, F d = F d0 :=
  Finset.sum_eq_single d0 (fun d _ hd => h d hd) (fun h' => absurd (Finset.mem_univ _) h')

include S in
lemma MI_sum7 (c b : BP7 p r k) :
    ∑ d : BP7 p r k, Mval7 p r (c.1 : ℕ) (d.1 : ℕ) * Ival7 p r (d.1 : ℕ) (b.1 : ℕ) =
      if c = b then 1 else 0 := by
  have hkp := S.kp; have hLlo := S.hLlo; have hrp := S.hrp; have hN := S.hN
  have hcP := c.2
  have hcr := c.1.2
  have hbr := b.1.2
  have heC := eC7_ne S.p5
  have hcb : c = b ↔ (b.1 : ℕ) = (c.1 : ℕ) :=
    ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h.symm)⟩
  rcases (by omega : (c.1 : ℕ) < r - p ∨ ((k ≤ (c.1 : ℕ)) ∧ (c.1 : ℕ) < p) ∨ p ≤ (c.1 : ℕ)) with
    h | h | h
  · -- P0
    let d0 : BP7 p r k := ⟨⟨(c.1 : ℕ) + p, by omega⟩, by simp only; omega⟩
    rw [sum_ite_BP7 _ d0]
    · show Mval7 p r (c.1 : ℕ) ((c.1 : ℕ) + p) * Ival7 p r ((c.1 : ℕ) + p) (b.1 : ℕ) = _
      rw [Mval7_P0 S h (by omega), if_pos rfl, Ival7_B2 S (by omega) (by omega) hbr]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos (by omega), if_pos (hcb.2 hh)]
        exact mul_inv_cancel₀ heC
      · rw [if_neg (by omega), if_neg (fun h' => hh (hcb.1 h')), mul_zero]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) + p := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [Mval7_P0 S h d.1.2, if_neg this, zero_mul]
  · -- B1
    obtain ⟨h1, h2⟩ := h
    rw [sum_ite_BP7 _ c]
    · rw [Mval7_B1 S h1 h2 hcr, if_pos rfl, Ival7_B1 S h1 h2 hbr]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos hh, if_pos (hcb.2 hh)]
        exact mul_inv_cancel₀ (b1C7_ne S.p5)
      · rw [if_neg hh, if_neg (fun h' => hh (hcb.1 h')), mul_zero]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [Mval7_B1 S h1 h2 d.1.2, if_neg this, zero_mul]
  · -- B2
    let d2 : BP7 p r k := ⟨⟨(c.1 : ℕ) - p, by omega⟩, by simp only; omega⟩
    have hne : c ≠ d2 := by
      intro h'; have := congrArg (fun t : BP7 p r k => (t.1 : ℕ)) h'
      simp only [d2] at this; omega
    rw [Finset.sum_eq_add c d2 hne]
    · show Mval7 p r (c.1 : ℕ) (c.1 : ℕ) * Ival7 p r (c.1 : ℕ) (b.1 : ℕ) +
        Mval7 p r (c.1 : ℕ) ((c.1 : ℕ) - p) * Ival7 p r ((c.1 : ℕ) - p) (b.1 : ℕ) = _
      rw [Mval7_B2 S h hcr hcr, Mval7_B2 S h hcr (by omega), Ival7_B2 S h hcr hbr,
        Ival7_P0 S (by omega) hbr]
      simp only [hcb]
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      split_ifs <;> first | (exfalso; omega) | (field_simp; try ring) | simp
    · intro d _ hd
      obtain ⟨hd1, hd2⟩ := hd
      have e1 : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd1 (Subtype.ext (Fin.ext h'))
      have e2 : (d.1 : ℕ) + p ≠ (c.1 : ℕ) := fun h' => hd2 (Subtype.ext (Fin.ext (by
        simp only [d2]; omega)))
      rw [Mval7_B2 S h hcr d.1.2, if_neg e1, if_neg e2, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro h'; exact absurd (Finset.mem_univ _) h'

/-- The inverse of `Mp57`. -/
noncomputable def Minv57 (p r k : ℕ) [Fact p.Prime] :
    Matrix (BP7 p r k) (BP7 p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (Ival7 p r (c.1 : ℕ) (d.1 : ℕ))

include S in
lemma Mp5_eq7 (c d : BP7 p r k) : Mp57 p r k c d = rfC p (Mval7 p r (c.1 : ℕ) (d.1 : ℕ)) := by
  simp only [Mp57, Matrix.of_apply]
  rw [TcF7_PP S c.1.2 d.1.2 c.2 d.2]

include S in
lemma Mp5_mul_Minv57 : Mp57 p r k * Minv57 p r k = 1 := by
  ext c b
  rw [Matrix.mul_apply]
  simp only [Minv57, Matrix.of_apply, Mp5_eq7 S]
  have h := MI_sum7 S c b
  have h2 := congrArg (rfCH p) h
  simp only [map_sum, map_mul, apply_ite (rfCH p), map_one, map_zero] at h2
  simp only [rfC_eq]
  rw [h2]
  simp [Matrix.one_apply]

include S in
@[instance_reducible] noncomputable def invMp57 : Invertible (Mp57 p r k) :=
  invertibleOfRightInverse _ _ (Mp5_mul_Minv57 S)

include S in
lemma invOf_Mp57 [Invertible (Mp57 p r k)] : ⅟(Mp57 p r k) = Minv57 p r k :=
  invOf_eq_right_inv (Mp5_mul_Minv57 S)

end Inv7

end CatalanCore.Arith.Hybrid
