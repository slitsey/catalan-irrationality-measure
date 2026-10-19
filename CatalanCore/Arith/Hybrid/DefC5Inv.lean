module

public import CatalanCore.Arith.Hybrid.DefC5Red

@[expose] public section

/-!
# Theorem C5: the block `𝒫` and its explicit inverse

On `𝒫 = C ∖ U` (labels `P0 = [0, r-p)`, `B1 = [k, p)`, `B2 = [p, r)`), `Mp5` is `1` on the
diagonal of `B1`, `15/16` on that of `B2`, `0` on that of `P0`, and `e = -3/16` on the pairs
`(a, a + p)`, `a ∈ P0`.  `Minv5` (label formulas `Ival`) is its inverse: `1` on `B1`, `0` on `B2`,
`-π₂/e²` on `P0`, `1/e` on the pairs.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Vals

variable (p : ℕ) [Fact p.Prime]

noncomputable def eC : ZMod p := (16 : ZMod p)⁻¹ * (-3)
noncomputable def piC : ZMod p := (16 : ZMod p)⁻¹ * 15

/-- The residues of `Mp5` on labels. -/
noncomputable def Mval (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then 0 else if A < p then 1 else piC p)
  else if A + p = B ∧ A < r - p then eC p else if B + p = A ∧ B < r - p then eC p else 0

/-- The residues of the inverse of `Mp5`. -/
noncomputable def Ival (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then -(piC p) * ((eC p)⁻¹) ^ 2 else if A < p then 1 else 0)
  else if A + p = B ∧ A < r - p then (eC p)⁻¹ else if B + p = A ∧ B < r - p then (eC p)⁻¹ else 0

variable {p}

lemma h16 (hp5 : 5 ≤ p) : (16 : ZMod p) ≠ 0 := by
  have : (16 : ZMod p) = 4 * 4 := by norm_num
  rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)

lemma three_ne (hp5 : 5 ≤ p) : (3 : ZMod p) ≠ 0 := by
  have : ((3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd (by norm_num) hd) (by omega)
  simpa using this

lemma eC_ne (hp5 : 5 ≤ p) : eC p ≠ 0 := by
  unfold eC
  exact mul_ne_zero (inv_ne_zero (h16 hp5)) (neg_ne_zero.2 (three_ne hp5))

variable {o r m k : ℕ} (S : CSetup o p r m k)
include S

lemma Mval_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    Mval p r C D = if D = C + p then eC p else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval; split_ifs <;> first | rfl | (exfalso; omega)

lemma Mval_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    Mval p r C D = if D = C then 1 else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval; split_ifs <;> first | rfl | (exfalso; omega)

lemma Mval_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    Mval p r C D = if D = C then piC p else if D + p = C then eC p else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp
  unfold Mval; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    Ival p r C D = if D = C then -(piC p) * ((eC p)⁻¹) ^ 2 else if D = C + p then (eC p)⁻¹ else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    Ival p r C D = if D = C then 1 else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    Ival p r C D = if D + p = C then (eC p)⁻¹ else 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival; split_ifs <;> first | rfl | (exfalso; omega)

omit S in
lemma Mval_symm (A B : ℕ) : Mval p r A B = Mval p r B A := by
  unfold Mval; split_ifs <;> first | rfl | (exfalso; omega)

/-- `TcF` on `𝒫 × 𝒫` for `A < B`. -/
lemma TcF_PP_lt {A B : ℕ} (hAB : A < B) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcF p r k A B = Mval p r A B := by
  have hkp := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  rw [TcF_lt hAB, wC_P S (by omega) hAP, wC_P S hB hBP]
  have h2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
  have h1 : ¬ ((1 : ℕ) + 1 = 1) := by norm_num
  unfold TCgen
  rw [if_neg h2, if_neg h1]
  by_cases hd : B - A = p
  · have hs : sing p k A B = -3 := by
      unfold sing; split_ifs <;> first | (exfalso; omega) | ring
    rw [if_pos ⟨rfl, hd⟩, hs]
    unfold Mval
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rfl
  · rw [if_neg (fun h => hd h.2)]
    unfold Mval
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma TcF_PP {A B : ℕ} (hA : A < r) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcF p r k A B = Mval p r A B := by
  have hkp := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  have h16' := h16 S.p5
  rcases lt_trichotomy A B with h | h | h
  · exact TcF_PP_lt S h hB hAP hBP
  · subst h
    rw [TcF_diag, wC_P S hA hAP]
    have e2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
    unfold TCDgen
    rw [if_neg e2, if_pos rfl]
    unfold Mval
    rw [if_pos rfl]
    unfold singD piC
    split_ifs <;> first | (exfalso; omega) | (field_simp; ring)
  · rw [TcF_symm, Mval_symm]
    exact TcF_PP_lt S h hA hBP hAP

end Vals

section Inv

variable {o p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup o p r m k)

lemma sum_ite_BP {α : Type*} [AddCommMonoid α] (F : BP p r k → α) (d0 : BP p r k)
    (h : ∀ d, d ≠ d0 → F d = 0) : ∑ d, F d = F d0 :=
  Finset.sum_eq_single d0 (fun d _ hd => h d hd) (fun h' => absurd (Finset.mem_univ _) h')

include S in
lemma MI_sum (c b : BP p r k) :
    ∑ d : BP p r k, Mval p r (c.1 : ℕ) (d.1 : ℕ) * Ival p r (d.1 : ℕ) (b.1 : ℕ) =
      if c = b then 1 else 0 := by
  have hkp := S.kp; have hLlo := S.hLlo; have hrp := S.hrp; have hN := S.hN
  have hcP := c.2
  have hcr := c.1.2
  have hbr := b.1.2
  have heC := eC_ne S.p5
  have hcb : c = b ↔ (b.1 : ℕ) = (c.1 : ℕ) :=
    ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h.symm)⟩
  rcases (by omega : (c.1 : ℕ) < r - p ∨ ((k ≤ (c.1 : ℕ)) ∧ (c.1 : ℕ) < p) ∨ p ≤ (c.1 : ℕ)) with
    h | h | h
  · -- P0
    let d0 : BP p r k := ⟨⟨(c.1 : ℕ) + p, by omega⟩, by simp only; omega⟩
    rw [sum_ite_BP _ d0]
    · show Mval p r (c.1 : ℕ) ((c.1 : ℕ) + p) * Ival p r ((c.1 : ℕ) + p) (b.1 : ℕ) = _
      rw [Mval_P0 S h (by omega), if_pos rfl, Ival_B2 S (by omega) (by omega) hbr]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos (by omega), if_pos (hcb.2 hh)]
        exact mul_inv_cancel₀ heC
      · rw [if_neg (by omega), if_neg (fun h' => hh (hcb.1 h')), mul_zero]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) + p := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [Mval_P0 S h d.1.2, if_neg this, zero_mul]
  · -- B1
    obtain ⟨h1, h2⟩ := h
    rw [sum_ite_BP _ c]
    · rw [Mval_B1 S h1 h2 hcr, if_pos rfl, Ival_B1 S h1 h2 hbr, one_mul]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos hh, if_pos (hcb.2 hh)]
      · rw [if_neg hh, if_neg (fun h' => hh (hcb.1 h'))]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [Mval_B1 S h1 h2 d.1.2, if_neg this, zero_mul]
  · -- B2
    let d2 : BP p r k := ⟨⟨(c.1 : ℕ) - p, by omega⟩, by simp only; omega⟩
    have hne : c ≠ d2 := by
      intro h'; have := congrArg (fun t : BP p r k => (t.1 : ℕ)) h'
      simp only [d2] at this; omega
    rw [Finset.sum_eq_add c d2 hne]
    · show Mval p r (c.1 : ℕ) (c.1 : ℕ) * Ival p r (c.1 : ℕ) (b.1 : ℕ) +
        Mval p r (c.1 : ℕ) ((c.1 : ℕ) - p) * Ival p r ((c.1 : ℕ) - p) (b.1 : ℕ) = _
      rw [Mval_B2 S h hcr hcr, Mval_B2 S h hcr (by omega), Ival_B2 S h hcr hbr,
        Ival_P0 S (by omega) hbr]
      simp only [hcb]
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      split_ifs <;> first | (exfalso; omega) | (field_simp; try ring) | simp
    · intro d _ hd
      obtain ⟨hd1, hd2⟩ := hd
      have e1 : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd1 (Subtype.ext (Fin.ext h'))
      have e2 : (d.1 : ℕ) + p ≠ (c.1 : ℕ) := fun h' => hd2 (Subtype.ext (Fin.ext (by
        simp only [d2]; omega)))
      rw [Mval_B2 S h hcr d.1.2, if_neg e1, if_neg e2, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro h'; exact absurd (Finset.mem_univ _) h'

/-- The inverse of `Mp5`. -/
noncomputable def Minv5 (p r k : ℕ) [Fact p.Prime] :
    Matrix (BP p r k) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (Ival p r (c.1 : ℕ) (d.1 : ℕ))

include S in
lemma Mp5_eq (c d : BP p r k) : Mp5 p r k c d = rfC p (Mval p r (c.1 : ℕ) (d.1 : ℕ)) := by
  simp only [Mp5, Matrix.of_apply]
  rw [TcF_PP S c.1.2 d.1.2 c.2 d.2]

include S in
lemma Mp5_mul_Minv5 : Mp5 p r k * Minv5 p r k = 1 := by
  ext c b
  rw [Matrix.mul_apply]
  simp only [Minv5, Matrix.of_apply, Mp5_eq S]
  have h := MI_sum S c b
  have h2 := congrArg (rfCH p) h
  simp only [map_sum, map_mul, apply_ite (rfCH p), map_one, map_zero] at h2
  simp only [rfC_eq]
  rw [h2]
  simp [Matrix.one_apply]

include S in
@[instance_reducible] noncomputable def invMp5 : Invertible (Mp5 p r k) :=
  invertibleOfRightInverse _ _ (Mp5_mul_Minv5 S)

include S in
lemma invOf_Mp5 [Invertible (Mp5 p r k)] : ⅟(Mp5 p r k) = Minv5 p r k :=
  invOf_eq_right_inv (Mp5_mul_Minv5 S)

end Inv

end CatalanCore.Arith.Hybrid
