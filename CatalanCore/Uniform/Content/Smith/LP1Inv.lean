module

public import CatalanCore.Uniform.Content.Smith.LP1Mat

@[expose] public section

/-!
# LP1: the block `𝒫` and its explicit inverse

On `𝒫 = C ∖ U` (labels `P0 = [0, r-p)`, `B1 = [k, p)`, `B2 = [p, r)`), `Mp5G` is `d₁ = nr⁻¹ v²` on
the diagonal of `B1`, `π = nr⁻¹ (v² - 1)` on that of `B2`, `0` on that of `P0`, and `e = nr⁻¹ (v + 1)`
on the pairs `(a, a + p)`, `a ∈ P0`.  `Minv5G` is its inverse: `d₁⁻¹` on `B1`, `0` on `B2`,
`-π/e²` on `P0`, `1/e` on the pairs.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

section Vals

variable {p : ℕ} [Fact p.Prime]

noncomputable def eCG (nr v : ZMod p) : ZMod p := nr⁻¹ * (v + 1)
noncomputable def dBG (nr v : ZMod p) : ZMod p := nr⁻¹ * v ^ 2
noncomputable def piCG (nr v : ZMod p) : ZMod p := nr⁻¹ * (v ^ 2 - 1)

/-- The residues of `Mp5G` on labels. -/
noncomputable def MvalG (nr v : ZMod p) (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then 0 else if A < p then dBG nr v else piCG nr v)
  else if A + p = B ∧ A < r - p then eCG nr v else if B + p = A ∧ B < r - p then eCG nr v else 0

/-- The residues of the inverse of `Mp5G`. -/
noncomputable def IvalG (nr v : ZMod p) (r A B : ℕ) : ZMod p :=
  if A = B then (if A < r - p then -(piCG nr v) * ((eCG nr v)⁻¹) ^ 2
    else if A < p then (dBG nr v)⁻¹ else 0)
  else if A + p = B ∧ A < r - p then (eCG nr v)⁻¹
  else if B + p = A ∧ B < r - p then (eCG nr v)⁻¹ else 0

variable {Fr : Frame} {q o N r m k j : ℕ}

lemma TTSing2.vk_add_one_ne (T : TwoTermData Fr q o) (S : TTSing2 p q o N k j) :
    vk p q j + 1 ≠ 0 := by
  have hj := S.j_ne T
  have hjq : j < q := (S.toSing).hjq T
  have hqp := S.hqp
  have e : vk p q j + 1 = ((j : ZMod p) - (q : ZMod p)) * ((j : ZMod p))⁻¹ := by
    unfold vk; field_simp; ring
  rw [e]
  refine mul_ne_zero ?_ (inv_ne_zero hj)
  have := zmod_sub_ne_zero_of_lt hjq (by omega : q - j < p)
  intro h; apply this; linear_combination -h

lemma eCG_ne (H : LP1Hyp Fr p q o r m k j) : eCG (red p Fr.norm) (vk p q j) ≠ 0 := by
  unfold eCG
  exact mul_ne_zero (inv_ne_zero H.cfg.hnm0) (H.cfg.sg.vk_add_one_ne H.cfg.tt)

lemma dBG_ne (H : LP1Hyp Fr p q o r m k j) : dBG (red p Fr.norm) (vk p q j) ≠ 0 := by
  unfold dBG
  exact mul_ne_zero (inv_ne_zero H.cfg.hnm0) (pow_ne_zero 2 (H.cfg.sg.vk_ne H.cfg.tt))

section Val2

variable (H : LP1Hyp Fr p q o r m k j)
include H

lemma MvalG_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    MvalG (red p Fr.norm) (vk p q j) r C D =
      if D = C + p then eCG (red p Fr.norm) (vk p q j) else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk
  unfold MvalG; split_ifs <;> first | rfl | (exfalso; omega)

lemma MvalG_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    MvalG (red p Fr.norm) (vk p q j) r C D =
      if D = C then dBG (red p Fr.norm) (vk p q j) else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk
  unfold MvalG; split_ifs <;> first | rfl | (exfalso; omega)

lemma MvalG_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    MvalG (red p Fr.norm) (vk p q j) r C D =
      if D = C then piCG (red p Fr.norm) (vk p q j)
      else if D + p = C then eCG (red p Fr.norm) (vk p q j) else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk
  unfold MvalG; split_ifs <;> first | rfl | (exfalso; omega)

lemma IvalG_P0 {C D : ℕ} (hC : C < r - p) (hD : D < r) :
    IvalG (red p Fr.norm) (vk p q j) r C D =
      if D = C then -(piCG (red p Fr.norm) (vk p q j)) *
          ((eCG (red p Fr.norm) (vk p q j))⁻¹) ^ 2
      else if D = C + p then (eCG (red p Fr.norm) (vk p q j))⁻¹ else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk; have := H.cfg.sg.hN2
  unfold IvalG; split_ifs <;> first | rfl | (exfalso; omega)

lemma IvalG_B1 {C D : ℕ} (hC : k ≤ C) (hC2 : C < p) (hD : D < r) :
    IvalG (red p Fr.norm) (vk p q j) r C D =
      if D = C then (dBG (red p Fr.norm) (vk p q j))⁻¹ else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk; have := H.cfg.sg.hN2
  unfold IvalG; split_ifs <;> first | rfl | (exfalso; omega)

lemma IvalG_B2 {C D : ℕ} (hC : p ≤ C) (hCr : C < r) (hD : D < r) :
    IvalG (red p Fr.norm) (vk p q j) r C D =
      if D + p = C then (eCG (red p Fr.norm) (vk p q j))⁻¹ else 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk; have := H.cfg.sg.hN2
  unfold IvalG; split_ifs <;> first | rfl | (exfalso; omega)

end Val2

lemma MvalG_symm (nr v : ZMod p) (r A B : ℕ) : MvalG nr v r A B = MvalG nr v r B A := by
  unfold MvalG; split_ifs <;> first | rfl | (exfalso; omega)

/-- `TcG` on `𝒫 × 𝒫` for `A < B`. -/
lemma LP1Hyp.TcG_PP_lt (H : LP1Hyp Fr p q o r m k j) {A B : ℕ} (hAB : A < B) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) A B =
      MvalG (red p Fr.norm) (vk p q j) r A B := by
  have hkp := H.cfg.sg.hkp; have := H.hrp; have := H.hUk
  rw [TcG_lt hAB, wC_P' (by omega) hAP, wC_P' hB hBP]
  have h2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
  have h1 : ¬ ((1 : ℕ) + 1 = 1) := by norm_num
  unfold TCgenG
  rw [if_neg h2, if_neg h1]
  by_cases hd : B - A = p
  · have hs : singG p k (vk p q j) (vk2 p q j) A B = vk p q j + 1 := by
      unfold singG; split_ifs <;> first | (exfalso; omega) | ring
    rw [if_pos ⟨rfl, hd⟩, hs]
    unfold MvalG
    rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
    rfl
  · rw [if_neg (fun h => hd h.2)]
    unfold MvalG
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma LP1Hyp.TcG_PP (H : LP1Hyp Fr p q o r m k j) {A B : ℕ} (hA : A < r) (hB : B < r)
    (hAP : ¬ (r - p ≤ A ∧ A < k)) (hBP : ¬ (r - p ≤ B ∧ B < k)) :
    TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) A B =
      MvalG (red p Fr.norm) (vk p q j) r A B := by
  have hkp := H.cfg.sg.hkp; have := H.hrp; have := H.hUk
  rcases lt_trichotomy A B with h | h | h
  · exact H.TcG_PP_lt h hB hAP hBP
  · subst h
    rw [TcG_diag, wC_P' hA hAP]
    have e2 : ¬ ((1 : ℕ) + 1 = 0) := by norm_num
    unfold TCDgenG
    rw [if_neg e2, if_pos rfl]
    unfold MvalG
    rw [if_pos rfl]
    unfold singDG piCG dBG
    split_ifs <;> first | (exfalso; omega) | ring
  · rw [TcG_symm, MvalG_symm]
    exact H.TcG_PP_lt h hA hBP hAP

end Vals

section Inv

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ} (H : LP1Hyp Fr p q o r m k j)

lemma sum_ite_BP' {α : Type*} [AddCommMonoid α] (F : BP p r k → α) (d0 : BP p r k)
    (h : ∀ d, d ≠ d0 → F d = 0) : ∑ d, F d = F d0 :=
  Finset.sum_eq_single d0 (fun d _ hd => h d hd) (fun h' => absurd (Finset.mem_univ _) h')

include H in
lemma MI_sumG (c b : BP p r k) :
    ∑ d : BP p r k, MvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) (d.1 : ℕ) *
        IvalG (red p Fr.norm) (vk p q j) r (d.1 : ℕ) (b.1 : ℕ) =
      if c = b then 1 else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk; have hN2 := H.cfg.sg.hN2
  have hcP := c.2
  have hcr := c.1.2
  have hbr := b.1.2
  have heC := eCG_ne H
  have hdB := dBG_ne H
  have hcb : c = b ↔ (b.1 : ℕ) = (c.1 : ℕ) :=
    ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h.symm)⟩
  rcases (by omega : (c.1 : ℕ) < r - p ∨ ((k ≤ (c.1 : ℕ)) ∧ (c.1 : ℕ) < p) ∨ p ≤ (c.1 : ℕ)) with
    h | h | h
  · -- P0
    let d0 : BP p r k := ⟨⟨(c.1 : ℕ) + p, by omega⟩, by simp only; omega⟩
    rw [sum_ite_BP' _ d0]
    · show MvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) ((c.1 : ℕ) + p) *
        IvalG (red p Fr.norm) (vk p q j) r ((c.1 : ℕ) + p) (b.1 : ℕ) = _
      rw [MvalG_P0 H h (by omega), if_pos rfl, IvalG_B2 H (by omega) (by omega) hbr]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos (by omega), if_pos (hcb.2 hh)]
        exact mul_inv_cancel₀ heC
      · rw [if_neg (by omega), if_neg (fun h' => hh (hcb.1 h')), mul_zero]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) + p := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [MvalG_P0 H h d.1.2, if_neg this, zero_mul]
  · -- B1
    obtain ⟨h1, h2⟩ := h
    rw [sum_ite_BP' _ c]
    · rw [MvalG_B1 H h1 h2 hcr, if_pos rfl, IvalG_B1 H h1 h2 hbr]
      by_cases hh : (b.1 : ℕ) = c.1
      · rw [if_pos hh, if_pos (hcb.2 hh)]
        exact mul_inv_cancel₀ hdB
      · rw [if_neg hh, if_neg (fun h' => hh (hcb.1 h')), mul_zero]
    · intro d hd
      have : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd (Subtype.ext (Fin.ext h'))
      rw [MvalG_B1 H h1 h2 d.1.2, if_neg this, zero_mul]
  · -- B2
    let d2 : BP p r k := ⟨⟨(c.1 : ℕ) - p, by omega⟩, by simp only; omega⟩
    have hne : c ≠ d2 := by
      intro h'; have := congrArg (fun t : BP p r k => (t.1 : ℕ)) h'
      simp only [d2] at this; omega
    rw [Finset.sum_eq_add c d2 hne]
    · show MvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) (c.1 : ℕ) *
          IvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) (b.1 : ℕ) +
        MvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) ((c.1 : ℕ) - p) *
          IvalG (red p Fr.norm) (vk p q j) r ((c.1 : ℕ) - p) (b.1 : ℕ) = _
      rw [MvalG_B2 H h hcr hcr, MvalG_B2 H h hcr (by omega), IvalG_B2 H h hcr hbr,
        IvalG_P0 H (by omega) hbr]
      simp only [hcb]
      have hp0 : 0 < p := (Fact.out : p.Prime).pos
      split_ifs <;> first | (exfalso; omega) | (field_simp; try ring) | simp
    · intro d _ hd
      obtain ⟨hd1, hd2⟩ := hd
      have e1 : (d.1 : ℕ) ≠ (c.1 : ℕ) := fun h' => hd1 (Subtype.ext (Fin.ext h'))
      have e2 : (d.1 : ℕ) + p ≠ (c.1 : ℕ) := fun h' => hd2 (Subtype.ext (Fin.ext (by
        simp only [d2]; omega)))
      rw [MvalG_B2 H h hcr d.1.2, if_neg e1, if_neg e2, zero_mul]
    · intro h'; exact absurd (Finset.mem_univ _) h'
    · intro h'; exact absurd (Finset.mem_univ _) h'

/-- The inverse of `Mp5G`. -/
noncomputable def Minv5G (nr v : ZMod p) (r k : ℕ) :
    Matrix (BP p r k) (BP p r k) (RatFunc (ZMod p)) :=
  Matrix.of fun c d => rfC p (IvalG nr v r (c.1 : ℕ) (d.1 : ℕ))

include H in
lemma Mp5G_eq (c d : BP p r k) :
    Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c d =
      rfC p (MvalG (red p Fr.norm) (vk p q j) r (c.1 : ℕ) (d.1 : ℕ)) := by
  simp only [Mp5G, Matrix.of_apply]
  rw [H.TcG_PP c.1.2 d.1.2 c.2 d.2]

include H in
lemma Mp5G_mul_Minv5G :
    Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j) *
      Minv5G (red p Fr.norm) (vk p q j) r k = 1 := by
  ext c b
  rw [Matrix.mul_apply]
  simp only [Minv5G, Matrix.of_apply, Mp5G_eq H]
  have h := MI_sumG H c b
  have h2 := congrArg (rfCH p) h
  simp only [map_sum, map_mul, apply_ite (rfCH p), map_one, map_zero] at h2
  simp only [rfC_eq]
  rw [h2]
  simp [Matrix.one_apply]

include H in
@[instance_reducible] noncomputable def invMp5G :
    Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) :=
  invertibleOfRightInverse _ _ (Mp5G_mul_Minv5G H)

include H in
lemma invOf_Mp5G [Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))] :
    ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) =
      Minv5G (red p Fr.norm) (vk p q j) r k :=
  invOf_eq_right_inv (Mp5G_mul_Minv5G H)

end Inv

end CatalanCore.Uniform.Content.Smith
