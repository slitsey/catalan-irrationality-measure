module

public import CatalanCore.Uniform.Content.Smith.LP1Schur
public import CatalanCore.Uniform.Content.Smith.Member

@[expose] public section

/-!
# Theorem LP1 for a general two-term frame `ψ(z+1) - ψ(z+a/q)`

**Theorem `LP1Hyp.gle`.**  Let `Fr` be a two-term frame (`TwoTermData Fr q o`, norm a unit mod `p`),
`p ≥ 5` prime, `p < r < p + k`, `r + 2m ≤ 2p`, where `k` is the first index with `p ∣ q k - o`
(`q k = j p + o`), and `p² ∤ q t - o` for `1 ≤ t < r + 2m` (corrected PoleData condition).  Let `L`
be the number of low zone nodes (rows and columns together) `z < p + k`, so that
`L = min (2m, p + k - r)`.  With `τ' = Σ u + Σ v` the value of the D2 weights `wC`,

  `GLE p (τ' - (L - m)) (Fr.fullPoly r m)`    (saving `max (0, L - m)`).

Proof: eliminate the invertible block `𝒫 = C ∖ U` (explicit inverse `Minv5G`); the Schur complement
is `[[s₀ I, G_Y], [G_X, 0]]` (PT: the `B1`-sum cancels the Loewner block), and the low zone rows and
columns are `e · e_{z-p}`; Frobenius–König (`rank_BbarC5_le`) gives the rank bound.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

section Sc

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ} (H : LP1Hyp Fr p q o r m k j)

include H in
lemma LP1Hyp.ScUU [Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))]
    (u w : BU p r k) :
    (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
        Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
          ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
        Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)) (Sum.inl u) (Sum.inl w) =
      if u = w then s0g k (red p Fr.norm) else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  have hnr := H.cfg.hnm0
  have hv := H.cfg.sg.vk_ne H.cfg.tt
  rw [invOf_Mp5G H, Matrix.sub_apply, UpMWG H]
  have hZ := schur_scalar H.p5 (r := p) (d := 0) (by omega) hkp.le hnr hv
    (u := (u.1 : ℕ)) (w := (w.1 : ℕ)) u.2.2 w.2.2
  rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero, add_zero] at hZ
  have e1 : ∀ c ∈ Ico k p,
      rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) (rowlab p r k m (Sum.inl u)) c) *
        rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
        rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c
          (collab p r k m (Sum.inl w))) =
      rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
        (rfC p (Tsym p k (red p Fr.norm) (vk p q j) (u.1 : ℕ) c) *
          rfC p (Tsym p k (red p Fr.norm) (vk p q j) (w.1 : ℕ) c)) := by
    intro c hc
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab, collab, Sum.elim_inl]
    rw [TcG_UB1 H u.2.1 u.2.2 hc'.1 hc'.2, TcG_symm, TcG_UB1 H w.2.1 w.2.2 hc'.1 hc'.2]
    ring
  rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
  simp only [T5G, Matrix.of_apply, rowlab, collab, Sum.elim_inl]
  rw [TcG_UU H u.2.1 u.2.2 w.2.1 w.2.2]
  have hZ' := congrArg (rfCH p) hZ
  have hdB : dBG (red p Fr.norm) (vk p q j) = (red p Fr.norm)⁻¹ * (vk p q j) ^ 2 := rfl
  simp only [hdB, rfC_eq, map_sub, map_mul, map_add, map_sum, map_inv₀, map_pow,
    apply_ite (rfCH p), map_zero] at hZ' ⊢
  have hu : u = w ↔ (u.1 : ℕ) = (w.1 : ℕ) :=
    ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h)⟩
  by_cases huw : u = w
  · simp only [huw, if_true, hu.1 huw] at hZ' ⊢
    simp only [s0g, rfC_eq, map_add, map_mul, map_inv₀]
    linear_combination hZ'
  · simp only [if_neg huw, if_neg (fun h => huw (hu.2 h))] at hZ' ⊢
    linear_combination hZ'

include H in
lemma LP1Hyp.ScXY [Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))]
    (x y : Fin m) :
    (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
        Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
          ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
        Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)) (Sum.inr x) (Sum.inr y) = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  have hx := x.2; have hy := y.2
  rw [invOf_Mp5G H, Matrix.sub_apply, UpMWG H]
  have hT : T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) (Sum.inr x) (Sum.inr y) = 0 := by
    simp only [T5G, Matrix.of_apply, rowlab, collab, Sum.elim_inr]
    rw [TcG_zone_zone H (by omega) (by omega) (by omega) (by omega) (by omega), rfC_zero, zero_add]
  rw [hT, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun c hc => ?_
  have hc' := Finset.mem_Ico.1 hc
  simp only [rowlab, collab, Sum.elim_inr]
  by_cases h1 : r + 2 * (x : ℕ) - c = p
  · have h2 : r + 2 * (y : ℕ) + 1 - c ≠ p := by omega
    rw [TcG_zone_B1 H hc'.1 hc'.2 (by omega) (by omega) h2, rfC_zero, mul_zero]
  · rw [TcG_symm, TcG_zone_B1 H hc'.1 hc'.2 (by omega) (by omega) h1, rfC_zero, zero_mul,
      zero_mul]

include H in
lemma LP1Hyp.ScGx [Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))]
    (w : BU p r k) (x : Fin m) (hx : r + 2 * (x : ℕ) < p + k) :
    (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
        Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
          ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
        Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)) (Sum.inr x) (Sum.inl w) =
      if (w.1 : ℕ) + p = r + 2 * (x : ℕ) then rfC p (eCG (red p Fr.norm) (vk p q j)) else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  have hx' := x.2
  have hw := w.2
  rw [invOf_Mp5G H, Matrix.sub_apply, UpMWG H]
  have hsum : ∑ c ∈ Ico k p,
      rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j)
        (rowlab p r k m (Sum.inr x)) c) *
        rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
        rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c
          (collab p r k m (Sum.inl w))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab, Sum.elim_inr]
    rw [TcG_symm, TcG_zone_B1 H hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, zero_mul,
      zero_mul]
  rw [hsum, sub_zero]
  simp only [T5G, Matrix.of_apply, rowlab, collab, Sum.elim_inr, Sum.elim_inl]
  rw [TcG_symm, TcG_U_low H hw.1 hw.2 (by omega) hx]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (x : ℕ)
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

include H in
lemma LP1Hyp.ScGy [Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))]
    (w : BU p r k) (y : Fin m) (hy : r + 2 * (y : ℕ) + 1 < p + k) :
    (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
        Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
          ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
        Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)) (Sum.inl w) (Sum.inr y) =
      if (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1 then rfC p (eCG (red p Fr.norm) (vk p q j))
      else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  have hy' := y.2
  have hw := w.2
  rw [invOf_Mp5G H, Matrix.sub_apply, UpMWG H]
  have hsum : ∑ c ∈ Ico k p,
      rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j)
        (rowlab p r k m (Sum.inl w)) c) *
        rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
        rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c
          (collab p r k m (Sum.inr y))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [collab, Sum.elim_inr]
    rw [TcG_zone_B1 H hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, mul_zero]
  rw [hsum, sub_zero]
  simp only [T5G, Matrix.of_apply, rowlab, collab, Sum.elim_inr, Sum.elim_inl]
  rw [TcG_U_low H hw.1 hw.2 (by omega) hy]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

end Sc

section Gle

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ}

lemma card_lowG (hUk : r < p + k) :
    (Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)).card +
      (Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)).card =
        min (p + k - r) (2 * m) := by
  have e1 : (Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)) =
      Finset.univ.filter (fun x : Fin m => (x : ℕ) < (p + k - r + 1) / 2) :=
    Finset.filter_congr fun x _ => by omega
  have e2 : (Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)) =
      Finset.univ.filter (fun y : Fin m => (y : ℕ) < (p + k - r) / 2) :=
    Finset.filter_congr fun x _ => by omega
  rw [e1, e2, Fin.card_filter_val_lt, Fin.card_filter_val_lt]
  omega

/-- **Theorem LP1, rank witness.** -/
theorem LP1Hyp.gleAt (H : LP1Hyp Fr p q o r m k j) :
    HasRankWit Fr p r m (fun a => wC p r k (Frame.hybRow r m a))
      (fun b => wC p r k (Frame.hybCol r m b)) (min (p + k - r) (2 * m) - m) := by
  classical
  have hkp := H.cfg.sg.hkp
  have hrp := H.hrp
  have hUk := H.hUk
  have hN2 := H.cfg.sg.hN2
  haveI : Invertible (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) := invMp5G H
  have hs0 : s0g k (red p Fr.norm) ≠ 0 := by
    unfold s0g rfX rfC
    rw [← map_add]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod p))).2
      (Polynomial.X_add_C_ne_zero _)
  let u0 : BU p r k := ⟨⟨r - p, by omega⟩, ⟨le_rfl, by show r - p < k; omega⟩⟩
  let cX : ℕ → BU p r k := fun z =>
    if h : r ≤ z ∧ z < p + k then
      ⟨⟨z - p, by omega⟩, ⟨by show r - p ≤ z - p; omega, by show z - p < k; omega⟩⟩ else u0
  have cX_val : ∀ z, r ≤ z → z < p + k → ((cX z).1 : ℕ) = z - p := by
    intro z h1 h2
    simp only [cX, dif_pos (And.intro h1 h2)]
  let LX := Finset.univ.filter (fun x : Fin m => r + 2 * (x : ℕ) < p + k)
  let LY := Finset.univ.filter (fun y : Fin m => r + 2 * (y : ℕ) + 1 < p + k)
  have hcard : LX.card + LY.card = min (p + k - r) (2 * m) := card_lowG hUk
  let Sc := T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
    Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
      ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
    Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)
  have h11 : Sc.toBlocks₁₁ = s0g k (red p Fr.norm) • (1 : Matrix (BU p r k) (BU p r k) _) := by
    ext u w
    simp only [Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    refine (H.ScUU u w).trans ?_
    by_cases h : u = w <;> simp [h]
  have h22 : Sc.toBlocks₂₂ = 0 := by
    ext x y
    simp only [Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.zero_apply]
    exact H.ScXY x y
  have hSchur : T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) -
      Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) *
        ⅟(Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) *
      Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) =
      fromBlocks (s0g k (red p Fr.norm) • (1 : Matrix (BU p r k) (BU p r k) _)) Sc.toBlocks₁₂
        Sc.toBlocks₂₁ 0 := by
    have hfb := Matrix.fromBlocks_toBlocks Sc
    rw [h11, h22] at hfb
    exact hfb.symm
  have hrank := rank_BbarC5_le (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
    (Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
    (Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
    (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j)) (s0g k (red p Fr.norm)) hs0
    Sc.toBlocks₂₁ Sc.toBlocks₁₂ hSchur LX LY (fun x => cX (r + 2 * (x : ℕ)))
    (fun y => cX (r + 2 * (y : ℕ) + 1)) (rfC p (eCG (red p Fr.norm) (vk p q j)))
    (by
      intro x hx w
      have hx' := (Finset.mem_filter.1 hx).2
      have := x.2
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply]
      refine (H.ScGx w x hx').trans ?_
      by_cases h : w = cX (r + 2 * (x : ℕ))
      · have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
        rw [cX_val _ (by omega) hx'] at h2
        rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg]
        intro h2
        apply h
        apply Subtype.ext; apply Fin.ext
        rw [cX_val _ (by omega) hx']
        omega)
    (by
      intro y hy w
      have hy' := (Finset.mem_filter.1 hy).2
      have := y.2
      simp only [Matrix.toBlocks₁₂, Matrix.of_apply]
      refine (H.ScGy w y hy').trans ?_
      by_cases h : w = cX (r + 2 * (y : ℕ) + 1)
      · have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
        rw [cX_val _ (by omega) hy'] at h2
        rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg]
        intro h2
        apply h
        apply Subtype.ext; apply Fin.ext
        rw [cX_val _ (by omega) hy']
        omega)
    (by
      intro x hx y hy
      have hx' := (Finset.mem_filter.1 hx).2
      have hy' := (Finset.mem_filter.1 hy).2
      have := x.2; have := y.2
      intro h
      have h2 := congrArg (fun t : BU p r k => (t.1 : ℕ)) h
      rw [cX_val _ (by omega) hx', cX_val _ (by omega) hy'] at h2
      omega)
  have hX : Fintype.card (Fin m) = m := Fintype.card_fin m
  have hLXm : LX.card ≤ m := by have := Finset.card_le_univ LX; rwa [Fintype.card_fin] at this
  have hLYm : LY.card ≤ m := by have := Finset.card_le_univ LY; rwa [Fintype.card_fin] at this
  have hBP := card_BU_BP (p := p) (r := r) (k := k)
  rw [hX] at hrank
  have hBT : BTcG p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) =
      (fromBlocks (T5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
        (Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
        (Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
        (Mp5G p r k (red p Fr.norm) (vk p q j) (vk2 p q j))).submatrix
      (eU p r k m) (eU p r k m) := by
    ext a b
    rw [Matrix.submatrix_apply, BTcG_eq]
  refine ⟨BTcG p r k m (red p Fr.norm) (vk p q j) (vk2 p q j), H.hred, ?_⟩
  have hle : (BTcG p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)).rank ≤ r + m := by
    simpa using Matrix.rank_le_card_width
      (BTcG p r k m (red p Fr.norm) (vk p q j) (vk2 p q j))
  rw [hBT, Matrix.rank_submatrix] at hle ⊢
  omega

/-- **Theorem LP1.**  `p^{τ' - (L - m)} · det Full(X)` is `ℤ_(p)`-integral, `L = min (p + k - r, 2m)`. -/
theorem LP1Hyp.gle (H : LP1Hyp Fr p q o r m k j) :
    GLE p (∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) -
      (min (p + k - r) (2 * m) - m)) (Fr.fullPoly r m) :=
  H.gleAt.gle

/-- LP1 for members of the hybrid family (any index type). -/
theorem LP1Hyp.gle_sub (H : LP1Hyp Fr p q o r m k j) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ia ib : ι → Fin r ⊕ Fin m) :
    GLE p (∑ i, wC p r k (Frame.hybRow r m (ia i)) + ∑ i, wC p r k (Frame.hybCol r m (ib i)) -
        (Fintype.card ι + (min (p + k - r) (2 * m) - m) - (r + m)))
      (Matrix.of fun i j => fullEntry Fr r m (ia i) (ib j)).det :=
  H.gleAt.gle_sub ia ib

end Gle

end CatalanCore.Uniform.Content.Smith
