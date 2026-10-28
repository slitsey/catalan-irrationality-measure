module

public import CatalanCore.Uniform.Content.Smith.LP1Inv
public import CatalanCore.Uniform.Content.Smith.LP2Schur

@[expose] public section

/-!
# LP1: vanishing of table entries, elimination of `𝒫`, the Schur complement blocks

Port of `DefC5Zero`, `DefC5Schur` and `DefC5Final` to the frame-generic table `TcG`.
After eliminating `𝒫` the Schur complement is `[[s₀ I_U, G_Y], [G_X, 0]]` with `s₀ = x + nr⁻¹ H2(k-1)`
(PT with the sum over all of `[k,p)`), zone × zone vanishing, and low zone rows/columns equal to
`e·e_{z-p}`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix
  CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Smith

section Zero

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ} (H : LP1Hyp Fr p q o r m k j)

omit H in
lemma TCgenG_zero {nr v v2 : ZMod p} {w A B : ℕ} (hw : 2 ≤ w) (hp : w = 2 → B - A ≠ p) :
    TCgenG p k nr v v2 w A B = 0 := by
  unfold TCgenG; split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; exact hp ‹_› ‹_›.2)

lemma TcG_lt_zero {nr v v2 : ZMod p} {A B : ℕ} (hAB : A < B)
    (hw : 2 ≤ wC p r k A + wC p r k B) (hp : wC p r k A + wC p r k B = 2 → B - A ≠ p) :
    TcG p r k nr v v2 A B = 0 := by
  rw [TcG_lt hAB]; exact TCgenG_zero hw hp

include H in
/-- A `P0` label against `U` or a zone label. -/
lemma TcG_P0 {nr v v2 : ZMod p} {c L : ℕ} (hc : c < r - p)
    (hL : (r - p ≤ L ∧ L < k) ∨ (r ≤ L ∧ L < r + 2 * m)) : TcG p r k nr v v2 c L = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk; have hN2 := H.cfg.sg.hN2
  have hcl : c < L := by omega
  have wc : wC p r k c = 1 := wC_P' (by omega) (by omega)
  rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have wl : wC p r k L = 0 := wC_U' H h1 h2
    rw [TcG_lt hcl, wc, wl]
    have hs : singG p k v v2 c L = 0 := by
      unfold singG; split_ifs <;> first | (exfalso; omega) | ring
    unfold TCgenG
    rw [if_neg (by omega), if_pos (by omega), hs, mul_zero]
  · by_cases hlow : L < p + k
    · apply TcG_lt_zero hcl
      · have := wC_low' h1 hlow; omega
      · intro _; omega
    · apply TcG_lt_zero hcl
      · have := wC_high' H (A := L) (by omega); omega
      · intro _; omega

include H in
/-- A zone label against `B1`: zero unless `z - c = p`. -/
lemma TcG_zone_B1 {nr v v2 : ZMod p} {c z : ℕ} (hc1 : k ≤ c) (hc2 : c < p) (hz1 : r ≤ z)
    (hz2 : z < r + 2 * m) (hzc : z - c ≠ p) : TcG p r k nr v v2 c z = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk
  have hcl : c < z := by omega
  have wc : wC p r k c = 1 := wC_P' (by omega) (by omega)
  apply TcG_lt_zero hcl
  · by_cases hlow : z < p + k
    · have := wC_low' hz1 hlow; omega
    · have := wC_high' H (A := z) (by omega); omega
  · intro _; exact hzc

include H in
/-- Zone × zone vanishes. -/
lemma TcG_zone_zone {nr v v2 : ZMod p} {z y : ℕ} (hz1 : r ≤ z) (hz2 : z < r + 2 * m)
    (hy1 : r ≤ y) (hy2 : y < r + 2 * m) (hzy : z ≠ y) : TcG p r k nr v v2 z y = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk; have hN2 := H.cfg.sg.hN2
  have wz : 1 ≤ wC p r k z := by
    by_cases h : z < p + k
    · rw [wC_low' hz1 h]; omega
    · rw [wC_high' H (by omega)]
  have wy : 1 ≤ wC p r k y := by
    by_cases h : y < p + k
    · rw [wC_low' hy1 h]; omega
    · rw [wC_high' H (by omega)]
  rcases lt_or_gt_of_ne hzy with h | h
  · apply TcG_lt_zero h
    · omega
    · intro _; omega
  · rw [TcG_symm]
    apply TcG_lt_zero h
    · omega
    · intro _; omega

include H in
/-- A low zone label against `U`. -/
lemma TcG_U_low {w z : ℕ} (hw1 : r - p ≤ w) (hw2 : w < k) (hz1 : r ≤ z) (hz2 : z < p + k) :
    TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) w z =
      if z - w = p then eCG (red p Fr.norm) (vk p q j) else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk
  have hwz : w < z := by omega
  rw [TcG_lt hwz, wC_U' H hw1 hw2, wC_low' hz1 hz2]
  unfold TCgenG
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases hd : z - w = p
  · have hs : singG p k (vk p q j) (vk2 p q j) w z = vk p q j + 1 := by
      unfold singG; split_ifs <;> first | (exfalso; omega) | ring
    rw [if_pos ⟨by omega, hd⟩, if_pos hd, hs]; rfl
  · rw [if_neg (fun h => hd h.2), if_neg hd]

include H in
lemma TcG_UU {u w : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hw1 : r - p ≤ w) (hw2 : w < k) :
    TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) u w =
      Tsym p k (red p Fr.norm) (vk p q j) u w := by
  rcases lt_trichotomy u w with h | h | h
  · rw [TcG_lt h, wC_U' H hu1 hu2, wC_U' H hw1 hw2]
    unfold Tsym; rw [if_pos h]
    unfold TCgenG Tg
    simp [hw2]
  · subst h
    rw [TcG_diag, wC_U' H hu1 hu2, Tsym_diag_lt p k _ _ hu2]
    unfold TCDgenG
    simp
  · rw [TcG_symm, Tsym_symm, TcG_lt h, wC_U' H hu1 hu2, wC_U' H hw1 hw2]
    unfold Tsym; rw [if_pos h]
    unfold TCgenG Tg
    simp [hu2]

include H in
lemma TcG_UB1 {u c : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hc1 : k ≤ c) (hc2 : c < p) :
    TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) u c =
      Tsym p k (red p Fr.norm) (vk p q j) u c := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  have huc : u < c := by omega
  rw [TcG_lt huc, wC_U' H hu1 hu2, wC_P' (by omega) (by omega), Tsym_lh hu2 hc1 hc2]
  have hs : singG p k (vk p q j) (vk2 p q j) u c = vk p q j := by
    unfold singG; split_ifs <;> first | (exfalso; omega) | ring
  unfold TCgenG
  rw [if_neg (by omega), if_pos (by omega), hs]
  rw [mul_inv]; ring

end Zero

section Elim

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {q o r m k j : ℕ} (H : LP1Hyp Fr p q o r m k j)

lemma IvalG_col_B1 {nr v : ZMod p} {α β : ℕ} (hS : LP1Hyp Fr p q o r m k j) (hα : α < r)
    (hb1 : k ≤ β) (hb2 : β < p) :
    IvalG nr v r α β = if β = α then (dBG nr v)⁻¹ else 0 := by
  have := hS.cfg.sg.hkp; have := hS.hrp; have := hS.hUk; have := hS.cfg.sg.hN2
  unfold IvalG; split_ifs <;> first | rfl | (exfalso; omega)

include H in
lemma IvalG_col_B2 {nr v : ZMod p} {α β : ℕ} (hα : r - p ≤ α) (hb : p ≤ β) (hβr : β < r)
    (hαr : α < r) : IvalG nr v r α β = 0 := by
  have := H.cfg.sg.hkp; have := H.hrp; have := H.hUk; have := H.cfg.sg.hN2
  unfold IvalG; split_ifs <;> first | rfl | (exfalso; omega)

include H in
lemma Up5G_P0 (a : BU p r k ⊕ Fin m) (α : BP p r k) (h : (α.1 : ℕ) < r - p) :
    Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a α = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  simp only [Up5G, Matrix.of_apply]
  rcases a with u | x
  · rw [rowlab, Sum.elim_inl, TcG_symm, TcG_P0 H h (Or.inl u.2), rfC_zero]
  · have hx := x.2
    rw [rowlab, Sum.elim_inr, TcG_symm, TcG_P0 H h (Or.inr ⟨by omega, by omega⟩), rfC_zero]

include H in
lemma Wp5G_P0 (b : BU p r k ⊕ Fin m) (α : BP p r k) (h : (α.1 : ℕ) < r - p) :
    Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) α b = 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp
  simp only [Wp5G, Matrix.of_apply]
  rcases b with u | y
  · rw [collab, Sum.elim_inl, TcG_P0 H h (Or.inl u.2), rfC_zero]
  · have hy := y.2
    rw [collab, Sum.elim_inr, TcG_P0 H h (Or.inr ⟨by omega, by omega⟩), rfC_zero]

include H in
lemma UpMinv_Wp_termG (a b : BU p r k ⊕ Fin m) (β : BP p r k) :
    (∑ α : BP p r k, Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a α *
        Minv5G (red p Fr.norm) (vk p q j) r k α β) *
      Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) β b =
      if k ≤ (β.1 : ℕ) ∧ (β.1 : ℕ) < p then
        rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) (rowlab p r k m a) (β.1 : ℕ)) *
          rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
          rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) (β.1 : ℕ) (collab p r k m b))
      else 0 := by
  have hkp := H.cfg.sg.hkp; have hrp := H.hrp; have hUk := H.hUk; have hN2 := H.cfg.sg.hN2
  have hβ := β.2
  have hβr := β.1.2
  rcases (by omega : (β.1 : ℕ) < r - p ∨ ((k ≤ (β.1 : ℕ)) ∧ (β.1 : ℕ) < p) ∨ p ≤ (β.1 : ℕ)) with
    h | h | h
  · rw [Wp5G_P0 H b β h, mul_zero, if_neg (by omega)]
  · rw [if_pos h]
    have hsum : ∑ α : BP p r k, Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a α *
        Minv5G (red p Fr.norm) (vk p q j) r k α β =
        Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a β *
          rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) := by
      rw [Finset.sum_eq_single β]
      · simp only [Minv5G, Matrix.of_apply]
        rw [IvalG_col_B1 H β.1.2 h.1 h.2, if_pos rfl]
      · intro α _ hα
        have : (β.1 : ℕ) ≠ (α.1 : ℕ) := fun h' => hα (Subtype.ext (Fin.ext h'.symm))
        simp only [Minv5G, Matrix.of_apply]
        rw [IvalG_col_B1 H α.1.2 h.1 h.2, if_neg this, rfC_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    rw [hsum]
    simp only [Up5G, Wp5G, Matrix.of_apply]
  · rw [if_neg (by omega)]
    have hsum : ∑ α : BP p r k, Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) a α *
        Minv5G (red p Fr.norm) (vk p q j) r k α β = 0 := by
      refine Finset.sum_eq_zero fun α _ => ?_
      by_cases hα : (α.1 : ℕ) < r - p
      · rw [Up5G_P0 H a α hα, zero_mul]
      · simp only [Minv5G, Matrix.of_apply]
        rw [IvalG_col_B2 H (by omega) h β.1.2 α.1.2, rfC_zero, mul_zero]
    rw [hsum, zero_mul]

include H in
lemma sum_BP_B1G {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ β : BP p r k, (if k ≤ (β.1 : ℕ) ∧ (β.1 : ℕ) < p then F β.1 else 0) =
      ∑ c ∈ Ico k p, F c := by
  have hrp := H.hrp
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun β _ => (β.1 : ℕ)) ?_ ?_ ?_ ?_
  · intro β hβ
    have := Finset.mem_filter.1 hβ
    simp only [Finset.mem_Ico]; exact this.2
  · intro a _ b _ h; exact Subtype.ext (Fin.ext h)
  · intro c hc
    have := Finset.mem_Ico.1 hc
    exact ⟨⟨⟨c, by omega⟩, by simp only; omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact this, rfl⟩
  · intro β _; rfl

include H in
/-- **`Up5G · Minv5G · Wp5G` is the weighted `B1`-sum.** -/
lemma UpMWG (a b : BU p r k ⊕ Fin m) :
    (Up5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j) * Minv5G (red p Fr.norm) (vk p q j) r k *
        Wp5G p r k m (red p Fr.norm) (vk p q j) (vk2 p q j)) a b =
      ∑ c ∈ Ico k p,
        rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) (rowlab p r k m a) c) *
          rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
          rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c (collab p r k m b)) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun β _ => UpMinv_Wp_termG H a b β)]
  exact sum_BP_B1G H (fun c => rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j)
    (rowlab p r k m a) c) * rfC p ((dBG (red p Fr.norm) (vk p q j))⁻¹) *
    rfC p (TcG p r k (red p Fr.norm) (vk p q j) (vk2 p q j) c (collab p r k m b)))

end Elim

end CatalanCore.Uniform.Content.Smith
