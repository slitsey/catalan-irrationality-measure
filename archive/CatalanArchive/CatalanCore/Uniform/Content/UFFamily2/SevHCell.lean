module

public import CatalanCore.Uniform.Content.UFFamily2.SevH
public import CatalanCore.Uniform.Content.UFFamily.SevECell

@[expose] public section

/-!
# UF family H (non-empty fibers): the family cell (lane H, H11)

`cellH` is ONE parametric `UFCellW` for every `(r, p)` of `SevH.Valid'`: representative `t₀ = r`
(fiber `{r - p}`), J-window `[r, k₁ - 1]`, top-extension window `[p, r - 1]` (`δ₁ = 1`, `δ₂ = r - p`),
kills of all border nodes `≥ k₁` (columns `TC`, rows `TR`) by `SevH.killH`, and
`u = (k₁ - p) + |TC| + |TR|` residues (`hu_gen2`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFFamily
  CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFFamily2.SevH

/-- Validity together with the `p`-integrality of the frame norm and `norm = 1`. -/
structure Valid' (Fr : Frame) (r p : ℕ) [Fact p.Prime] : Prop where
  v : Valid r p
  hnorm : Fr.norm ∈ S p
  hnorm0 : red p Fr.norm ≠ 0
  hnrm : Fr.norm = 1

theorem borderSize_H {r p : ℕ} (h : Valid r p) :
    (altGeom cE cE_pos).borderSize r = r / 12 := by
  have hr12 := h.hr12
  have hr0 := h.hr0
  obtain ⟨m, rfl⟩ : ∃ m, r = 12 * m := ⟨r / 12, by omega⟩
  have hm : 0 < m := by omega
  have hr : (12 * m) % 2 = 0 := by omega
  rw [altGeom_borderSize cE cE_pos hr]
  have h1 : ⌈cE * ((12 * m : ℕ) : ℚ) / 2⌉₊ = m := by
    have : cE * ((12 * m : ℕ) : ℚ) / 2 = (m : ℚ) := by unfold cE; push_cast; ring
    rw [this, Nat.ceil_natCast]
  have h2 : ⌈(cE * ((12 * m : ℕ) : ℚ) - 1) / 2⌉₊ = m := by
    rw [Nat.ceil_eq_iff hm.ne']
    have hc : ((m - 1 : ℕ) : ℚ) = (m : ℚ) - 1 := by rw [Nat.cast_sub hm]; simp
    rw [hc]
    unfold cE; push_cast
    constructor <;> linarith
  rw [h1, h2, min_self]
  omega

theorem hNp_H {r p : ℕ} (h : Valid r p) : 14 * (r / 12) < p * p := by
  have h1 := h.hlo
  have h2 := h.p_big
  have : 29 * (7 * (r / 12) + 1) ≤ p * p := Nat.mul_le_mul h2 h1
  omega

theorem hsq_H {r p : ℕ} (h : Valid r p) :
    ∀ t, 1 ≤ t → t < 14 * (r / 12) → ¬ p ^ 2 ∣ 7 * t - 5 := by
  intro t ht1 ht2 hd
  have := Nat.le_of_dvd (by omega) hd
  have h1 := h.hlo
  have h2 := h.p_big
  have h3 : 29 * (7 * (r / 12) + 1) ≤ p * p := Nat.mul_le_mul h2 h1
  have h5 : p ^ 2 = p * p := sq p
  omega

theorem hu_gen2 {k p lo hi t0 tv d1 d2 : ℕ} [Fact p.Prime] (xs ys : Fin k → ℕ)
    (TC TR : Finset (Fin k)) (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (hxp : ∀ i ∈ TR, xs i < lo + p) (hyp : ∀ i ∈ TC, ys i < lo + p)
    (hTC : ∀ j ∈ TC, hi + 1 ≤ ys j) (hTR : ∀ i ∈ TR, hi + 1 ≤ xs i)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (hlh : lo ≤ hi + 1)
    (hhi : hi < lo + p)
    (hU : Finset.Icc t0 tv ∪ Finset.Icc (t0 - d2) (t0 - d1) = Finset.Icc lo hi) :
    (hi + 1 - lo) + TC.card + TR.card ≤ (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - d2) (t0 - d1)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪
        (TR.image fun t => (((xs t : ℕ)) : ZMod p)))).card := by
  classical
  have hinj : ∀ a b : ℕ, lo ≤ a → a < lo + p → lo ≤ b → b < lo + p →
      ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) → a = b := by
    intro a b ha1 ha2 hb1 hb2 hab
    have h1 := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rcases le_total a b with hle | hle
    · have hd := (Nat.modEq_iff_dvd' hle).1 h1
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
    · have hd := (Nat.modEq_iff_dvd' hle).1 h1.symm
      have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
      omega
  rw [hU]
  have hA : ((Finset.Icc lo hi).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = hi + 1 - lo := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    intro a ha b hb hab
    simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
    exact hinj a b (by omega) (by omega) (by omega) (by omega) hab
  have hB : (TC.image fun t => (((ys t : ℕ)) : ZMod p)).card = TC.card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    have := hTC a ha
    have := hTC b hb
    have := hyp a ha
    have := hyp b hb
    exact hyinj (hinj _ _ (by omega) (by omega) (by omega) (by omega) hab)
  have hC : (TR.image fun t => (((xs t : ℕ)) : ZMod p)).card = TR.card := by
    rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    have := hTR a ha
    have := hTR b hb
    have := hxp a ha
    have := hxp b hb
    exact hxinj (hinj _ _ (by omega) (by omega) (by omega) (by omega) hab)
  have hBC : Disjoint (TC.image fun t => (((ys t : ℕ)) : ZMod p))
      (TR.image fun t => (((xs t : ℕ)) : ZMod p)) := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hxB
    obtain ⟨i, _, hi'⟩ := Finset.mem_image.1 hxC
    exact hdist i j hi'
  have hAB : Disjoint ((Finset.Icc lo hi).image (fun t : ℕ => ((t : ℕ) : ZMod p)))
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪ (TR.image fun t => (((xs t : ℕ)) : ZMod p))) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBC
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hxA
    rw [Finset.mem_Icc] at hn
    rcases Finset.mem_union.1 hxBC with hx | hx
    · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (by have := hTC j hj; omega) (hyp j hj) (by omega) (by omega) hjn
      have := hTC j hj
      omega
    · obtain ⟨i, hi', hin⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (by have := hTR i hi'; omega) (hxp i hi') (by omega) (by omega) hin
      have := hTR i hi'
      omega
  rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC, hA, hB, hC]
  omega

set_option maxHeartbeats 1600000 in
/-- **The family cell**: one `UFCellW` for every `(r, p)` of the family `SevH.Valid'`. -/
noncomputable def cellH {Fr : Frame} (T : TwoTermData Fr 7 5) {r p : ℕ} [Fact p.Prime]
    (h : Valid' Fr r p) : UFCellW cE cE_pos Fr 7 5 T r p :=
  have hv := h.v
  have hr12 := hv.hr12
  have hr0 := hv.hr0
  have hlo := hv.hlo
  have hhi := hv.hhi
  have hp7 := hv.hp7
  have hk := hv.k1_spec
  have hk1 := hv.k1_lo
  have hk2 := hv.k1_hi
  have hpr := hv.p_lt_r
  have hp29 := hv.p_big
  have h2p := hv.two_p
  have hr2 : r % 2 = 0 := by omega
  have hbs := borderSize_H hv
  have hNp := hNp_H hv
  have hsq := hsq_H hv
  have hrN : r + 2 * (altGeom cE cE_pos).borderSize r ≤ 14 * (r / 12) := by rw [hbs]; omega
  have hDs : (twoTermPoleData T hNp.le hsq h.hnorm h.hnorm0).singular = ttSing p 7 5 := rfl
  have hw : ∀ a Δ : ℕ, p ≤ a → a + Δ < k1 p →
      NoSingWin (twoTermPoleData T hNp.le hsq h.hnorm h.hnorm0) a Δ :=
    fun a Δ ha hb => noSing (T := T) hv _ hDs a Δ ha hb
  have hcov : ∀ x, x < r → ∃ a : ((altGeom cE cE_pos).geometry r).C, (a : ℕ) = x := fun x hx =>
    ⟨⟨x, by rw [altGeom_C cE cE_pos r]; exact Finset.mem_range.2 hx⟩, rfl⟩
  { hr := hr2
    N := 14 * (r / 12)
    hNp := hNp
    hsq := hsq
    hnorm := h.hnorm
    hnorm0 := h.hnorm0
    hrN := hrN
    hp := by rw [hbs]; omega
    hp2 := by omega
    ho := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
    hq := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega
    t0 := r
    tmax := k1 p - 1
    ht0N := by omega
    hrt := le_rfl
    htm := by omega
    hdiv := by
      rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
        Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    hw := hw r (k1 p - 1 - r) (by omega) (by omega)
    TC := Finset.univ.filter fun j => k1 p ≤ ((altGeom cE cE_pos).geometry r).ys j
    TR := Finset.univ.filter fun j => k1 p ≤ ((altGeom cE cE_pos).geometry r).xs j
    kC := fun t ht => killH T hv hNp hsq h.hnorm h.hnorm0 h.hnrm rfl
      (fun a : ((altGeom cE cE_pos).geometry r).C => (a : ℕ)) ((altGeom cE cE_pos).geometry r).xs
      ((altGeom cE cE_pos).geometry r).ys (alt_hc' cE cE_pos hrN) (alt_hx' cE cE_pos hr2 hrN)
      (alt_hy' cE cE_pos hr2 hrN) Subtype.val_injective (alt_core_lt cE cE_pos) hcov _
      (by simpa using ht) (alt_hy' cE cE_pos hr2 hrN t)
    kR := fun t ht => killH T hv hNp hsq h.hnorm h.hnorm0 h.hnrm rfl
      (fun a : ((altGeom cE cE_pos).geometry r).C => (a : ℕ)) ((altGeom cE cE_pos).geometry r).xs
      ((altGeom cE cE_pos).geometry r).ys (alt_hc' cE cE_pos hrN) (alt_hx' cE cE_pos hr2 hrN)
      (alt_hy' cE cE_pos hr2 hrN) Subtype.val_injective (alt_core_lt cE cE_pos) hcov _
      (by simpa using ht) (alt_hx' cE cE_pos hr2 hrN t)
    tv := k1 p - 1
    htv0 := by omega
    htv := by omega
    htvN := by omega
    htvd := by
      rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
        Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    hwv := hw r (k1 p - 1 - r) (by omega) (by omega)
    δ₁ := 1
    δ₂ := r - p
    hδ12 := by omega
    hδ2 := by omega
    hlt := by omega
    hr3 := by omega
    hqd := by
      rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
        Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega)]
    hwd := hw (r - (r - p)) (r - p) (by omega) (by omega)
    u := (k1 p - 1 + 1 - p) +
      (Finset.univ.filter fun j => k1 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card +
      (Finset.univ.filter fun j => k1 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card
    hu := hu_gen2 (lo := p) (hi := k1 p - 1) ((altGeom cE cE_pos).geometry r).xs
      ((altGeom cE cE_pos).geometry r).ys _ _
      (fun a b hab => (((altGeom cE cE_pos).geometry r).X'.orderEmbOfFin rfl).injective hab)
      (fun a b hab => (((altGeom cE cE_pos).geometry r).Y'.orderEmbOfFin
        ((altGeom cE cE_pos).geometry r).card_eq.symm).injective hab)
      (fun i _ => by have := alt_hx' cE cE_pos hr2 hrN i; omega)
      (fun i _ => by have := alt_hy' cE cE_pos hr2 hrN i; omega)
      (fun j hj => by have := (Finset.mem_filter.1 hj).2; omega)
      (fun j hj => by have := (Finset.mem_filter.1 hj).2; omega)
      (alt_hdist cE cE_pos hr2 (by rw [hbs]; omega)) (by omega) (by omega)
      (by ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega) }

end CatalanCore.Uniform.Content.UFFamily2.SevH
