module

public import CatalanCore.Uniform.Content.UFFamily.SevE
public import CatalanCore.Uniform.Content.UFWedge.Cell

@[expose] public section

/-!
# UF families, sevenths `a = 2`, `p ≡ 5 (mod 7)`: the family cell and its debit layer (lane H10)

`cellE` is ONE parametric `UFCellW` for every `(r, p)` of the family (`SevE.Valid'`): representative
`t₀ = r`, J-window `[r, k₀ - 1]`, top-extension window `[0, r - 1]`, kills of all border nodes
`≥ k₀` (columns `TC`, rows `TR`) by `SevE.killE`, and `u = k₀ + |TC| + |TR|` residues.
`layerE` is the resulting `DebitLayer`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFFamily.SevE

/-- The sevenths block constant `c = 2 α = 1/6`. -/
def cE : ℚ := 1 / 6

theorem cE_pos : 0 < cE := by unfold cE; norm_num

/-- Validity together with the `p`-integrality of the frame norm. -/
structure Valid' (Fr : Frame) (r p : ℕ) [Fact p.Prime] : Prop where
  v : Valid r p
  hnorm : Fr.norm ∈ S p
  hnorm0 : red p Fr.norm ≠ 0

theorem borderSize_E {r p : ℕ} (h : Valid r p) :
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

theorem hNp_E {r p : ℕ} (h : Valid r p) : 14 * (r / 12) < p * p := by
  have := h.hlo; nlinarith

theorem hsq_E {r p : ℕ} (h : Valid r p) :
    ∀ t, 1 ≤ t → t < 14 * (r / 12) → ¬ p ^ 2 ∣ 7 * t - 5 := by
  intro t ht1 ht2 hd
  have := Nat.le_of_dvd (by omega) hd
  have hlo := h.hlo
  have h3 : (14 * (r / 12) + 2) * (14 * (r / 12) + 2) ≤ p * p := Nat.mul_le_mul hlo hlo
  have h4 : 7 * t - 5 ≤ 7 * t := Nat.sub_le _ _
  have h5 : p ^ 2 = p * p := sq p
  generalize r / 12 = m at *
  nlinarith

theorem hu_gen {k p r k0 : ℕ} [Fact p.Prime] (xs ys : Fin k → ℕ) (TC TR : Finset (Fin k))
    (hxinj : Function.Injective xs) (hyinj : Function.Injective ys)
    (hxp : ∀ i, xs i < p) (hyp : ∀ i, ys i < p)
    (hTC : ∀ j ∈ TC, k0 ≤ ys j) (hTR : ∀ i ∈ TR, k0 ≤ xs i)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (hk0 : k0 ≤ p) (hr : 1 ≤ r)
    (hrk : r ≤ k0) :
    k0 + TC.card + TR.card ≤ (((Finset.Icc r (k0 - 1) ∪ Finset.Icc (r - r) (r - 1)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪
        (TR.image fun t => (((xs t : ℕ)) : ZMod p)))).card := by
  classical
  have hinj : ∀ a b : ℕ, a < p → b < p → ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) → a = b := by
    intro a b ha hb hab
    have := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  have hU : Finset.Icc r (k0 - 1) ∪ Finset.Icc (r - r) (r - 1) = Finset.Icc 0 (k0 - 1) := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [hU]
  have hA : ((Finset.Icc 0 (k0 - 1)).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = k0 := by
    rw [Finset.card_image_of_injOn, Nat.card_Icc]
    · omega
    · intro a ha b hb hab
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha hb
      exact hinj a b (by omega) (by omega) hab
  have hB : (TC.image fun t => (((ys t : ℕ)) : ZMod p)).card = TC.card := by
    rw [Finset.card_image_of_injOn]
    intro a _ b _ hab
    exact hyinj (hinj _ _ (hyp a) (hyp b) hab)
  have hC : (TR.image fun t => (((xs t : ℕ)) : ZMod p)).card = TR.card := by
    rw [Finset.card_image_of_injOn]
    intro a _ b _ hab
    exact hxinj (hinj _ _ (hxp a) (hxp b) hab)
  have hBC : Disjoint (TC.image fun t => (((ys t : ℕ)) : ZMod p))
      (TR.image fun t => (((xs t : ℕ)) : ZMod p)) := by
    rw [Finset.disjoint_left]
    intro x hxB hxC
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hxB
    obtain ⟨i, _, hi⟩ := Finset.mem_image.1 hxC
    exact hdist i j hi
  have hAB : Disjoint ((Finset.Icc 0 (k0 - 1)).image (fun t : ℕ => ((t : ℕ) : ZMod p)))
      ((TC.image fun t => (((ys t : ℕ)) : ZMod p)) ∪ (TR.image fun t => (((xs t : ℕ)) : ZMod p))) := by
    rw [Finset.disjoint_left]
    intro x hxA hxBC
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hxA
    rw [Finset.mem_Icc] at hn
    rcases Finset.mem_union.1 hxBC with hx | hx
    · obtain ⟨j, hj, hjn⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (hyp j) (by omega) hjn
      have := hTC j hj
      omega
    · obtain ⟨i, hi, hin⟩ := Finset.mem_image.1 hx
      have := hinj _ _ (hxp i) (by omega) hin
      have := hTR i hi
      omega
  rw [Finset.card_union_of_disjoint hAB, Finset.card_union_of_disjoint hBC, hA, hB, hC]
  omega

set_option maxHeartbeats 1600000 in
/-- **The family cell**: one `UFCellW` for every `(r, p)` of the sevenths `a = 2` class `p ≡ 5 (7)`. -/
noncomputable def cellE {Fr : Frame} (T : TwoTermData Fr 7 5) {r p : ℕ} [Fact p.Prime]
    (h : Valid' Fr r p) : UFCellW cE cE_pos Fr 7 5 T r p :=
  have hv := h.v
  have hr12 := hv.hr12
  have hr0 := hv.hr0
  have hlo := hv.hlo
  have hhi := hv.hhi
  have hp7 := hv.hp7
  have hk := hv.k0_spec
  have hk1 := hv.k0_lo
  have hk2 := hv.k0_hi
  have hr2 : r % 2 = 0 := by omega
  have hbs := borderSize_E hv
  have hNp := hNp_E hv
  have hsq := hsq_E hv
  have hrN : r + 2 * (altGeom cE cE_pos).borderSize r ≤ 14 * (r / 12) := by rw [hbs]; omega
  have hDs : (twoTermPoleData T hNp.le hsq h.hnorm h.hnorm0).singular = ttSing p 7 5 := rfl
  have hw : ∀ a Δ : ℕ, a + Δ < k0 p →
      NoSingWin (twoTermPoleData T hNp.le hsq h.hnorm h.hnorm0) a Δ :=
    fun a Δ ha => noSing (T := T) hv _ hDs a Δ ha
  have hpgt : 30 ≤ p := by omega
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
    tmax := k0 p - 1
    ht0N := by omega
    hrt := le_rfl
    htm := by omega
    hdiv := by
      rw [Nat.div_eq_of_lt (by omega : k0 p - 1 < p), Nat.div_eq_of_lt (by omega : r < p)]
    hw := hw r (k0 p - 1 - r) (by omega)
    TC := Finset.univ.filter fun j => k0 p ≤ ((altGeom cE cE_pos).geometry r).ys j
    TR := Finset.univ.filter fun j => k0 p ≤ ((altGeom cE cE_pos).geometry r).xs j
    kC := fun t ht => killE T hv hNp hsq h.hnorm h.hnorm0 rfl
      (fun a : ((altGeom cE cE_pos).geometry r).C => (a : ℕ)) ((altGeom cE cE_pos).geometry r).xs
      ((altGeom cE cE_pos).geometry r).ys (alt_hc' cE cE_pos hrN) (alt_hx' cE cE_pos hr2 hrN)
      (alt_hy' cE cE_pos hr2 hrN) Subtype.val_injective (alt_core_lt cE cE_pos) _
      (by simpa using ht) (alt_hy' cE cE_pos hr2 hrN t)
    kR := fun t ht => killE T hv hNp hsq h.hnorm h.hnorm0 rfl
      (fun a : ((altGeom cE cE_pos).geometry r).C => (a : ℕ)) ((altGeom cE cE_pos).geometry r).xs
      ((altGeom cE cE_pos).geometry r).ys (alt_hc' cE cE_pos hrN) (alt_hx' cE cE_pos hr2 hrN)
      (alt_hy' cE cE_pos hr2 hrN) Subtype.val_injective (alt_core_lt cE cE_pos) _
      (by simpa using ht) (alt_hx' cE cE_pos hr2 hrN t)
    tv := k0 p - 1
    htv0 := by omega
    htv := by omega
    htvN := by omega
    htvd := by
      rw [Nat.div_eq_of_lt (by omega : k0 p - 1 < p), Nat.div_eq_of_lt (by omega : r < p)]
    hwv := hw r (k0 p - 1 - r) (by omega)
    δ₁ := 1
    δ₂ := r
    hδ12 := by omega
    hδ2 := le_rfl
    hlt := by omega
    hr3 := by omega
    hqd := by
      rw [Nat.sub_self, Nat.zero_div, Nat.div_eq_of_lt (by omega : r < p)]
    hwd := hw (r - r) r (by omega)
    u := k0 p +
      (Finset.univ.filter fun j => k0 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card +
      (Finset.univ.filter fun j => k0 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card
    hu := hu_gen ((altGeom cE cE_pos).geometry r).xs ((altGeom cE cE_pos).geometry r).ys _ _
      (fun a b hab => (((altGeom cE cE_pos).geometry r).X'.orderEmbOfFin rfl).injective hab)
      (fun a b hab => (((altGeom cE cE_pos).geometry r).Y'.orderEmbOfFin
        ((altGeom cE cE_pos).geometry r).card_eq.symm).injective hab)
      (fun i => by have := alt_hx' cE cE_pos hr2 hrN i; omega)
      (fun i => by have := alt_hy' cE cE_pos hr2 hrN i; omega)
      (fun j hj => by simpa using hj) (fun j hj => by simpa using hj)
      (alt_hdist cE cE_pos hr2 (by rw [hbs]; omega)) (by omega) (by omega) (by omega) }

end CatalanCore.Uniform.Content.UFFamily.SevE
