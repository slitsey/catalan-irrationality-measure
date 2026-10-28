module

public import CatalanCore.Uniform.Content.UFFamily3.Run
public import CatalanCore.Uniform.Content.UFFamily3.Count
public import CatalanCore.Uniform.Content.UFWire.CellFree

@[expose] public section

/-!
# The UF window cell with a mid-border `J`-window (lane H, H12)

`Cell3` is `UFCellF` without the top-extension window and with the transport window `[t₀, t_v]`
free to run past the border (`t_v` is the last residue before the next singular index): the data
needed by the thirds bank, where the best `J` is a run in the middle of the border.

* `Cell3.datum` is the `altSmithJKDatum_UFK` of the window `[t₀, t_v]` and the kill sets `TC, TR`;
* `Cell3.price_le : datum.price ≤ bound`, `bound = 2 (|C| + m) - (m + σ + (σ - (p - u)))`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Wire

namespace CatalanCore.Uniform.Content.UFFamily3

set_option maxHeartbeats 1600000 in
/-- UF input of one `(r, p)`: the window `[t₀, t_v]` and kill sets. -/
structure Cell3 (c : ℚ) (hc : 0 < c) (Fr : Frame) (q o : ℕ) (T : TwoTermData Fr q o)
    (r p : ℕ) [Fact p.Prime] where
  hr : r % 2 = 0
  N : ℕ
  hNp : N < p * p
  hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o
  hnorm : Fr.norm ∈ S p
  hnorm0 : red p Fr.norm ≠ 0
  hrN : r + 2 * (altGeom c hc).borderSize r ≤ N
  hp : 2 * (altGeom c hc).borderSize r ≤ p
  hp2 : p ≠ 2
  ho : (o : ZMod p) ≠ 0
  hq : (q : ZMod p) ≠ 0
  t0 : ℕ
  tv : ℕ
  ht0N : t0 < N
  hrt : r ≤ t0
  htv0 : t0 ≤ tv
  htv : tv < r + p
  htvN : tv < N
  hdiv : tv / p = t0 / p
  hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0)
  TC : Finset (Fin ((altGeom c hc).geometry r).k)
  TR : Finset (Fin ((altGeom c hc).geometry r).k)
  hwC : ∀ t ∈ TC, wedgeC (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0
  hwR : ∀ t ∈ TR, wedgeR (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0
  u : ℕ
  hu : u ≤ (((Finset.Icc t0 tv).image (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {T : TwoTermData Fr q o} {r p : ℕ}
  [Fact p.Prime]

open Classical in
/-- The rows of `TR` that are really retained (`v ≠ 0`). -/
noncomputable def Cell3.TR' (X : Cell3 c hc Fr q o T r p) :
    Finset (Fin ((altGeom c hc).geometry r).k) :=
  X.TR.filter fun t => vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
    (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0
    ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p) ≠ 0

open Classical in
/-- The `SmithJKDatum` of a cell. -/
noncomputable def Cell3.datum (X : Cell3 c hc Fr q o T r p) : SmithJKDatum (altGeom c hc) Fr r p :=
  altSmithJKDatum_UFK c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN X.hp X.hp2 X.ho X.hq X.t0
    X.tv X.ht0N X.hrt X.htv X.hdiv X.hw X.TC X.TR'
    X.hwC (fun t ht => X.hwR t (Finset.mem_filter.1 ht).1) (fun t ht => (Finset.mem_filter.1 ht).2)

noncomputable def Cell3.sigma (X : Cell3 c hc Fr q o T r p) : ℕ :=
  (winRows (r := r) c hc X.t0 X.tv).card + (winCols (r := r) c hc X.t0 X.tv).card -
    Fintype.card (Fin ((altGeom c hc).geometry r).k)

noncomputable def Cell3.bound (X : Cell3 c hc Fr q o T r p) : ℕ :=
  2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
    (Fintype.card (Fin ((altGeom c hc).geometry r).k) + (X.sigma + (X.sigma - (p - X.u))))

/-- `v = 0` on the transport residues of the cell. -/
theorem Cell3.v_zero_I (X : Cell3 c hc Fr q o T r p) :
    ∀ c' ∈ ((Finset.Icc X.t0 X.tv).image (fun t : ℕ => ((t : ℕ) : ZMod p))),
      vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0 c' = 0 := by
  classical
  have hC := altGeom_C c hc r
  have := X.htv0
  have := X.htv
  have := X.htvN
  intro c' hc'
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
  obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
  obtain ⟨Δ, rfl⟩ : ∃ Δ, t = X.t0 + Δ := ⟨t - X.t0, by omega⟩
  exact vS7_zero T X.hNp.le X.hsq X.hnorm X.hnorm0 X.hNp X.hp2 X.ho X.hq _ _ _
    (alt_hc' c hc X.hrN) (alt_hx' c hc X.hr X.hrN) (alt_hy' c hc X.hr X.hrN) X.t0 (X.t0 + Δ)
    (by omega)
    (alt_shiftData T X.hNp.le X.hsq X.hnorm X.hnorm0 _ hC X.t0 Δ X.hrt (by omega)
      (div_eq_of_between (by omega) ht2 X.hdiv) (fun k hk1 hk2 => X.hw k hk1 (by omega)))

theorem Cell3.price_le (X : Cell3 c hc Fr q o T r p) : X.datum.price ≤ X.bound := by
  classical
  have hzero : ∀ c' ∈ (((Finset.Icc X.t0 X.tv).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((X.TR \ X.TR').image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))),
      vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0 c' = 0 := by
    intro c' hc'
    rcases Finset.mem_union.1 hc' with h | h
    · exact X.v_zero_I c' h
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
      by_contra hne
      exact h2 (Finset.mem_filter.2 ⟨h1, hne⟩)
  have hcount := card_retOf_sdiff_le (vS7 p q o Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0)
      (((Finset.Icc X.t0 X.tv).image
        (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
        ((X.TR \ X.TR').image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR'.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) hzero
  have hsub : X.TR' ⊆ X.TR := Finset.filter_subset _ _
  have hset : (((Finset.Icc X.t0 X.tv).image
        (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
        ((X.TR \ X.TR').image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) ∪
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR'.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) =
      (((Finset.Icc X.t0 X.tv).image
        (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff]
    constructor
    · rintro ((h | ⟨t, ⟨h1, _⟩, h3⟩) | (h | ⟨t, h1, h3⟩))
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨t, h1, h3⟩)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨t, hsub h1, h3⟩)
    · rintro (h | h | ⟨t, h1, h3⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · by_cases ht : t ∈ X.TR'
        · exact Or.inr (Or.inr ⟨t, ht, h3⟩)
        · exact Or.inl (Or.inr ⟨t, ⟨h1, ht⟩, h3⟩)
  rw [hset] at hcount
  have eS : X.datum.J.sJ ≤ p - (((Finset.Icc X.t0 X.tv).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card := hcount
  have eR : X.datum.J.Jr = winRows c hc X.t0 X.tv := rfl
  have eC : X.datum.J.Jc = winCols c hc X.t0 X.tv := rfl
  have hu := X.hu
  unfold SmithJKDatum.price Cell3.bound Cell3.sigma
  rw [eR, eC]
  generalize (((Finset.Icc X.t0 X.tv).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card = U at eS hu
  generalize X.datum.J.sJ = sJ at eS ⊢
  omega

/-- **The UF debit layer from window cells.** -/
noncomputable def layer3 {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → Cell3 c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    DebitLayer (altGeom c hc) Fr depth :=
  smithJKLayer valid base (fun r p _ h => (cell r p h).datum)
    (fun r p _ h => (cell r p h).price_le.trans (hbase r p h))

end CatalanCore.Uniform.Content.UFFamily3
