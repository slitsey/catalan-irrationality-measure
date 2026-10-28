module

public import CatalanCore.Uniform.Content.UFWire.Layer

@[expose] public section

/-!
# UF cells without the `v ≠ 0` certificate at killed rows (lane H8)

`UFCell` asks, for every killed outside row `t ∈ TR`, for `v(x_t) ≠ 0` (`hvR`).  This is not a
certificate the bank needs: rows with `v(x_t) = 0` are simply not retained, so their residues may
still be counted in `I_J ∪ K`.  `UFCellF` drops `hvR`; the datum kills only the rows of `TR` with
`v ≠ 0` (a classical filter), and the price is still bounded using ALL residues of `TR`.
Only wedge-nonvanishing certificates (`hwC`, `hwR`) remain as exact-evaluation inputs.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFWire

set_option maxHeartbeats 1600000 in
/-- UF input of one `(r, p)` without `hvR`. -/
structure UFCellF (c : ℚ) (hc : 0 < c) (Fr : Frame) (q o : ℕ) (T : TwoTermData Fr q o)
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
  tmax : ℕ
  ht0N : t0 < N
  hrt : r ≤ t0
  htm : tmax < r + p
  hdiv : tmax / p = t0 / p
  hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0)
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
  tv : ℕ
  htv0 : t0 ≤ tv
  htv : tv < r + p
  htvN : tv < N
  htvd : tv / p = t0 / p
  hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0)
  δ₁ : ℕ
  δ₂ : ℕ
  hδ12 : δ₁ ≤ δ₂
  hδ2 : δ₂ ≤ t0
  hlt : t0 - δ₁ < r
  hr3 : r ≤ t0 - δ₂ + p
  hqd : (t0 - δ₂) / p = t0 / p
  hwd : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) (t0 - δ₂) δ₂
  /-- A lower bound for the number of residues of `I_J ∪ K` (all of `TR` counted). -/
  u : ℕ
  hu : u ≤ (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ} {T : TwoTermData Fr q o} {r p : ℕ}
  [Fact p.Prime]

open Classical in
/-- The rows of `TR` that are really retained (`v ≠ 0`). -/
noncomputable def UFCellF.TR' (X : UFCellF c hc Fr q o T r p) :
    Finset (Fin ((altGeom c hc).geometry r).k) :=
  X.TR.filter fun t => vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
    (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0
    ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p) ≠ 0

open Classical in
/-- The `SmithJKDatum` of a cell without `hvR`. -/
noncomputable def UFCellF.datum (X : UFCellF c hc Fr q o T r p) :
    SmithJKDatum (altGeom c hc) Fr r p :=
  altSmithJKDatum_UFK c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN X.hp X.hp2 X.ho X.hq X.t0
    X.tmax X.ht0N X.hrt X.htm X.hdiv X.hw X.TC X.TR'
    X.hwC (fun t ht => X.hwR t (Finset.mem_filter.1 ht).1) (fun t ht => (Finset.mem_filter.1 ht).2)

noncomputable def UFCellF.sigma (X : UFCellF c hc Fr q o T r p) : ℕ :=
  (winRows (r := r) c hc X.t0 X.tmax).card + (winCols (r := r) c hc X.t0 X.tmax).card -
    Fintype.card (Fin ((altGeom c hc).geometry r).k)

noncomputable def UFCellF.bound (X : UFCellF c hc Fr q o T r p) : ℕ :=
  2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
    (Fintype.card (Fin ((altGeom c hc).geometry r).k) + (X.sigma + (X.sigma - (p - X.u))))


/-- `v = 0` on the transport and top-extension residues of the cell. -/
theorem UFCellF.v_zero_I (X : UFCellF c hc Fr q o T r p) :
    ∀ c' ∈ ((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))),
      vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc X.hr T X.hNp X.hsq X.hnorm X.hnorm0 X.hrN).toBlocks₁₁ X.t0 c' = 0 := by
  classical
  have hC := altGeom_C c hc r
  have := X.htv0
  have := X.htv
  have := X.htvN
  intro c' hc'
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
  rcases Finset.mem_union.1 ht with ht | ht
  · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = X.t0 + Δ := ⟨t - X.t0, by omega⟩
    exact vS7_zero T X.hNp.le X.hsq X.hnorm X.hnorm0 X.hNp X.hp2 X.ho X.hq _ _ _
      (alt_hc' c hc X.hrN) (alt_hx' c hc X.hr X.hrN) (alt_hy' c hc X.hr X.hrN) X.t0 (X.t0 + Δ)
      (by omega)
      (alt_shiftData T X.hNp.le X.hsq X.hnorm X.hnorm0 _ hC X.t0 Δ X.hrt (by omega)
        (div_eq_of_between (by omega) ht2 X.htvd) (fun k hk1 hk2 => X.hwv k hk1 (by omega)))
  · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
    obtain ⟨δ, hδt, rfl⟩ : ∃ δ, δ ≤ X.t0 ∧ t = X.t0 - δ := ⟨X.t0 - t, by omega, by omega⟩
    have := X.hδ12
    have := X.hδ2
    have := X.hlt
    have := X.hr3
    refine vS7_topext T X.hNp.le X.hsq X.hnorm X.hnorm0 X.hNp X.ho X.hq _ hC _ _
      (alt_hc' c hc X.hrN) (alt_hx' c hc X.hr X.hrN) (alt_hy' c hc X.hr X.hrN) X.t0 δ X.ht0N
      X.hrt (by omega) (by omega) (by omega) (by omega) ?_ ?_
    · exact le_antisymm (Nat.div_le_div_right (by omega)) (X.hqd ▸ Nat.div_le_div_right (by omega))
    · intro k hk1 hk2
      exact X.hwd k (by omega) (by omega)

theorem UFCellF.price_le (X : UFCellF c hc Fr q o T r p) : X.datum.price ≤ X.bound := by
  classical
  have hzero : ∀ c' ∈ (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
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
      (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
        (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
        ((X.TR \ X.TR').image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR'.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) hzero
  have hsub : X.TR' ⊆ X.TR := Finset.filter_subset _ _
  have hset : (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
        (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
        ((X.TR \ X.TR').image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) ∪
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR'.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) =
      (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
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
  have eS : X.datum.J.sJ ≤ p - (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂)
      (X.t0 - X.δ₁)).image (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
      ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card := hcount
  have eR : X.datum.J.Jr = winRows c hc X.t0 X.tmax := rfl
  have eC : X.datum.J.Jc = winCols c hc X.t0 X.tmax := rfl
  have hu := X.hu
  unfold SmithJKDatum.price UFCellF.bound UFCellF.sigma
  rw [eR, eC]
  generalize (((Finset.Icc X.t0 X.tv ∪ Finset.Icc (X.t0 - X.δ₂) (X.t0 - X.δ₁)).image
      (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
    ((X.TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
      (X.TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card = U at eS hu
  generalize X.datum.J.sJ = sJ at eS ⊢
  omega

/-- **The UF debit layer without the `hvR` certificate.** -/
noncomputable def ufLayerF {depth : ℕ} (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (cell : ∀ r p : ℕ, ∀ [Fact p.Prime], valid r p → UFCellF c hc Fr q o T r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (cell r p h).bound ≤ base r p) :
    DebitLayer (altGeom c hc) Fr depth :=
  smithJKLayer valid base (fun r p _ h => (cell r p h).datum)
    (fun r p _ h => (cell r p h).price_le.trans (hbase r p h))

end CatalanCore.Uniform.Content.UFWire
