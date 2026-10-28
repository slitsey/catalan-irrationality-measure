module

public import CatalanCore.Uniform.Content.UFMoments.S7FinalK
public import CatalanCore.Uniform.Content.UFMoments.AltPriceUF

@[expose] public section

/-!
# The UF Smith datum of the alternating geometry WITH wedge kills, and its price

`altSmithJKDatum_UFK`: `altSmithJKDatum_UF` plus kills of outside border columns `TC` / rows `TR`
with nonzero wedges.  `altSmithJKDatum_UFK_price`: with `I_J` = transport window ∪ top-extension
window and `K` = killed residues,

  `price ≤ 2(|C| + m) - (m + σ + (σ - (p - |I_J ∪ K|)))`   (Theorem UF's `s_J = #(ℤ/p \\ I_J) - #K`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape

namespace CatalanCore.Uniform.Content.UFMoments

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

theorem card_retOf_sdiff_le {p : ℕ} [Fact p.Prime] (v : ZMod p → RatFunc (ZMod p))
    (Iset Kset : Finset (ZMod p)) (hv : ∀ c ∈ Iset, v c = 0) :
    (retOf v \ Kset).card ≤ p - (Iset ∪ Kset).card := by
  classical
  have hsub : retOf v \ Kset ⊆ univ \ (Iset ∪ Kset) := by
    intro c hc'
    simp only [Finset.mem_sdiff, retOf, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
    exact ⟨fun h => hc'.1 (hv c h), hc'.2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card] at this
  exact this

section
variable (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 tmax : ℕ) (ht0N : t0 < N) (hrt : r ≤ t0) (htm : tmax < r + p)
    (hdiv : tmax / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tmax - t0))

/-- The lift of the alternating geometry (abbreviation). -/
noncomputable abbrev altLift : Matrix (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k)
    (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) (LocRing p)[X] :=
  sLift (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
    ((altGeom c hc).geometry r).ys (hint_of_poleData (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp
      (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN))

/-- **The UF Smith datum with kills.** -/
noncomputable def altSmithJKDatum_UFK (TC TR : Finset (Fin ((altGeom c hc).geometry r).k))
    (hwC : ∀ t ∈ TC, wedgeC (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0)
    (hwR : ∀ t ∈ TR, wedgeR (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0)
    (hvR : ∀ t ∈ TR, vS7 p q o Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
      ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p) ≠ 0) :
    SmithJKDatum (altGeom c hc) Fr r p := by
  classical
  have hC := altGeom_C c hc r
  have hS : ∀ t, t0 ≤ t → t ≤ tmax →
      ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0)
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0 t := by
    intro t h1 h2
    obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
    exact alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
      (div_eq_of_between h1 h2 hdiv) (fun k hk1 hk2 => hw k hk1 (by omega))
  exact
  { N := N
    D := twoTermPoleData T hNp.le hsq hnorm hnorm0
    hN := hNp
    hc := alt_hc' c hc hrN
    hx := alt_hx' c hc hr hrN
    hy := alt_hy' c hc hr hrN
    hdist := alt_hdist c hc hr hp
    J := s7_twoTermK T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq _ _ _ (alt_hc' c hc hrN)
      (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) (alt_hdist c hc hr hp) t0
      (hB0_auto (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _ (alt_hc' c hc hrN)
        (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0N)
      (winRows c hc t0 tmax) (winCols c hc t0 tmax)
      (fun z hz => by
        simp only [winRows, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        exact hS _ hz.1 hz.2)
      (fun y hy => by
        simp only [winCols, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hS _ hy.1 hy.2) TC TR hwC hwR hvR }

/-- **Price of the UF datum with kills.** -/
theorem altSmithJKDatum_UFK_price (TC TR : Finset (Fin ((altGeom c hc).geometry r).k)) (hwC) (hwR)
    (hvR) (tv : ℕ) (htv0 : t0 ≤ tv) (htv : tv < r + p) (htvN : tv < N) (htvd : tv / p = t0 / p)
    (hwv : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) t0 (tv - t0))
    (δ₁ δ₂ : ℕ) (hδ12 : δ₁ ≤ δ₂) (hδ2 : δ₂ ≤ t0) (hlt : t0 - δ₁ < r) (hr3 : r ≤ t0 - δ₂ + p)
    (hqd : (t0 - δ₂) / p = t0 / p)
    (hwd : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) (t0 - δ₂) δ₂) :
    (altSmithJKDatum_UFK c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt htm hdiv
        hw TC TR hwC hwR hvR).price ≤
      2 * Fintype.card (((altGeom c hc).geometry r).C ⊕ Fin ((altGeom c hc).geometry r).k) -
        (Fintype.card (Fin ((altGeom c hc).geometry r).k) +
          (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) +
            (((winRows (r := r) c hc t0 tmax).card + (winCols (r := r) c hc t0 tmax).card -
              Fintype.card (Fin ((altGeom c hc).geometry r).k)) -
                (p - (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)).image
                    (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
                  ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
                    (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card)))) := by
  classical
  have hC := altGeom_C c hc r
  have hcount := card_retOf_sdiff_le (vS7 p q o Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
      (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0)
      ((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂) (t0 - δ₁)).image (fun t : ℕ => ((t : ℕ) : ZMod p)))
      ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) (by
    intro c' hc'
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
      obtain ⟨Δ, rfl⟩ : ∃ Δ, t = t0 + Δ := ⟨t - t0, by omega⟩
      exact vS7_zero T hNp.le hsq hnorm hnorm0 hNp hp2 ho hq _ _ _ (alt_hc' c hc hrN)
        (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 (t0 + Δ) (by omega)
        (alt_shiftData T hNp.le hsq hnorm hnorm0 _ hC t0 Δ hrt (by omega)
          (div_eq_of_between (by omega) ht2 htvd) (fun k hk1 hk2 => hwv k hk1 (by omega)))
    · obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 ht
      obtain ⟨δ, hδt, rfl⟩ : ∃ δ, δ ≤ t0 ∧ t = t0 - δ := ⟨t0 - t, by omega, by omega⟩
      refine vS7_topext T hNp.le hsq hnorm hnorm0 hNp ho hq _ hC _ _ (alt_hc' c hc hrN)
        (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 δ ht0N hrt (by omega) (by omega)
        (by omega) (by omega) ?_ ?_
      · exact le_antisymm (Nat.div_le_div_right (by omega)) (hqd ▸ Nat.div_le_div_right (by omega))
      · intro k hk1 hk2
        exact hwd k (by omega) (by omega))
  have eS : (altSmithJKDatum_UFK c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw TC TR hwC hwR hvR).J.sJ ≤ p - (((Finset.Icc t0 tv ∪ Finset.Icc (t0 - δ₂)
        (t0 - δ₁)).image (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
          ((TC.image fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
            (TR.image fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))).card :=
    hcount
  have eR : (altSmithJKDatum_UFK c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw TC TR hwC hwR hvR).J.Jr = winRows c hc t0 tmax := rfl
  have eC : (altSmithJKDatum_UFK c hc hr T hNp hsq hnorm hnorm0 hrN hp hp2 ho hq t0 tmax ht0N hrt
      htm hdiv hw TC TR hwC hwR hvR).J.Jc = winCols c hc t0 tmax := rfl
  unfold SmithJKDatum.price
  rw [eR, eC]
  omega

end

end CatalanCore.Uniform.Content.UFMoments
