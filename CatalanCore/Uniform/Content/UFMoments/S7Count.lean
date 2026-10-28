module

public import CatalanCore.Uniform.Content.UFMoments.AltDatum

@[expose] public section

/-!
# (S7) counts: the derived weight vanishes on the whole transport window

`vS7_zero`: `vS7(t̄) = 0` for every node `t < N` (border node or not: a VIRTUAL node) that is a
shift of the representative (`ShiftData`).  Hence (`card_retOf_le`) the retained set has at most
`p - |T|` residues, `T` the residues of the transport window — the transport part (i) of
`I_J` in Theorem UF.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem vS7_zero {q o : ℕ} (T : TwoTermData Fr q o) (hNle : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hN : N < p * p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (t0 t : ℕ) (ht : t < N)
    (hS : ShiftData (twoTermPoleData T hNle hsq hnorm hnorm0) c t0 t) :
    vS7 p q o Fr c (sLift c xs ys (hint_of_poleData (twoTermPoleData T hNle hsq hnorm hnorm0)
      hN hc hx hy)).toBlocks₁₁ t0 ((t : ℕ) : ZMod p) = 0 := by
  classical
  set D := twoTermPoleData T hNle hsq hnorm hnorm0
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
  set σ0 := loewRow p Fr c t0
  set d := dirOf Fr c A.toBlocks₁₁ t0 σ0
  set m := fibMom c (Dmat c A.toBlocks₁₁) (fun a => ellL p Fr (c a) - d)
  set n := (rfH p (red p Fr.norm))⁻¹
  set C0 := rfH p (wT p q o ((t0 : ℕ) : ZMod p)) * n - m ((t0 : ℕ) : ZMod p)
  set W : ZMod p → RatFunc (ZMod p) := fun c' => rfH p (wT p q o c') * n - C0
  set K0 := -(rfH p (cauchyH (wT p q o) ((t0 : ℕ) : ZMod p))) * n
  have hR := tt_regRed (p := p) T hNle hsq hnorm hnorm0
  have hQ := sLift_core_rel D hN c xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)
  obtain ⟨Δ, rfl, hwt, e, hce, hwc⟩ := hS
  have hT : TypeData Fr c A.toBlocks₁₁ t0 σ0 K0 W (t0 + Δ) (loewRow p Fr c (t0 + Δ)) := by
    refine typeData_of_shift D hN c xs ys hc hx hy hR t0 Δ σ0 _ (fun a => rfl) (fun a => rfl) e
      hce hwc hwt ht K0 W ?_
    rw [tt_hres T hNle hsq hnorm hnorm0 hp2 ho hq t0 Δ ht hwt]
    congr 1
    exact (sum_mul_inv_sub_const (rfH p) hp2 _ C0 _).symm
  have hm := TypeData.fibMom_eq D c hc A.toBlocks₁₁ hQ hdet t0 σ0 K0 W _ _ d hT
  have hw := wT_window T hNle hsq hnorm hnorm0 ho hq t0 Δ ht hwt
  show vDer Fr c A.toBlocks₁₁ d W ((t0 + Δ : ℕ) : ZMod p) = 0
  simp only [vDer, W, C0]
  rw [hw, hm]
  ring

/-- **Retained-residue count.** -/
theorem card_retOf_le (v : ZMod p → RatFunc (ZMod p)) (Tset : Finset (ZMod p))
    (hv : ∀ c ∈ Tset, v c = 0) : (retOf v).card ≤ p - Tset.card := by
  classical
  have hsub : retOf v ⊆ univ \ Tset := by
    intro c hc'
    simp only [retOf, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun h => hc' (hv c h)
  have := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, ZMod.card] at this
  exact this

/-- The `J`-block of `s7_twoTerm`: rows, columns, retained set and count. -/
theorem s7_twoTerm_fields {q o : ℕ} (T : TwoTermData Fr q o) (hNle : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hN : N < p * p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (t0 : ℕ) (hB0) (Jr Jc : Finset κ)
    (hJr) (hJc) :
    let J := s7_twoTerm T hNle hsq hnorm hnorm0 hN hp2 ho hq c xs ys hc hx hy hdist t0 hB0 Jr Jc
      hJr hJc
    J.Jr = Jr ∧ J.Jc = Jc ∧
      J.sJ = (retOf (vS7 p q o Fr c (sLift c xs ys (hint_of_poleData
        (twoTermPoleData T hNle hsq hnorm hnorm0) hN hc hx hy)).toBlocks₁₁ t0)).card := by
  intro J
  refine ⟨rfl, rfl, ?_⟩
  show (J.Ret \ (J.KillR ∪ J.KillC)).card = _
  have h1 : J.KillR = ∅ := Finset.image_empty _
  have h2 : J.KillC = ∅ := Finset.image_empty _
  rw [h1, h2, Finset.union_empty, Finset.sdiff_empty]
  rfl

end CatalanCore.Uniform.Content.UFMoments
