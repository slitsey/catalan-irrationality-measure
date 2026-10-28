module

public import CatalanCore.Uniform.Content.UFMoments.JHnum

@[expose] public section

/-!
# UF moments: the `J`-block datum of the Smith layer from (S7-Lean)

`jblockKill_of_jtype`: from the joint-type data of `hnum_jtype` and the vanishing of the derived
weight `v = vDer` at the residues of the `J` nodes, the `JBlockKill` datum (no kills) of the divided
Schur complement, with retained set `Ret = {c : v(c) ≠ 0}` (`retOf`).  Its retained count is
`|Ret|` (`jblockKill_of_jtype_sJ`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The retained residues of a derived weight. -/
noncomputable def retOf (v : ZMod p → RatFunc (ZMod p)) : Finset (ZMod p) := by
  classical exact univ.filter fun c => v c ≠ 0

theorem hDer_retOf (v : ZMod p → RatFunc (ZMod p)) (t : ZMod p) :
    hDer univ v t = hDer (retOf v) v t := by
  classical
  unfold hDer retOf
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : v c = 0
  · simp [h]
  · simp [h]

/-- **The `J`-block datum from (S7-Lean).** -/
noncomputable def jblockKill_of_jtype (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hz : (ellL p Fr t0 - d) - (sOwn c t0 σ0 ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁)⁻¹) ⬝ᵥ
        (fun a => ellL p Fr (c a) - d) = 0)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 σ0 ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁)⁻¹) j) ≠ 0)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p)) (Jr Jc : Finset κ)
    (hTr : ∀ z ∈ Jr, TypeData Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      t0 σ0 K0 W (xs z) (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a))
    (hTc : ∀ y ∈ Jc, TypeData Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      t0 σ0 K0 W (ys y) (fun a => (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y))
    (hvr : ∀ z ∈ Jr, vDer Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ d W
      ((xs z : ℕ) : ZMod p) = 0)
    (hvc : ∀ y ∈ Jc, vDer Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ d W
      ((ys y : ℕ) : ZMod p) = 0) :
    JBlockKill (schurW c xs ys (hint_of_poleData D hN hc hx hy)) := by
  classical
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
  set v := vDer Fr c A.toBlocks₁₁ d W
  have h := hnum_jtype D hN c xs ys hc hx hy t0 σ0 d hz hB0 K0 W Jr Jc hTr hTc
  refine JBlockKill.of_moments D hN c xs ys hc hx hy hdist Jr Jc (retOf v) v
    (fun z => phiP p (rowMomA A z) / phiP p A.toBlocks₁₁.det) (fun y => phiP p (colMomA A y))
    ?_ ?_ ?_ ∅ (fun _ => 1) (by simp) (by simp) ∅ (fun _ => 1) (by simp) (by simp) (by simp)
  · intro z hz' y hy'
    obtain ⟨q, hq1, hq2⟩ := h z hz' y hy'
    refine ⟨q, hq1, ?_⟩
    rw [hq2, hDer_retOf, hDer_retOf]
  · intro z hz' c' _ hv hc'
    exact hv (by rw [hc']; exact hvr z hz')
  · intro y hy' c' _ hv hc'
    exact hv (by rw [hc']; exact hvc y hy')

end CatalanCore.Uniform.Content.UFMoments
