module

public import CatalanCore.Uniform.Content.UFMoments.JBlockUF

@[expose] public section

/-!
# The `J`-block datum WITH wedge kills

Outside border columns `t ∈ TC` (rows `t ∈ TR`) whose first-layer wedge with the direction of `J`
is nonzero kill their residue (Theorem UF: occupied outside border residues).  In `GaussLoc p` the
wedge is the residue

  `wedgeC t = res(β¹'_t) - res(u d) res(α'_t)`,  `wedgeR t = (res(α_t) res(u d) - res(β¹_t)) / res(det Q)`,

with `β = π β¹` (`colMomB_eq`, `rowMomB_eq`).  `jblockKill_of_jtypeK` is `jblockKill_of_jtype` with
these kills (`hwC`, `hwR`: the wedges are nonzero; `hvR`: `v ≠ 0` at killed row residues).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- `β'_t / π` for a border column. -/
noncomputable def colMomB1 (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (ys : κ → ℕ) (t : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det * PF1 p Fr (ys t) -
    ∑ j, (∑ k, PF1 p Fr (c k) * A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j t

/-- `β_t / π` for a border row. -/
noncomputable def rowMomB1 (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (xs : κ → ℕ) (t : κ) : (LocRing p)[X] :=
  A.toBlocks₁₁.det * PF1 p Fr (xs t) -
    ∑ i, A.toBlocks₂₁ t i * ∑ k, A.toBlocks₁₁.adjugate i k * PF1 p Fr (c k)

/-- The column wedge with the direction `u d`. -/
noncomputable def wedgeC (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (ys : κ → ℕ) (d : GaussLoc p) (t : κ) : RatFunc (ZMod p) :=
  phiP p (colMomB1 A Fr c ys t) -
    res p (algebraMap _ (GaussLoc p) (nL p Fr) * d) * phiP p (colMomA A t)

/-- The row wedge with the direction `u d`. -/
noncomputable def wedgeR (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (xs : κ → ℕ) (d : GaussLoc p) (t : κ) : RatFunc (ZMod p) :=
  (phiP p (rowMomA A t) * res p (algebraMap _ (GaussLoc p) (nL p Fr) * d) -
    phiP p (rowMomB1 A Fr c xs t)) / phiP p A.toBlocks₁₁.det

/-- **The `J`-block datum with kills.** -/
noncomputable def jblockKill_of_jtypeK (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
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
      ((ys y : ℕ) : ZMod p) = 0)
    (TC TR : Finset κ)
    (hwC : ∀ t ∈ TC, wedgeC (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c ys d t ≠ 0)
    (hwR : ∀ t ∈ TR, wedgeR (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs d t ≠ 0)
    (hvR : ∀ t ∈ TR, vDer Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ d W
      ((xs t : ℕ) : ZMod p) ≠ 0) :
    JBlockKill (schurW c xs ys (hint_of_poleData D hN hc hx hy)) := by
  classical
  set A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
  set v := vDer Fr c A.toBlocks₁₁ d W
  set f := algebraMap (LocRing p)[X] (GaussLoc p)
  have h := hnum_jtype D hN c xs ys hc hx hy t0 σ0 d hz hB0 K0 W Jr Jc hTr hTc
  have hQ := sLift_core_rel D hN c xs ys hc hx hy
  have hdet := sLift_core_det (Fr := Fr) c xs ys (hint_of_poleData D hN hc hx hy)
  have hrow : ∀ z ∈ Jr, ∃ Φ : GaussLoc p,
      f (rowMomB A Fr c xs z) = f (rowMomA A z) *
        (piL p * (f (nL p Fr) * d) + piL p ^ 2 * Φ) := fun z hz' =>
    (jtype_node_hDer D c hc A.toBlocks₁₁ hQ hdet t0 σ0 d hz hB0 K0 W (xs z) (hx z) _
      (sLift_row_rel D hN c xs ys hc hx hy z) _ _ (sLift_rowA D hN c xs ys hc hx hy z)
      (sLift_rowB D hN c xs ys hc hx hy z) (hTr z hz')).imp fun _ h => h.1
  have hcol : ∀ y ∈ Jc, ∃ Φ : GaussLoc p,
      f (colMomB A Fr c ys y) = f (colMomA A y) *
        (piL p * (f (nL p Fr) * d) + piL p ^ 2 * Φ) := fun y hy' =>
    (jtype_node_hDer D c hc A.toBlocks₁₁ hQ hdet t0 σ0 d hz hB0 K0 W (ys y) (hy y) _
      (sLift_col_rel D hN c xs ys hc hx hy y) _ _ (sLift_colA D hN c xs ys hc hx hy y)
      (sLift_colB D hN c xs ys hc hx hy y) (hTc y hy')).imp fun _ h => h.1
  have hcB : ∀ t, colMomB A Fr c ys t = Polynomial.C ((p : ℕ) : LocRing p) * colMomB1 A Fr c ys t :=
    fun t => colMomB_eq D A c ys hc hy t
  have hrB : ∀ t, rowMomB A Fr c xs t = Polynomial.C ((p : ℕ) : LocRing p) * rowMomB1 A Fr c xs t :=
    fun t => rowMomB_eq D A c xs hc hx t
  refine JBlockKill.of_moments D hN c xs ys hc hx hy hdist Jr Jc (retOf v) v
    (fun z => phiP p (rowMomA A z) / phiP p A.toBlocks₁₁.det) (fun y => phiP p (colMomA A y))
    ?_ ?_ ?_ TC (wedgeC A Fr c ys d) hwC ?_ TR (fun t => wedgeR A Fr c xs d t) hwR hvR ?_
  · intro z hz' y hy'
    obtain ⟨q, hq1, hq2⟩ := h z hz' y hy'
    refine ⟨q, hq1, ?_⟩
    rw [hq2, hDer_retOf, hDer_retOf]
  · intro z hz' c' _ hv hc'
    exact hv (by rw [hc']; exact hvr z hz')
  · intro y hy' c' _ hv hc'
    exact hv (by rw [hc']; exact hvc y hy')
  · intro t _ z hz'
    obtain ⟨Φ, hΦ⟩ := hrow z hz'
    have hloc : f (dispNum A Fr c xs ys z t) = piL p ^ 1 * (f (rowMomA A z) *
        (f (colMomB1 A Fr c ys t) - (f (nL p Fr) * d + piL p * Φ) * f (colMomA A t))) := by
      rw [dispNum_eq_moments, map_sub, map_mul, map_mul, hΦ, hcB t, map_mul]
      ring
    obtain ⟨q, hq1, hq2⟩ := dvd_of_local p _ 1 _ hloc
    refine ⟨q, by rw [hq1, pow_one], ?_⟩
    rw [hq2]
    have hd0 : phiP p A.toBlocks₁₁.det ≠ 0 := hdet
    have hpz : phiP p (Polynomial.C ((p : ℕ) : LocRing p)) = 0 := (phiP_eq_zero_iff p _).2 dvd_rfl
    simp only [f, A, hpz, zero_mul, mul_zero, map_mul, map_sub, map_add, res_algebraMap, res_piL, zero_mul, add_zero]
    unfold wedgeC
    rw [map_mul, res_algebraMap]
    field_simp
  · intro t _ y hy'
    obtain ⟨Φ, hΦ⟩ := hcol y hy'
    have hloc : f (dispNum A Fr c xs ys t y) = piL p ^ 1 * (f (colMomA A y) *
        (f (rowMomA A t) * (f (nL p Fr) * d + piL p * Φ) - f (rowMomB1 A Fr c xs t))) := by
      rw [dispNum_eq_moments, map_sub, map_mul, map_mul, hΦ, hrB t, map_mul]
      ring
    obtain ⟨q, hq1, hq2⟩ := dvd_of_local p _ 1 _ hloc
    refine ⟨q, by rw [hq1, pow_one], ?_⟩
    rw [hq2]
    have hd0 : phiP p A.toBlocks₁₁.det ≠ 0 := hdet
    have hpz : phiP p (Polynomial.C ((p : ℕ) : LocRing p)) = 0 := (phiP_eq_zero_iff p _).2 dvd_rfl
    simp only [f, A, hpz, zero_mul, mul_zero, map_mul, map_sub, map_add, res_algebraMap, res_piL, zero_mul, add_zero]
    unfold wedgeR
    rw [map_mul, res_algebraMap]
    field_simp

end CatalanCore.Uniform.Content.UFMoments
