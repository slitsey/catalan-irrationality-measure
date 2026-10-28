module

public import CatalanCore.Uniform.Content.UFMoments.S7TwoTerm

@[expose] public section

/-!
# (S7-Lean) for two-term frames: the `J`-block datum of a joint type (final assembly)

`s7_twoTerm`: two-term frame `Δ_t = 1/t - q/(qt - o)` with its `PoleData`, any core `c` and border
`xs, ys` below `N < p²` with distinct border residues, a representative border node `t₀` with
`B₀ = ᾱ_{t₀} ≠ 0`, and border rows `Jr` / columns `Jc` at nodes `t₀ + Δ` whose own chains are the
`Δ`-shifted chain of `t₀` (chain equivalence `e`, `c(e⁻¹ i) = c(i) + Δ`) with no singular index in
any window `(a, a + Δ]` (`a = t₀` or a chain node of `t₀`).  Then the `JBlockKill` datum of the
divided Schur complement exists, with `Ret = retOf (vS7 …)`,

  `vS7(c) = norm · (wT(c)/norm - C₀ - m(c))`,   `m(c) = fibMom (ℓ - d) c` (the `γ(c)/B²` of (S7)),

`wT` the cyclic step and `C₀` the normalisation making `vS7` vanish on the type.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The Loewner row of a node against the core. -/
noncomputable def loewRow (p : ℕ) [Fact p.Prime] (Fr : Frame) (c : ι → ℕ) (t : ℕ) :
    ι → (LocRing p)[X] :=
  fun a => Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t (c a)))

/-- Shift data of a node `t₀ + Δ` relative to `t₀`. -/
def ShiftData (D : PoleData Fr p N) (c : ι → ℕ) (t0 t : ℕ) : Prop :=
  ∃ Δ : ℕ, t = t0 + Δ ∧ NoSingWin D t0 Δ ∧
    ∃ e : {a // colOf (p := p) c a = ((t0 + Δ : ℕ) : ZMod p)} ≃
        {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)},
      (∀ i, c (e.symm i).1 = c i.1 + Δ) ∧
      (∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, NoSingWin D (c i.1) Δ)

/-- The normalised derived weight of (S7). -/
noncomputable def vS7 (p q o : ℕ) [Fact p.Prime] (Fr : Frame) (c : ι → ℕ)
    (Q : Matrix ι ι (LocRing p)[X]) (t0 : ℕ) : ZMod p → RatFunc (ZMod p) :=
  let d := dirOf Fr c Q t0 (loewRow p Fr c t0)
  let m := fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d)
  let n := (rfH p (red p Fr.norm))⁻¹
  vDer Fr c Q d (fun c' => rfH p (wT p q o c') * n -
    (rfH p (wT p q o ((t0 : ℕ) : ZMod p)) * n - m ((t0 : ℕ) : ZMod p)))

/-- **(S7-Lean) for two-term frames: the `J`-block datum.** -/
noncomputable def s7_twoTerm {q o : ℕ} (T : TwoTermData Fr q o) (hNle : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hN : N < p * p) (hp2 : p ≠ 2)
    (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (t0 : ℕ)
    (hB0 : res p (1 - ∑ j, (sOwn c t0 (loewRow p Fr c t0) ᵥ*
      (Dmat c (sLift c xs ys (hint_of_poleData (twoTermPoleData T hNle hsq hnorm hnorm0) hN hc hx
        hy)).toBlocks₁₁)⁻¹) j) ≠ 0)
    (Jr Jc : Finset κ)
    (hJr : ∀ z ∈ Jr, ShiftData (twoTermPoleData T hNle hsq hnorm hnorm0) c t0 (xs z))
    (hJc : ∀ y ∈ Jc, ShiftData (twoTermPoleData T hNle hsq hnorm hnorm0) c t0 (ys y)) :
    JBlockKill (schurW c xs ys
      (hint_of_poleData (twoTermPoleData T hNle hsq hnorm hnorm0) hN hc hx hy)) := by
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
  have hz := own_dir_zero Fr c A.toBlocks₁₁ t0 σ0 (isUnit_of_res_ne _ hB0)
  -- `TypeData` of a shifted node
  have hTD : ∀ (t : ℕ) (σ : ι → (LocRing p)[X]), t < N → ShiftData D c t0 t →
      (∀ a, σ a = Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t (c a)))) →
      TypeData Fr c A.toBlocks₁₁ t0 σ0 K0 W t σ := by
    intro t σ ht hS hσ
    obtain ⟨Δ, rfl, hwt, e, hce, hwc⟩ := hS
    refine typeData_of_shift D hN c xs ys hc hx hy hR t0 Δ σ0 σ (fun a => rfl) hσ e hce hwc hwt ht
      K0 W ?_
    rw [tt_hres T hNle hsq hnorm hnorm0 hp2 ho hq t0 Δ ht hwt]
    congr 1
    exact (sum_mul_inv_sub_const (rfH p) hp2 _ C0 _).symm
  -- the weight vanishes on the type
  have hv : ∀ (t : ℕ) (σ : ι → (LocRing p)[X]), t < N → ShiftData D c t0 t →
      TypeData Fr c A.toBlocks₁₁ t0 σ0 K0 W t σ →
      vDer Fr c A.toBlocks₁₁ d W ((t : ℕ) : ZMod p) = 0 := by
    intro t σ ht hS hT
    have hm := TypeData.fibMom_eq D c hc A.toBlocks₁₁ hQ hdet t0 σ0 K0 W t σ d hT
    obtain ⟨Δ, rfl, hwt, -⟩ := hS
    have hw := wT_window T hNle hsq hnorm hnorm0 ho hq t0 Δ ht hwt
    simp only [vDer, W, C0]
    rw [hw, hm]
    ring
  have hTr : ∀ z ∈ Jr, TypeData Fr c A.toBlocks₁₁ t0 σ0 K0 W (xs z)
      (fun a => A.toBlocks₂₁ z a) := fun z hz' =>
    hTD _ _ (hx z) (hJr z hz') (fun a => sLift_row_entry D hN c xs ys hc hx hy z a)
  have hTc : ∀ y ∈ Jc, TypeData Fr c A.toBlocks₁₁ t0 σ0 K0 W (ys y)
      (fun a => A.toBlocks₁₂ a y) := fun y hy' =>
    hTD _ _ (hy y) (hJc y hy') (fun a => sLift_col_entry D hN c xs ys hc hx hy a y)
  exact jblockKill_of_jtype D hN c xs ys hc hx hy hdist t0 σ0 d hz hB0 K0 W Jr Jc hTr hTc
    (fun z hz' => hv _ _ (hx z) (hJr z hz') (hTr z hz'))
    (fun y hy' => hv _ _ (hy y) (hJc y hy') (hTc y hy'))

end CatalanCore.Uniform.Content.UFMoments
