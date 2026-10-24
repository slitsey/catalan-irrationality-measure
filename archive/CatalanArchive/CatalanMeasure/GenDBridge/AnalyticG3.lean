module

public import CatalanMeasure.GenD.Analytic.DeltaSmall
public import CatalanMeasure.GenD.D58.Final
public import CatalanArchive.CatalanMeasure.Parametric.GapSmallness

@[expose] public section

/-!
# Bridge (NOT part of `GenD`): group 3 of the generic analytic layer at P20 and at D58

This module imports `CatalanMeasure.GenD.Analytic.*` together with the old P20-pinned files, so it
must never be imported from `GenD`.  Contents:

* P20 parity of definitions (`sheetPrefactor`, `atomBaseBoundAt`, `atomColumnCost`,
  `realBaseMatrix`, `nodeAtomVectors/Weights` at `twenty` are the old ones);
* conversions `WeightedAtomPointOn <-> WeightedAtomPoint twenty`, `MarkedSheetBound twenty`;
* the OLD theorems `weighted_atom_point_on`, `weighted_atom_det_on`, `base_bound_on`,
  `perturbation_on` re-derived (same hypotheses and conclusions) from the generic ones;
* the shape check: the generic `delta_small` at `D58.Odd.design` has exactly the `delta_small`
  hypothesis of `D58.measure_592_of_certificates` / `measure_590_of_certificates`.
-/

namespace CatalanMeasure.GenD
namespace Analytic
namespace BridgeG3

open CatalanMeasure.Parametric OAI.InternalCatalan Filter Set Polynomial
open scoped Topology BigOperators

noncomputable section

theorem n0_twenty : ((twenty.n0 : ℕ) : ℝ) = 20 := by norm_num [twenty]

theorem sheetPrefactor_twenty (N : ℕ) :
    Analytic.sheetPrefactor twenty N = twentySheetPrefactor N := rfl

theorem atomBaseBoundAt_twenty (target : ℝ) (N : ℕ) (δ : ℝ) :
    Analytic.atomBaseBoundAt twenty target N δ = Parametric.atomBaseBoundAt target N δ := by
  unfold Analytic.atomBaseBoundAt Parametric.atomBaseBoundAt
  rw [n0_twenty]; rfl

theorem atomColumnCost_twenty (ρ : ℝ) (N : ℕ) :
    Analytic.atomColumnCost ρ N = twentyParametricAtomColumnCost ρ N := rfl

theorem realBaseMatrix_twenty (N : ℕ) :
    Analytic.realBaseMatrix twenty N = twentyRealBaseMatrix N := rfl

theorem nodeAtomVectors_twenty (τ : (N : ℕ) → Fin (18 * N) → ℝ) (N : ℕ) :
    Analytic.nodeAtomVectors twenty τ N = Parametric.nodeAtomVectors τ N := rfl

theorem nodeAtomWeights_twenty (τ : (N : ℕ) → Fin (18 * N) → ℝ) (N : ℕ) :
    Analytic.nodeAtomWeights twenty τ N = Parametric.nodeAtomWeights τ N := rfl

theorem pointToGen {τ : (N : ℕ) → Fin (18 * N) → ℝ} {G : ℝ → Prop} {target ρ : ℝ}
    (h : WeightedAtomPointOn τ G target ρ) : WeightedAtomPoint twenty τ G target ρ := by
  intro ε hε
  have := h ε hε
  rw [n0_twenty]
  exact this

theorem pointOfGen {τ : (N : ℕ) → Fin (18 * N) → ℝ} {G : ℝ → Prop} {target ρ : ℝ}
    (h : WeightedAtomPoint twenty τ G target ρ) : WeightedAtomPointOn τ G target ρ := by
  intro ε hε
  have := h ε hε
  rw [n0_twenty] at this
  exact this

theorem sheetBoundToGen {G : ℝ → Prop} {target r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      markedSheetProduct twenty N hpm x y s ≤
        (5 : ℝ) ^ m * twentySheetPrefactor N *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) + r * N * m)) :
    MarkedSheetBound twenty G target r := by
  intro ε hε
  have := h ε hε
  rw [n0_twenty]
  exact this

/-- The old `weighted_atom_point_on`, re-derived from the generic one. -/
theorem weighted_atom_point_on_via_generic {target c residual nearCap cost r w : ℝ}
    (F : FirstTrialBoundsAt target c) (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (D : SecondTrialBoundsOn target residual nearCap cost G) (hfc : 20*c ≤ r) (hsc : 20*cost ≤ r)
    (hweights : ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (a : Fin (18*N)),
      |(rowCommonFactor twenty N).eval (τ N a)| *
        |restrictedWeight twenty N k (τ N) a| ≤
          108000*(N : ℝ)*Real.exp (w*N)) : WeightedAtomPointOn τ G target (r+w) :=
  pointOfGen (weighted_atom_point_of_sheet twenty twenty_admissible τ G
    (sheetBoundToGen (fun _ hε => marked_sheet_on F G D hfc hsc hε)) hweights)

theorem weighted_atom_det_on_via_generic
    (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointOn τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ f : Fin (twenty.n N) → Option (Fin (18*N)),
      (∏ k, (f k).elim 1 (fun a => |Parametric.nodeAtomWeights τ N a k|)) *
        |(CatalanMeasure.atomMatrix (twentyRealBaseMatrix N) (Parametric.nodeAtomVectors τ N) f).det| ≤
      Parametric.atomBaseBoundAt target N ε *
        ∏ k, (f k).elim 1 (fun _ => twentyParametricAtomColumnCost ρ N) := by
  filter_upwards [weighted_atom_det twenty τ G hτinj hτmem hτzero hτG target ρ (pointToGen hpoint)
    hε] with N hN f
  have := hN f
  rw [atomBaseBoundAt_twenty] at this
  exact this

theorem base_bound_on_via_generic
    (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointOn τ G target ρ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop,|aeval catalan (Parametric.deltaPoly twenty N)| ≤
      Real.exp ((20*(N:ℝ))^2*(-target+Real.log 2/2+ε)) := by
  filter_upwards [base_bound twenty twenty_admissible τ G hτinj hτmem hτzero hτG target ρ
    (pointToGen hpoint) hε] with N hN
  rw [n0_twenty] at hN
  exact hN

theorem perturbation_on_via_generic
    (τ : (N : ℕ) → Fin (18*N) → ℝ) (G : ℝ → Prop)
    (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Set.Ioo (-1:ℝ) 1)
    (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i))) (target ρ : ℝ)
    (hpoint : WeightedAtomPointOn τ G target ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x-catalan| ≤ Real.exp (-(ρ*(N : ℝ))) →
      |aeval x (Parametric.deltaPoly twenty N)-aeval catalan (Parametric.deltaPoly twenty N)| ≤
        Real.exp ((20*(N : ℝ))^2*(-target+Real.log 2/2+ε)) := by
  filter_upwards [perturbation twenty twenty_admissible τ G hτinj hτmem hτzero hτG target ρ
    (pointToGen hpoint) hε] with N hN
  rw [n0_twenty] at hN
  exact hN

/-- Shape check, bank K160: the generic `delta_small` is the hypothesis of
`D58.measure_592_of_certificates`. -/
theorem delta_small_d58_160 {τ : (N : ℕ) → Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) → ℝ}
    {G : ℝ → Prop} (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1) (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i)))
    (hpoint : WeightedAtomPoint D58.Odd.design τ G D58.K160.target D58.K160.rho) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(D58.K160.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly D58.Odd.design N)| ≤
          Real.exp (-((D58.tDelta160 - ε) * (N : ℝ) ^ 2)) :=
  delta_small D58.Odd.design D58.Odd.design_admissible τ G hτinj hτmem hτzero hτG _ _ _
    (by unfold D58.tDelta160; norm_num [D58.Odd.design]; ring) hpoint

/-- Shape check, bank K640. -/
theorem delta_small_d58_640 {τ : (N : ℕ) → Fin ((D58.Odd.design.n0 - D58.Odd.design.g0) * N) → ℝ}
    {G : ℝ → Prop} (hτinj : ∀ N, Function.Injective (τ N))
    (hτmem : ∀ N i, τ N i ∈ Ioo (-1 : ℝ) 1) (hτzero : ∀ N i, τ N i ≠ 0)
    (hτG : ∀ N i, G (realCoordinate (τ N i)))
    (hpoint : WeightedAtomPoint D58.Odd.design τ G D58.K640.target D58.K640.rho) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      |x - catalan| ≤ Real.exp (-(D58.K640.rho * (N : ℝ))) →
        |aeval x (Parametric.deltaPoly D58.Odd.design N)| ≤
          Real.exp (-((D58.tDelta640 - ε) * (N : ℝ) ^ 2)) :=
  delta_small D58.Odd.design D58.Odd.design_admissible τ G hτinj hτmem hτzero hτG _ _ _
    (by unfold D58.tDelta640; norm_num [D58.Odd.design]; ring) hpoint

end

end BridgeG3
end Analytic
end CatalanMeasure.GenD
