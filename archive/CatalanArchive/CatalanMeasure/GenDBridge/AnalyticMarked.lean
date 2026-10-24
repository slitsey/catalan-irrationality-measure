module

public import CatalanMeasure.GenD.Analytic.MarkedSheetOn
public import CatalanMeasure.GenD.Analytic.MarkedMixedMajorant
public import CatalanMeasure.GenD.Analytic.FullInterval
public import CatalanArchive.CatalanMeasure.GenDBridge.Analytic
public import CatalanArchive.CatalanMeasure.Parametric.GapAtomCost
public import CatalanArchive.CatalanMeasure.Parametric.MarkedAtomsDegeneracy
public import CatalanMeasure.Parametric.FullIntervalFormula
public import CatalanArchive.CatalanMeasure.Parametric.TwentyMarkedSecondProduct
public import CatalanArchive.CatalanMeasure.Parametric.TwentyWeightedIntegrand

@[expose] public section

/-!
# Bridge (NOT part of `GenD`): the generic marked-sheet chain at P20 reproduces the old one

Imports both `CatalanMeasure.GenD.Analytic.Marked*` and the old P20-pinned files; never to be
imported from `GenD`.  Definitions agree by `rfl` (`markedSheetProduct`, `firstMarkedProduct`,
`sheetPrefactor`); the old theorems `marked_sheet_on`, `second_marked_sheet_product_on`,
`first_marked_sheet_with_trial`, `original_poly_atoms_mixedDouble_mul_weight_le`,
`marked_sheet_weight_cancellation`, `twenty_full_weight_formula` are re-derived (same statement
text) from the generic ones.
-/

namespace CatalanMeasure.GenD
namespace Analytic
namespace Bridge

open CatalanMeasure.Parametric OAI.InternalCatalan Filter Set Finset
open scoped Topology BigOperators

noncomputable section

private theorem n0_twenty : ((twenty.n0 : ℕ) : ℝ) = 20 := by simp [twenty]

theorem markedSheetProduct_twenty {N p m : ℕ} (hpm : p + m = twenty.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    Analytic.markedSheetProduct twenty N hpm x y s =
      CatalanMeasure.Parametric.markedSheetProduct twenty N hpm x y s := rfl

theorem firstMarkedProduct_twenty {N p m : ℕ} (hpm : p + m = twenty.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) :
    Analytic.firstMarkedProduct twenty N hpm x y s =
      CatalanMeasure.Parametric.firstMarkedProduct twenty N hpm x y s := rfl

theorem sheetPrefactor_twenty (N : ℕ) :
    Analytic.sheetPrefactor twenty N = twentySheetPrefactor N := rfl

theorem markedSheetWeight_twenty (N : ℕ) (x : ℝ) :
    Analytic.markedSheetWeight twenty N x =
      CatalanMeasure.Parametric.markedSheetWeight twenty N x := rfl

theorem originalPolyAtoms_twenty {N p m : ℕ} (y : Fin m → ℝ) :
    Analytic.originalPolyAtoms (p := p) twenty N y =
      CatalanMeasure.Parametric.originalPolyAtoms twenty N y := rfl

/-- Old `marked_sheet_weight_cancellation`, from the generic one. -/
theorem marked_sheet_weight_cancellation_via_generic {P : Parameters} (hP : Admissible P)
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) (hx0 : x ≠ 0) :
    |x| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) * paramRowNodeWeight P N x =
      |(rowCommonFactor P N).eval (realCoordinateInv x)| *
        CatalanMeasure.Parametric.markedSheetWeight P N x :=
  Analytic.marked_sheet_weight_cancellation hP hN hx hx0

/-- Old `twenty_full_weight_formula`, from the generic `full_weight_formula`. -/
theorem twenty_full_weight_formula_via_generic {N r : ℕ} (hN : 0 < N) (hr : r < twenty.n N)
    (k : ℕ) :
    (filteredCatalanCoeffRat twenty N r k : ℝ) =
      ∑ a : Fin (18 * N), (realPoly (rowP twenty N r)).eval (CatalanMeasure.chebX (18 * N) a) *
        restrictedWeight twenty N k (CatalanMeasure.chebX (18 * N)) a :=
  Analytic.full_weight_formula twenty_admissible hN hr
    (by simp [Parameters.n, Parameters.g, twenty]; omega) ⟨9 * N, by omega⟩ k

/-- Old `first_marked_sheet_with_trial`, from the generic `first_marked_sheet`. -/
theorem first_marked_sheet_with_trial_via_generic {target c : ℝ}
    (F : FirstTrialBoundsAt target c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-1 < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      CatalanMeasure.Parametric.markedSheetProduct twenty N hpm x y s ≤
        ((3 / 2 : ℝ) ^ twenty.n N * (twenty.n N : ℝ) ^ ((twenty.n N : ℝ) / 2)) *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            (20 * c) * N * m) := by
  have h := Analytic.first_marked_sheet twenty_admissible (firstToGen F) hε
  rw [n0_twenty] at h
  exact h

/-- Old `second_marked_sheet_product_on`, from the generic one. -/
theorem second_marked_sheet_product_on_via_generic (target cost : ℝ) (G : ℝ → Prop)
    (hgrouped : CatalanMeasure.Parametric.GroupedMarkedProductCostOn target cost G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) →
      Function.Injective s →
      ((∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) ≤ -1) →
      CatalanMeasure.Parametric.markedSheetProduct twenty N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (twenty.n N : ℝ)) ^ twenty.n N *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            cost * N * m) := by
  have hg : Analytic.GroupedMarkedProductCostOn twenty target cost G := by
    intro ε hε
    filter_upwards [hgrouped ε hε] with N he
    intro r a b hc z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
    have h := he r a b hc z x y s hz hz0 hx hxG hy hs hzi hxi hyi hsi
    rw [n0_twenty]
    exact h
  have h := Analytic.second_marked_sheet_product_on twenty_admissible target cost G hg hε
  rw [n0_twenty] at h
  exact h

/-- Old `marked_sheet_on`, from the generic one. -/
theorem marked_sheet_on_via_generic {target c residual nearCap cost r : ℝ}
    (F : FirstTrialBoundsAt target c) (G : ℝ → Prop)
    (D : SecondTrialBoundsOn target residual nearCap cost G) (hfc : 20*c ≤ r) (hsc : 20*cost ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = twenty.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective (Fin.append x y) → Function.Injective s →
      CatalanMeasure.Parametric.markedSheetProduct twenty N hpm x y s ≤
        (5 : ℝ) ^ m * twentySheetPrefactor N *
          Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
            r * N * m) := by
  have h := Analytic.marked_sheet_on (r := r) twenty_admissible (firstToGen F) G (secondToGen D)
    (by rw [n0_twenty]; exact hfc) (by rw [n0_twenty]; exact hsc) hε
  rw [n0_twenty] at h
  exact h

/-- Old `original_poly_atoms_mixedDouble_mul_weight_le`, from the generic one. -/
theorem original_poly_atoms_mixedDouble_mul_weight_le_via_generic {P : Parameters}
    (hP : Admissible P)
    {N p m : ℕ} (hN : 0 < N) (hpm : p + m = P.n N)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) (β : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ j, s j ∈ Ioo (0 : ℝ) 1) {Q : ℝ}
    (hweight : ∀ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| * |β j| ≤ Q) :
    |CatalanMeasure.mixedDoubleWithAtoms (paramPinRowFun P N)
      (CatalanMeasure.Parametric.originalPolyAtoms P N y)
      (paramPinColFun P N E) paramPinKernel (realCoordinateInv ∘ x) s| * (∏ j, |β j|) ≤
      CatalanMeasure.Parametric.markedSheetProduct P N hpm x y s * Q ^ m :=
  Analytic.original_poly_atoms_mixedDouble_mul_weight_le hP hN hpm E hE hEn x y s β
    hx hx0 hy hy0 hs hweight

end
end Bridge
end Analytic
end CatalanMeasure.GenD
