module

public import CatalanMeasure.GenD.Analytic.Second
public import CatalanMeasure.GenD.Analytic.First
public import CatalanMeasure.Parametric.FlexibleSecondEnergy
public import CatalanMeasure.Parametric.FlexibleFirstEnergy
public import CatalanMeasure.G728.Glue
public import CatalanMeasure.GenD.Analytic.Glue
public import CatalanMeasure.GenD.Analytic.GroupedProduct
public import CatalanMeasure.Parametric.FlexibleGroupedProduct
public import CatalanMeasure.Parametric.TwentyGroupedPhysicalFields
public import CatalanMeasure.Parametric.TwentyPhysicalConstants
public import CatalanMeasure.Parametric.TwentyGroupedConstants

@[expose] public section

/-!
# Bridge (NOT part of `GenD`): the generic analytic layer at P20 reproduces the old layer

This module imports both `CatalanMeasure.GenD.Analytic.*` and the old P20-pinned files, so it must
never be imported from `GenD`.  It records the P20 parity of the exported statements:

* constants: `gRes twenty = 9/10`, `gKappa twenty = 3/10`, `gC0 twenty = 1/5`, `gC1 twenty = 8/5`;
* definitions: `groupedConstant`, `groupedMarkedField`, `groupedNearField` at `twenty` are the old
  `groupedPhysical*` (by `rfl`);
* `grouped_constant_le` / `physical_one_constant_le` at `twenty` are the old
  `twenty_grouped_constant_le` / `twenty_physical_one_constant_le`;
* `grouped_marked_field_identity` / `firstDampingError` at `twenty` are the old identity / error;
* `SecondTrialBoundsOn` and `FirstTrialBoundsAt` convert to the generic structures at `twenty`
  (`secondToGen`, `firstToGen`), and the old `second_energy_on`, `first_energy_with_trial` are re-derived from
  `second_energy`, `first_energy`.
-/

namespace CatalanMeasure.GenD
namespace Analytic
namespace Bridge

open CatalanMeasure.Parametric CatalanMeasure.Cert CatalanMeasure.G728 OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

theorem gRes_twenty : gRes twenty = 9 / 10 := by
  unfold gRes twenty; norm_num

theorem gKappa_twenty : gKappa twenty = 3 / 10 := by
  unfold gKappa twenty; norm_num

theorem gC0_twenty : gC0 twenty = 1 / 5 := by
  unfold gC0; rw [gKappa_twenty]; norm_num

theorem gC1_twenty : gC1 twenty = 8 / 5 := by
  unfold gC1; rw [gKappa_twenty, gRes_twenty]; norm_num

theorem groupedConstant_twenty : groupedConstant twenty = groupedPhysicalConstant twenty := rfl

theorem groupedMarkedField_twenty : groupedMarkedField twenty = groupedPhysicalMarkedField twenty :=
  rfl

theorem groupedNearField_twenty : groupedNearField twenty = groupedPhysicalNearField twenty := rfl

/-- The old `twenty_grouped_constant_le` is the generic `grouped_constant_le` at `twenty`. -/
theorem grouped_constant_le_twenty {N r a b : ℕ} (hN : 0 < N)
    (hcount : r + a + b = twenty.n N) :
    groupedPhysicalConstant twenty N r a b -
        (1 / 2 : ℝ) * ((((r + a : ℕ) : ℝ) / (twenty.n N : ℝ)) ^ 2 +
          ((b : ℝ) / (twenty.n N : ℝ)) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / (twenty.n N : ℝ)) ^ 2 * Real.log 2 ≤
      (-(1 / 5 : ℝ) + (8 / 5) * (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) -
        (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) ^ 2 +
        (b : ℝ) / (twenty.n N : ℝ) - ((b : ℝ) / (twenty.n N : ℝ)) ^ 2) * Real.log 2 := by
  have h := grouped_constant_le twenty_admissible hN hcount
  rw [gC0_twenty, gC1_twenty] at h
  exact h

/-- The old `twenty_physical_one_constant_le` is the generic `physical_one_constant_le`. -/
theorem physical_one_constant_le_twenty {N p m : ℕ} (hN : 0 < N) (hpm : p + m = twenty.n N) :
    populationPhysicalOneConstant twenty N p -
        (3 / 2 : ℝ) * ((p : ℝ) / (twenty.n N : ℝ)) ^ 2 * Real.log 2 ≤
      -(1 / 5 : ℝ) * Real.log 2 +
        (2 * ((m : ℝ) / (twenty.n N : ℝ)) - ((m : ℝ) / (twenty.n N : ℝ)) ^ 2) * Real.log 2 := by
  have h := physical_one_constant_le twenty_admissible hN hpm
  rw [gC0_twenty] at h
  linarith only [h]

/-- The old marked-field identity is the generic one at `twenty`. -/
theorem grouped_marked_field_identity_twenty {N : ℕ} (hN : 0 < N) (x : ℝ) :
    groupedPhysicalMarkedField twenty N x =
      -(9 / 10 : ℝ) * Real.log (1 + x ^ 2) + Real.log (1 + x ^ 2) / (twenty.n N : ℝ) := by
  have h := grouped_marked_field_identity twenty_admissible hN x
  rw [gRes_twenty] at h
  exact h

/-- Old second-population contract to the generic one. -/
def secondToGen {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsOn target residual nearCap cost G) :
    SecondTrialBounds twenty target residual nearCap cost G where
  p := D.p
  v := D.v
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  marked := D.marked
  near := D.near
  budget := by
    intro a t ha ht
    have h := D.budget ha ht
    rw [gC0_twenty, gC1_twenty]
    linarith only [h]

/-- The old `second_energy_on`, re-derived from the generic `second_energy`. -/
theorem second_energy_on_via_generic {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsOn target residual nearCap cost G) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = twenty.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedValueWithFields (twenty.n N : ℝ) (groupedPhysicalConstant twenty N r a b)
        (populationPhysicalFreeField twenty N) (groupedPhysicalMarkedField twenty N)
        (groupedPhysicalNearField twenty N) (populationPhysicalColumnField twenty N (a + b))
        z x y s ≤ -target + Real.log 2 / 2 +
          cost * (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) + δ :=
  second_energy twenty_admissible (secondToGen D) hδ

/-- Old first-population contract to the generic one. -/
def firstToGen {target cost : ℝ} (D : FirstTrialBoundsAt target cost) :
    FirstTrialBounds twenty target cost where
  p := D.p
  v := D.v
  lambda := D.lambda
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  lambda_nonneg := D.lambda_nonneg
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  budget := by
    intro a
    have h := D.budget a
    rw [gC0_twenty, gC1_twenty]
    have hg : ((twenty.g0 : ℕ) : ℝ) / (twenty.n0 : ℕ) = 1 / 10 := by
      unfold twenty; norm_num
    rw [hg]
    linarith only [h]

/-- The old `first_energy_with_trial`, re-derived from the generic `first_energy`. -/
theorem first_energy_with_trial_via_generic {target c : ℝ} (D : FirstTrialBoundsAt target c)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ), p + m = twenty.n N →
      ∀ (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) →
      (∀ j, s j ∈ Ioo (0 : ℝ) 1) → Function.Injective x → Function.Injective s →
      (-(1 : ℝ) < ∑ i : Fin (p + m), paramCaseField twenty N (Fin.append x y i)) →
      weightedPopulationOneValue twenty N (((m : ℝ) / (twenty.n N : ℝ))) x y s ≤
        -target + Real.log 2 / 2 + c * ((m : ℝ) / (twenty.n N : ℝ)) + δ :=
  first_energy twenty_admissible (firstToGen D) hδ


/-- Generic second-population contract at `twenty` back to the old one. -/
def secondOfGen {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds twenty target residual nearCap cost G) :
    SecondTrialBoundsOn target residual nearCap cost G where
  p := D.p
  v := D.v
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  marked := D.marked
  near := D.near
  budget := by
    intro a t ha ht
    have h := D.budget ha ht
    rw [gC0_twenty, gC1_twenty] at h
    linarith only [h]

/-- The near-field cap of the old glue is the generic `near_sup` at `twenty`. -/
theorem near_sup_twenty {p : ℝ} (hp : (9 / 50 : ℝ) ≤ p) :
    ∀ y ∈ Ioo (0 : ℝ) 1,
      -gRes twenty * Real.log (1 + y ^ 2) +
        (((twenty.n0 : ℝ) - 2 * twenty.g0 - 1) / twenty.n0) * Real.log y - p * y ≤ -(3 / 4 : ℝ) := by
  intro y hy
  have h := near_residual_field_le_three_fourths hp hy.1 hy.2.le
  have hθ : (((twenty.n0 : ℝ) - 2 * twenty.g0 - 1) / twenty.n0) = 3 / 4 := by
    unfold twenty; norm_num
  rw [gRes_twenty, hθ]
  exact h

/-- The old `secondTrialOfFieldsS`, re-derived from the generic `secondTrial_of_fields`
(same hypotheses, same conclusion). -/
def secondTrialOfFieldsS_via_generic {target residual cost normCap fieldCap : ℝ} {G : ℝ → Prop}
    (Pc Vc : List ℤ) (P V : List TailQ) (hP : tailsInDisk P = true) (hV : tailsInDisk V = true)
    (R : RowWeights) (hR : R = ⟨2 / 5, 1 / 10, 27 / 20, 0, 1 / 5⟩)
    (C : ColumnWeights) (hC : C = ⟨3 / 20, 1 / 20, 0⟩) (MX MY : ℝ)
    (first_lower : (9 / 50 : ℝ) ≤ trialSeqS Pc P 1)
    (norm_le : 2 * barrierTrialNormSq (trialSeqS Pc P) + barrierTrialNormSq (trialSeqS Vc V) / 2 ≤
      normCap)
    (field_sum : MX + MY = fieldCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1, rowFieldS R Pc Vc P V x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldS C Vc V s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldS Pc P x ≤ residual)
    (budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-(1 / 5 : ℝ) + (8 / 5) * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
        (a - t) * residual + t * (-(3 / 4 : ℝ)) + (9 / 10) * a ≤
          -target + Real.log 2 / 2 + (cost + 9 / 10) * a) :
    SecondTrialBoundsOn target residual (-(3 / 4 : ℝ)) cost G :=
  secondOfGen
    (secondTrial_of_fields (P := twenty) twenty_admissible (trialSeqS Pc P) (trialSeqS Vc V)
      (trialSeqS_summable hP).1 (trialSeqS_summable hV).1
      (R.alpha : ℝ) (R.beta : ℝ) (R.gamma : ℝ) (C.b : ℝ) (C.q : ℝ)
      (by subst hR; unfold twenty; norm_num) (by subst hR; unfold twenty; norm_num)
      (by subst hR; unfold twenty; norm_num) (by subst hC; unfold twenty; norm_num)
      (by subst hC; unfold twenty; norm_num) MX MY (-(3 / 4 : ℝ))
      (near_sup_twenty first_lower) norm_le field_sum row_sup column_sup
      (fun x hx hg => by
        have h := residual_sup x hx hg
        unfold resFieldS resFieldG at h
        unfold resFieldGen
        rw [gRes_twenty]
        exact h)
      (fun {a t} ha ht => by
        rw [gC0_twenty, gC1_twenty]
        have h := budget ha ht
        linarith only [h]))


theorem groupedProduct_twenty : groupedProduct twenty = groupedPhysicalProduct twenty := rfl

/-- The old `grouped_marked_product_on`, re-derived from the generic `grouped_marked_product`. -/
theorem grouped_marked_product_on_via_generic {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsOn target residual nearCap cost G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (r a b : ℕ), r + a + b = twenty.n N →
      ∀ (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ),
      (∀ i, z i ∈ Ioo (-1 : ℝ) 1) → (∀ i, z i ≠ 0) →
      (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, G (x i)) → (∀ i, y i ∈ Ioo (0 : ℝ) 1) →
      (∀ i, s i ∈ Ioo (0 : ℝ) 1) → Function.Injective z →
      Function.Injective (Fin.append z x) → Function.Injective y → Function.Injective s →
      groupedPhysicalProduct twenty N z x y s ≤
        Real.exp ((20 * (N : ℝ)) ^ 2 * (-target + Real.log 2 / 2 + ε) +
          (20 * cost) * N * (a + b)) := by
  have h := grouped_marked_product twenty_admissible (secondToGen D) hε
  have h20 : ((twenty.n0 : ℕ) : ℝ) = 20 := by simp [twenty]
  rw [h20] at h
  exact h

end
end Bridge
end Analytic
end CatalanMeasure.GenD
