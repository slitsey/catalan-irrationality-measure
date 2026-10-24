module
public import CatalanArchive.CatalanMeasure.G728.Budgets
public import CatalanArchive.CatalanMeasure.Parametric.GapActualWeights
public import CatalanArchive.CatalanMeasure.Parametric.GapFinalTransfer
@[expose] public section

/-!
# The 728 irrationality-measure bound, modulo the second-trial bounds

The second-trial data enters as the abstract hypothesis `D`; the first trial is the old
`FirstStrongTrial` retargeted to `target728`.
-/

namespace CatalanMeasure.G728
open CatalanMeasure.Parametric Polynomial Filter Real OAI.InternalCatalan
open scoped Topology
noncomputable section

/-- The statement of `CatalanMeasure.Parametric.u6_combined_content` (the combined secondary-tent,
U3 and U6 content), kept as a hypothesis here so that this module does not import the (very
heavy) U3/U6 content chain; `CatalanMeasure.Parametric.u6_combined_content` is a proof of it. -/
def U6Content : Prop :=
  ∃ c : ℕ → ℕ,
    (∀ N, 0 < c N) ∧
    (∀ N i, (c N : ℤ) ∣ (twentyMeasureIntPoly N).coeff i) ∧
    (∀ N q, q.Prime → N < q → q ≤ 2 * N → Nat.Coprime q (c N)) ∧
    (∀ᶠ N : ℕ in atTop,
      (507 / 2000 + 3331 / 10000 + 624 / 10000 : ℝ) * (N : ℝ) ^ 2 ≤ log (c N))

/-- Retarget a first trial (any trial for the old target with the same caps) to `target728`:
only the budget changes.  Applied to the old `FirstStrongTrial` trial `gapFirstTrial`. -/
def retarget728 (F : FirstTrialBoundsAt strongTarget strongFirstCost)
    (hn : F.normCap = strongNormFirst) (hf : F.fieldCap = strongFieldsFirst)
    (hl : F.lambda = strongLambda) : FirstTrialBoundsAt target728 strongFirstCost where
  p := F.p
  v := F.v
  lambda := F.lambda
  MX := F.MX
  MY := F.MY
  normCap := F.normCap
  fieldCap := F.fieldCap
  lambda_nonneg := F.lambda_nonneg
  p_summable := F.p_summable
  v_summable := F.v_summable
  norm_le := F.norm_le
  field_sum := F.field_sum
  row := F.row
  column := F.column
  budget := by
    intro a
    rw [hn, hf, hl]
    exact first_budget728 a

theorem gap_weight_bounds728 : GapWeightBounds :=
  Filter.Eventually.of_forall fun N k a => gap_actual_weight_joint_le N k a

/-- Weighted atom point at the new target and radius cost. -/
theorem atom_point728
    (F : FirstTrialBoundsAt target728 strongFirstCost)
    (D : SecondTrialBoundsOn target728 residual728 (-(3/4:ℝ)) secondCost728 gapAtomDomain) :
    WeightedAtomPointOn twentyGapNodes gapAtomDomain target728 rho728 := by
  rw [← payments728.2.1]
  exact weighted_atom_point_on F twentyGapNodes gapAtomDomain D
    payments728.1 le_rfl gap_weight_bounds728

theorem measure_728_of_bounds (hU : U6Content)
    (F : FirstTrialBoundsAt target728 strongFirstCost)
    (D : SecondTrialBoundsOn target728 residual728 (-(3/4:ℝ)) secondCost728 gapAtomDomain) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(728 : ℝ)) < |catalan - (a : ℝ) / b| := by
  obtain ⟨c, hc, hdiv, hcop, hgrowth⟩ := hU
  obtain ⟨hfc, hrho, hg, hr, hk, hd, hw, hl, hp, hrk, -⟩ := payments728
  rw [chi_eq728] at hgrowth
  have h := measure_of_content_on twentyGapNodes gapAtomDomain
    (fun N => (twenty_gap_nodes_properties N).1)
    (fun N i => ((twenty_gap_nodes_properties N).2 i).1) gap_nodes_nonzero
    (fun N i => ((twenty_gap_nodes_properties N).2 i).2) target728 c hc hdiv hcop
    (χ := chi728) (ρ := rho728) (η := eta728) (κ := kappa728) (δ := delta728)
    hgrowth (atom_point728 F D) eta_lt728 hg hr hk hd hw hl hp
  rwa [hrk] at h

end
end CatalanMeasure.G728
