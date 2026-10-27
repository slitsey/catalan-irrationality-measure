module
public import CatalanMeasure.GenD.Uniform.Bank.Budget532
public import CatalanMeasure.GenD.Uniform.Bank.TrialFields
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

/-! Feasible-trial qualification at the corrected D58 constraints. The old
witness remains valid because its actual coefficients, first coefficient, norm,
three field covers, and gap circle are proved independently of the denominator
gain. No claim is made that these coefficients equal the corrected optimizer's
minimizer. All analytic costs are those of the existing weaker envelope. -/
namespace CatalanMeasure.GenD.Uniform.Bank532
open D58 Analytic Filter Set Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.CellCert
noncomputable section

/-- The exact corrected-generator constraint u₁ ≥ 9/50, for the actual stored
second witness, including every complex tail contribution. -/
theorem corrected_u1 : (9 / 50 : ℝ) ≤ secondU590 1 := Cert590.first_lower

theorem u1_exact : secondU590 1 =
    (199568949785990693712071 / 1099511627776000000000000 : ℝ) := by
  have h : D58.Cert.firstQ Cert590.Pc Cert590.P =
      (199568949785990693712071 / 1099511627776000000000000 : ℚ) := by
    decide +kernel
  unfold secondU590
  rw [D58.Cert.trialSeqS_one, h]
  norm_num

def first : FirstTrialBounds Odd.design K590.target K590.firstCost := firstTrial_D58 hrow_D58 hcol_D58 K590.first_budget_log2

theorem near : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes Odd.design * Real.log (1 + y ^ 2) +
      (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
        secondU590 1 * y ≤ D58.nearCap := by
  intro y hy
  have h := second_near_sup_d58_590 y hy
  rw [Instances.d58_gRes]
  have e : (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) = 47 / 58 := by
    norm_num [Odd.design]
  rw [e]
  simpa [D58.nearCap] using h

/-- A genuine generic field certificate with the corrected six design weights,
actual norm and covers, and the exact residual gap. -/
def second : SecondFieldCert Odd.design K590.target K590.residualCap D58.nearCap
    K590.secondCost (fun x => (401 / 2500 : ℝ) ≤ |x|) :=
  { u := secondU590, v := secondV590, hu := second_hu590, hv := second_hv590,
    MX := (Cert590.MX : ℚ), MY := (Cert590.MY : ℚ), normCap := K590.normCap,
    fieldCap := K590.fieldCap, near_sup := near, norm_le := second_norm_le590,
    field_sum := second_field_sum590,
    row_sup := by
      rw [(Instances.d58_row_weights).1, (Instances.d58_row_weights).2.1,
        (Instances.d58_row_weights).2.2]
      exact second_row_sup590,
    column_sup := by
      rw [(Instances.d58_column_weights).1, (Instances.d58_column_weights).2]
      exact second_column_sup590,
    residual_sup := fun x hx hg => by
      rw [Instances.d58_gRes]; exact second_residual_sup590 x hx hg,
    budget := fun ha ht => second_budget ha ht }

theorem circle : GapCircleBound Odd.design
    (2 * (401 / 2500 : ℝ) / (1 + (401 / 2500 : ℝ) ^ 2))
    (1001 / 1000) 3 (52788 / 1000) := circ_hcirc

/-- The real analytic provider conclusion, independent of a denominator-growth
claim. Joining it with the separately certified new ledger remains required. -/
theorem delta_small : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
    |x - catalan| ≤ Real.exp (-(rho * (N : ℝ))) →
      |aeval x (deltaPoly Odd.design N)| ≤ Real.exp (-((tDelta - ε) * (N : ℝ) ^ 2)) := by
  exact delta_small_of_certificates Odd.design_admissible circ_hg0 circ_hg1 circ_ha4
    circ_hr1 circ_hr2 circle (w := rho - 58 * K590.secondCost)
    (by norm_num [rho, K590.rho, K590.secondCost, D58.wcap]) first second
    (r := 58 * K590.secondCost)
    (by norm_num [Odd.design, K590.firstCost, K590.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring)

end
end CatalanMeasure.GenD.Uniform.Bank532
#print axioms CatalanMeasure.GenD.Uniform.Bank532.corrected_u1
#print axioms CatalanMeasure.GenD.Uniform.Bank532.first
#print axioms CatalanMeasure.GenD.Uniform.Bank532.second
#print axioms CatalanMeasure.GenD.Uniform.Bank532.circle
#print axioms CatalanMeasure.GenD.Uniform.Bank532.delta_small


