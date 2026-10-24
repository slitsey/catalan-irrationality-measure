module

public import CatalanMeasure.GenD.D58.Final
public import CatalanMeasure.GenD.Analytic.DeltaChain
public import CatalanMeasure.GenD.Analytic.Instances

@[expose] public section

/-!
# D58: the final blocks from the certificates (`delta_small` discharged)

`measure_592_of_certificates` (bank K160) and `measure_590_of_certificates` (bank K640) are
`measure_592/590_of_delta_small` with `delta_small` produced by the wired chain
`Analytic.delta_small_of_certificates` (sups -> trial bounds -> marked sheets -> weighted atoms
-> perturbation), the gap nodes of `Analytic.gapNodesD` with node count `(n0 - g0) N = 53 N`.

Remaining hypotheses (nothing else):
* `F`                  the first-population trial `FirstTrialBounds Odd.design target firstCost`
                       (trial sequences, its own row/column pointwise facts, `budget`);
* `u v hu hv MX MY ...` the second-population certificate: the three sups `row_sup`, `column_sup`,
                       `residual_sup` (with `MX + MY = fieldCap`), the trial-norm bound `norm_le`
                       and the one-variable near cap `near_sup`; its budget inequality is proved
                       here from `K160.second_budget_log2` / `K640.second_budget_log2`;
* gap and cover        `g`, and the circle certificate `GapCircleBound` (constants `rc, C, wc`)
                       with `wc < K.rho - 58 K.secondCost`;
* `c3`                 the residue determinants modulo 1009.
-/

namespace CatalanMeasure.GenD
namespace D58
open Polynomial Filter Real CatalanMeasure.Parametric OAI.InternalCatalan Set CatalanMeasure.G728
open scoped Topology
noncomputable section

section budgets
open Analytic

theorem K160.second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K160.normCap + (1 - a) * K160.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K160.residualCap + t * nearCap ≤
        -K160.target + Real.log 2 / 2 + K160.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K160.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

theorem K640.second_budget_gen {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    (-gC0 Odd.design + gC1 Odd.design * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      K640.normCap + (1 - a) * K640.fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * K640.residualCap + t * nearCap ≤
        -K640.target + Real.log 2 / 2 + K640.secondCost * a := by
  rw [Instances.d58_gC0, Instances.d58_gC1]
  have h := K640.second_budget_log2 ha ht
  norm_num [c07, c26] at h
  linarith

end budgets

/-- Bank K160: `B = 592`, from the certificates. -/
theorem measure_592_of_certificates
    {g rc C wc : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * g / (1 + g ^ 2)) rc C wc)
    (hwc : wc < K160.rho - 58 * K160.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K160.target K160.firstCost)
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (MX MY : ℝ) (field_sum : MX + MY = K160.fieldCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ K160.normCap)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          u 1 * y ≤ nearCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG (11 / 29) (3 / 29) (39 / 29) u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, g ≤ |x| →
      Analytic.resFieldGen (53 / 58) u x ≤ K160.residualCap)
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(592 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have S : Analytic.SecondFieldCert Odd.design K160.target K160.residualCap nearCap
      K160.secondCost (fun x => g ≤ |x|) :=
    { u := u, v := v, hu := hu, hv := hv, MX := MX, MY := MY, normCap := K160.normCap,
      fieldCap := K160.fieldCap, near_sup := near_sup, norm_le := norm_le,
      field_sum := field_sum,
      row_sup := by
        rw [(Analytic.Instances.d58_row_weights).1, (Analytic.Instances.d58_row_weights).2.1,
          (Analytic.Instances.d58_row_weights).2.2]
        exact row_sup,
      column_sup := by
        rw [(Analytic.Instances.d58_column_weights).1, (Analytic.Instances.d58_column_weights).2]
        exact column_sup,
      residual_sup := fun x hx hg => by
        rw [Analytic.Instances.d58_gRes]; exact residual_sup x hx hg,
      budget := fun ha ht => K160.second_budget_gen ha ht }
  refine measure_592_of_delta_small ?_ c3
  intro ε hε
  exact Analytic.delta_small_of_certificates Odd.design_admissible hg0 hg1 ha4 hr1 hr2 hcirc
    (w := K160.rho - 58 * K160.secondCost) hwc F S
    (r := 58 * K160.secondCost) (by norm_num [Odd.design, K160.firstCost, K160.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta160; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring) ε hε


/-- Bank K640: `B = 590`, from the certificates. -/
theorem measure_590_of_certificates
    {g rc C wc : ℝ} (hg0 : 0 < g) (hg1 : g < 1)
    (ha4 : 1 - (2 * g / (1 + g ^ 2)) ^ 2 ≤ 4 * (2 * g / (1 + g ^ 2)))
    (hr1 : 1 < rc) (hr2 : rc ≤ 2)
    (hcirc : Analytic.GapCircleBound Odd.design (2 * g / (1 + g ^ 2)) rc C wc)
    (hwc : wc < K640.rho - 58 * K640.secondCost)
    (F : Analytic.FirstTrialBounds Odd.design K640.target K640.firstCost)
    (u v : ℕ → ℝ) (hu : Summable (fun k => |u k|)) (hv : Summable (fun k => |v k|))
    (MX MY : ℝ) (field_sum : MX + MY = K640.fieldCap)
    (norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ K640.normCap)
    (near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
      -Analytic.gRes Odd.design * Real.log (1 + y ^ 2) +
        (((Odd.design.n0 : ℝ) - 2 * Odd.design.g0 - 1) / Odd.design.n0) * Real.log y -
          u 1 * y ≤ nearCap)
    (row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      rowFieldG (11 / 29) (3 / 29) (39 / 29) u v x ≤ MX)
    (column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (9 / 58) (3 / 58) v s ≤ MY)
    (residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, g ≤ |x| →
      Analytic.resFieldGen (53 / 58) u x ≤ K640.residualCap)
    (c3 : C3) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ, (b : ℝ) ^ (-(590 : ℝ)) < |catalan - (a : ℝ) / b| := by
  have S : Analytic.SecondFieldCert Odd.design K640.target K640.residualCap nearCap
      K640.secondCost (fun x => g ≤ |x|) :=
    { u := u, v := v, hu := hu, hv := hv, MX := MX, MY := MY, normCap := K640.normCap,
      fieldCap := K640.fieldCap, near_sup := near_sup, norm_le := norm_le,
      field_sum := field_sum,
      row_sup := by
        rw [(Analytic.Instances.d58_row_weights).1, (Analytic.Instances.d58_row_weights).2.1,
          (Analytic.Instances.d58_row_weights).2.2]
        exact row_sup,
      column_sup := by
        rw [(Analytic.Instances.d58_column_weights).1, (Analytic.Instances.d58_column_weights).2]
        exact column_sup,
      residual_sup := fun x hx hg => by
        rw [Analytic.Instances.d58_gRes]; exact residual_sup x hx hg,
      budget := fun ha ht => K640.second_budget_gen ha ht }
  refine measure_590_of_delta_small ?_ c3
  intro ε hε
  exact Analytic.delta_small_of_certificates Odd.design_admissible hg0 hg1 ha4 hr1 hr2 hcirc
    (w := K640.rho - 58 * K640.secondCost) hwc F S
    (r := 58 * K640.secondCost) (by norm_num [Odd.design, K640.firstCost, K640.secondCost])
    (by norm_num [Odd.design]) (by linarith)
    (by unfold tDelta640; rw [show ((Odd.design.n0 : ℕ) : ℝ) = 58 by norm_num [Odd.design]]; ring) ε hε


end
end D58
end CatalanMeasure.GenD
