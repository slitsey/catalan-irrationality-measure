module

public import CatalanMeasure.GenD.Analytic.DeltaSmall
public import CatalanMeasure.GenD.Analytic.GapWeights
public import CatalanMeasure.GenD.Analytic.Glue

@[expose] public section

/-!
# Analytic layer: the wired chain  sups -> `delta_small` (design-generic)

* `weighted_atom_point`: G2's `marked_sheet_on` feeds G3's `weighted_atom_point_of_sheet`
  (`ρ = r + w`);
* `SecondFieldCert`: the arguments of `secondTrial_of_fields` (three suprema, trial norms,
  near cap, budget) bundled as one structure, with the weights `α β γ b q` written out;
* `delta_small_of_certificates`: gap nodes `gapNodesD P (2g/(1+g²))` with the weight bounds of
  `gap_weight_bounds` (node count `(n0 - g0) N`, any parity of `d0`), the first-trial bounds `F`
  and the second-trial bounds built from a `SecondFieldCert`, give the `delta_small` shape
  consumed by `GenD.measure_of_design`.
-/

namespace CatalanMeasure.GenD
namespace Analytic

open CatalanMeasure.Parametric CatalanMeasure.CellCert OAI.InternalCatalan Filter Set Polynomial
open scoped Topology BigOperators

noncomputable section

/-- The certificate data of the second population: all arguments of `secondTrial_of_fields`
(the three suprema `row_sup`, `column_sup`, `residual_sup`, the near cap, the trial norms and the
numerical budget), with the weights written out in terms of `P`. -/
structure SecondFieldCert (P : Parameters) (target residual nearCap cost : ℝ) (G : ℝ → Prop) where
  u : ℕ → ℝ
  v : ℕ → ℝ
  hu : Summable (fun k => |u k|)
  hv : Summable (fun k => |v k|)
  MX : ℝ
  MY : ℝ
  normCap : ℝ
  fieldCap : ℝ
  near_sup : ∀ y ∈ Ioo (0 : ℝ) 1,
    -gRes P * Real.log (1 + y ^ 2) + (((P.n0 : ℝ) - 2 * P.g0 - 1) / P.n0) * Real.log y -
      u 1 * y ≤ nearCap
  norm_le : 2 * barrierTrialNormSq u + barrierTrialNormSq v / 2 ≤ normCap
  field_sum : MX + MY = fieldCap
  row_sup : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    rowFieldG (((P.b0 : ℝ) + P.q0 + 2 * P.g0) / P.n0) (2 * (P.h0 : ℝ) / P.n0)
      (((P.n0 : ℝ) + P.b0 + P.q0 + P.g0 + P.h0) / P.n0) u v x ≤ MX
  column_sup : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG ((P.b0 : ℝ) / P.n0) ((P.q0 : ℝ) / P.n0) v s ≤ MY
  residual_sup : ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes P) u x ≤ residual
  budget : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
    (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
      normCap + (1 - a) * fieldCap + a * (1 - a) * Real.log 2 +
      (a - t) * residual + t * nearCap ≤
        -target + Real.log 2 / 2 + cost * a

/-- The second-trial bounds of a `SecondFieldCert`. -/
def SecondFieldCert.bounds {P : Parameters} (hP : Admissible P)
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (C : SecondFieldCert P target residual nearCap cost G) :
    SecondTrialBounds P target residual nearCap cost G :=
  secondTrial_of_fields hP C.u C.v C.hu C.hv _ _ _ _ _ rfl rfl rfl rfl rfl C.MX C.MY nearCap
    C.near_sup C.norm_le C.field_sum C.row_sup C.column_sup C.residual_sup C.budget

end

end Analytic
end CatalanMeasure.GenD
