module

public import CatalanMeasure.GenD.Analytic.FirstGlue
public import CatalanArchive.CatalanMeasure.GenDBridge.Analytic
public import CatalanArchive.CatalanMeasure.Parametric.StrongFirstFields

@[expose] public section

/-!
# Bridge (NOT part of `GenD`): `firstTrial_of_fields` at P20 reproduces `strongFirstTrialOfFields`

The generic scale-free first-row / column fields at the P20 weights are the old certificate fields
`shiftedRowField (twentyRowWeights 1 λ)` and `shiftedColumnField (twentyColumnWeights 0)`, so the
generic glue `firstTrial_of_fields` applied to the old suprema yields a `FirstTrialBounds twenty`
with the same data as `strongFirstTrialOfFields`.
-/

namespace CatalanMeasure.GenD
namespace Analytic
namespace Bridge

open CatalanMeasure.Parametric CatalanMeasure.Cert CatalanMeasure.G728 OAI.InternalCatalan Filter Set
open scoped Topology BigOperators

noncomputable section

theorem firstRowFieldG_twenty (lam : ℚ) (Pc Vc : List ℤ) (P V : List TailQ) (x : ℝ) :
    firstRowFieldG (2 / 5) (1 / 10) (17 / 20) (lam : ℝ) (1 / 5)
        (fun j => 2 * trialSeq Pc P j) (trialSeq Vc V) x =
      shiftedRowField (twentyRowWeights 1 lam) Pc Vc P V x := by
  rw [twenty_shiftedFirstRowField Nat.one_pos, twenty_populationRowField Nat.one_pos,
    twenty_caseField Nat.one_pos]
  unfold firstRowFieldG firstRowReg
  norm_num only [Rat.cast_one]
  ring

theorem colFieldG_twenty (Vc : List ℤ) (V : List TailQ) (s : ℝ) :
    colFieldG (3 / 20) (1 / 20) (trialSeq Vc V) s =
      shiftedColumnField (twentyColumnWeights 0) Vc V s := by
  rw [twenty_shiftedColumnField]
  unfold colFieldG colRegG
  norm_num only [Rat.cast_zero]
  ring

/-- Parity: the generic glue at `twenty`, fed with the old suprema, has the data of
`strongFirstTrialOfFields`. -/
def strongFirstTrial_via_generic
    (hrow : ∀ x ∈ Ico (-1:ℝ) 0 ∪ Ioo 0 1,
      shiftedRowField FirstStrongTrial.R FirstStrongTrial.Pc FirstStrongTrial.Vc
        FirstStrongTrial.P FirstStrongTrial.V x ≤ (FirstStrongTrial.MX:ℝ))
    (hcol : ∀ s ∈ Ioo (0:ℝ) 1,
      shiftedColumnField FirstStrongTrial.C FirstStrongTrial.Vc FirstStrongTrial.V s ≤
        (FirstStrongTrial.MY:ℝ)) :
    FirstTrialBounds twenty strongTarget strongFirstCost :=
  let D := strongFirstTrialOfFields hrow hcol
  firstTrial_of_fields twenty_admissible D.p D.v D.lambda D.lambda_nonneg D.p_summable D.v_summable
    (2 / 5) (1 / 10) (17 / 20) (1 / 5) (3 / 20) (1 / 20)
    (by unfold twenty; norm_num) (by unfold twenty; norm_num) (by unfold twenty; norm_num)
    (by unfold twenty; norm_num) (by unfold twenty; norm_num) (by unfold twenty; norm_num)
    D.MX D.MY D.norm_le D.field_sum
    (by
      intro x hx
      have h := hrow x hx
      rw [show FirstStrongTrial.R = twentyRowWeights 1 (168493357/100000000) by decide +kernel,
        ← firstRowFieldG_twenty] at h
      have e : (((168493357 / 100000000 : ℚ)) : ℝ) = strongLambda := by
        norm_num [strongLambda]
      rw [e] at h
      exact h)
    (by
      intro s hs
      have h := hcol s hs
      rw [show FirstStrongTrial.C = twentyColumnWeights 0 by decide +kernel,
        ← colFieldG_twenty] at h
      exact h)
    (firstToGen D).budget

end
end Bridge
end Analytic
end CatalanMeasure.GenD
