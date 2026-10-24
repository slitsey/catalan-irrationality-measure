module

public import CatalanMeasure.GenD.Analytic.FirstGlue
public import CatalanMeasure.GenD.P20.Budget
public import CatalanMeasure.GenD.TrialScale
public import CatalanMeasure.FirstStrongTrial.NormP
public import CatalanMeasure.FirstStrongTrial.NormV
public import CatalanMeasure.FirstStrongTrial.Sup

@[expose] public section

/-!
# P20: the first-population trial `FirstTrialBounds twenty target firstCost` (instance file)

The existing frozen first trial (`FirstStrongTrial`: data, norms, and the kernel-checked suprema
`row_sup`, `column_sup` of the shifted fields) is fed into the generic `firstTrial_of_fields`; the
shifted fields are the generic scale-free first fields at the P20 weights by unfolding.
-/

namespace CatalanMeasure.GenD
namespace P20
open Set Filter OAI.InternalCatalan CatalanMeasure.Cert
open CatalanMeasure.GenD.Analytic
noncomputable section

def lamFirst : ℝ := 168493357 / 100000000
def MX1 : ℝ := -2883 / 2500
def MY1 : ℝ := -132593 / 100000

def firstP (j : ℕ) : ℝ := 2 * trialSeq FirstStrongTrial.Pc FirstStrongTrial.P j
def firstV : ℕ → ℝ := trialSeq FirstStrongTrial.Vc FirstStrongTrial.V

theorem firstP_summable : Summable (fun j => |firstP j|) := by
  have hs := (trialSeq_summable (cs := FirstStrongTrial.Pc) FirstStrongTrial.tailsP).1
  simpa only [firstP, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    using hs.mul_left (2 : ℝ)

theorem firstV_summable : Summable (fun j => |firstV j|) :=
  (trialSeq_summable (cs := FirstStrongTrial.Vc) FirstStrongTrial.tailsV).1

theorem first_norm_le :
    barrierTrialNormSq firstP + barrierTrialNormSq firstV / 2 ≤ n1 := by
  have hp : barrierTrialNormSq (trialSeq FirstStrongTrial.Pc FirstStrongTrial.P) ≤
      (FirstStrongTrial.NP : ℝ) := normOK_spec FirstStrongTrial.hNP
  have hv : barrierTrialNormSq (trialSeq FirstStrongTrial.Vc FirstStrongTrial.V) ≤
      (FirstStrongTrial.NV : ℝ) := normOK_spec FirstStrongTrial.hNV
  have e : barrierTrialNormSq firstP =
      2 ^ 2 * barrierTrialNormSq (trialSeq FirstStrongTrial.Pc FirstStrongTrial.P) :=
    barrierTrialNormSq_scale 2 _
  rw [e]
  unfold firstV
  norm_num [FirstStrongTrial.NP, FirstStrongTrial.NV, n1] at hp hv ⊢
  linarith only [hp, hv]

theorem MX1_add_MY1 : MX1 + MY1 = F1 := by norm_num [MX1, MY1, F1]

theorem firstRow_eq (x : ℝ) :
    shiftedRowField FirstStrongTrial.R FirstStrongTrial.Pc FirstStrongTrial.Vc
        FirstStrongTrial.P FirstStrongTrial.V x =
      firstRowFieldG (2 / 5) (1 / 10) (17 / 20) lamFirst (1 / 5) firstP firstV x := by
  have h : barrierTrialT firstP x =
      2 * barrierTrialT (trialSeq FirstStrongTrial.Pc FirstStrongTrial.P) x :=
    barrierTrialT_scale 2 _ x
  unfold shiftedRowField realEnergyRowTrialField realEnergyField firstRowFieldG firstRowReg
    FirstStrongTrial.R lamFirst
  rw [h]
  unfold firstV
  dsimp
  push_cast
  ring

theorem firstCol_eq (s : ℝ) :
    shiftedColumnField FirstStrongTrial.C FirstStrongTrial.Vc FirstStrongTrial.V s =
      colFieldG (3 / 20) (1 / 20) firstV s := by
  unfold shiftedColumnField realEnergyColumnTrialField realEnergyColumnField colFieldG colRegG
    FirstStrongTrial.C firstV
  dsimp
  push_cast
  ring

theorem first_hrow : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
    firstRowFieldG (2 / 5) (1 / 10) (17 / 20) lamFirst (1 / 5) firstP firstV x ≤ MX1 := by
  intro x hx
  have h := FirstStrongTrial.row_sup x hx
  rw [firstRow_eq] at h
  have e : ((FirstStrongTrial.MX : ℚ) : ℝ) = MX1 := by norm_num [FirstStrongTrial.MX, MX1]
  linarith

theorem first_hcol : ∀ s ∈ Ioo (0 : ℝ) 1, colFieldG (3 / 20) (1 / 20) firstV s ≤ MY1 := by
  intro s hs
  have h := FirstStrongTrial.column_sup s hs
  rw [firstCol_eq] at h
  have e : ((FirstStrongTrial.MY : ℚ) : ℝ) = MY1 := by norm_num [FirstStrongTrial.MY, MY1]
  linarith

/-- The first-population contract at P20. -/
def firstTrial : FirstTrialBounds design target firstCost :=
  firstTrial_of_fields design_admissible firstP firstV lamFirst (by norm_num [lamFirst])
    firstP_summable firstV_summable (2 / 5) (1 / 10) (17 / 20) (1 / 5) (3 / 20) (1 / 20)
    (by norm_num [design, Parametric.twenty]) (by norm_num [design, Parametric.twenty])
    (by norm_num [design, Parametric.twenty]) (by norm_num [design, Parametric.twenty])
    (by norm_num [design, Parametric.twenty]) (by norm_num [design, Parametric.twenty])
    MX1 MY1 first_norm_le MX1_add_MY1 first_hrow first_hcol
    (by
      intro a
      have h := first_budget_log2 a
      rw [gC0_p20, gC1_p20]
      have e : (design.g0 : ℝ) / design.n0 = 1 / 10 := by
        norm_num [design, Parametric.twenty]
      rw [e]
      have e3 : Lm = lamFirst * (2 * (1 / 10)) := by norm_num [Lm, lamFirst]
      have e4 : c07 - 1 / 2 = 1 / 5 := by norm_num [c07]
      have e5 : c26 - 1 = 8 / 5 := by norm_num [c26]
      rw [e3, e4, e5] at h
      linarith only [h])

end
end P20
end CatalanMeasure.GenD
