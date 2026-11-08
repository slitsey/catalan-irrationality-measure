module

public import CatalanMeasure.GenD.Analytic.InverseImageKeyhole
public import CatalanMeasure.GenD.Analytic.PsiSelector
public import CatalanMeasure.GenD.Signed.Davis.Design72Nodes

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis
open Set Polynomial CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Refinement.Trimmed130
noncomputable section

local notation "P72" => dc72.toParameters

def green72 (z : ℂ) : ℝ := nodalGreen realP 130 z
def circleCap72 : ℝ := 24330011831893 / 549755813888
def psi072 : ℝ := 119576174384707 / 1099511627776
def omega72 (κ : ℝ) : ℝ := ((12 - 72 * κ) * Real.log (3 / 5) + circleCap72) / 72

theorem psi072_strict : psi072 < (54377 / 500 : ℝ) := by
  norm_num [psi072]

theorem hweights72_of_contour
    (hcirc : ∀ z : ℂ, ‖z‖ = (3 / 5 : ℝ) →
      8 * Real.log ‖(1 : ℂ) - z‖ + 66 * green72 z ≤ circleCap72)
    (hseg : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, (3 / 5 : ℝ) ≤ |x| → |x| ≤ 1 →
      nodalPhi P72 green72 κ (x : ℂ) ≤ 72 * omega72 κ)
    (hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, omega72 κ + binomRate κ ≤ psi072 / 72) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ p m : ℕ, p + m = 72 * N →
      ∀ k : ℕ, k < 72 * N → ∀ i : Fin (66 * N),
        |(rowCommonFactor P72 N).eval (tau72 N i)| *
          |restrictedWeight P72 N k (tau72 N) i| *
          (CatalanMeasure.binomBeta p m k : ℝ) ≤
            108000 * (N : ℝ) * Real.exp ((54377 / 500 : ℝ) * N) := by
  have hcircle : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = (3 / 5 : ℝ) →
      nodalPhi P72 green72 κ z ≤ 72 * omega72 κ := by
    intro κ hκ z hz
    norm_num [nodalPhi, dc72, DesignConst.toParameters]
    rw [hz]
    unfold omega72
    linarith [hcirc z hz]
  exact inverseImage_binom_hweights_of_phi P72 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) branchCertificate realP_natDegree (by norm_num)
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1) omega72 hcircle hseg hΨ
    (by change 72 * (psi072 / 72) < (54377 / 500 : ℝ); nlinarith [psi072_strict])

theorem hPsi72_of_finite_selector {ι : Type*} (lo hi U : ι → ℝ)
    (hcover : ∀ κ ∈ Icc (0 : ℝ) 1, ∃ i, κ ∈ Icc (lo i) (hi i))
    (hlo : ∀ i, 0 ≤ lo i) (hhi : ∀ i, hi i ≤ 1)
    (hU : ∀ i, (12 - 72 * hi i) * Real.log (3 / 5) + circleCap72 ≤ U i)
    (hΨ : ∀ i, U i + 72 * binomRate (lo i) ≤ psi072) :
    ∀ κ ∈ Icc (0 : ℝ) 1, omega72 κ + binomRate κ ≤ psi072 / 72 := by
  have ht := finite_affine_circle_selector lo hi U
    (by norm_num : (0 : ℝ) < 3 / 5) (by norm_num : (3 / 5 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) ≤ 72) hcover hlo hhi hU hΨ
  intro κ hκ
  have h := ht κ hκ
  unfold omega72
  linarith

end
end CatalanMeasure.GenD.Signed.Davis
#print axioms CatalanMeasure.GenD.Signed.Davis.psi072_strict
#print axioms CatalanMeasure.GenD.Signed.Davis.hweights72_of_contour
#print axioms CatalanMeasure.GenD.Signed.Davis.hPsi72_of_finite_selector
