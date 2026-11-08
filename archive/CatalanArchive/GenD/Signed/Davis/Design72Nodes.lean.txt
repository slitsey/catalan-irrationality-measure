module
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Analytic.RationalNodeScale
public import CatalanMeasure.GenD.Signed.Davis.InverseImageWeights
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Branches
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Support

@[expose] public section
namespace CatalanMeasure.GenD.Signed.Davis
open Set CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open CatalanMeasure.Refinement.Trimmed130 CatalanMeasure.Improvement.Fields
noncomputable section

/-! D72 specialization of the pinned Davis construction. The construction and
branch proofs are reused unchanged; this file supplies only the design argument.
The fitted trial break dc72.gstar remains independent of actual node support. -/

local notation "P72" => dc72.toParameters

def tau72 (N : ℕ) : Fin (66 * N) → ℝ :=
  inverseQuadratureNodes P72 branchCertificate (by norm_num) N

theorem tau72_injective (N : ℕ) : Function.Injective (tau72 N) :=
  inverseQuadratureNodes_injective P72 branchCertificate (by norm_num) N

theorem tau72_mem (N : ℕ) (a : Fin (66 * N)) : tau72 N a ∈ Ioo (-1 : ℝ) 1 :=
  (inverseQuadratureNodes_support P72 branchCertificate (by norm_num) N a).1

theorem tau72_ne_zero (N : ℕ) (a : Fin (66 * N)) : tau72 N a ≠ 0 :=
  (inverseQuadratureNodes_support P72 branchCertificate (by norm_num) N a).2.1

theorem tau72_allowed (N : ℕ) (a : Fin (66 * N)) : allowedT (tau72 N a) :=
  (inverseQuadratureNodes_support P72 branchCertificate (by norm_num) N a).2.2

theorem tau72_trimmed_support (N : ℕ) (a : Fin (66 * N)) :
    trimmedResidualSupport (realCoordinate (tau72 N a)) :=
  coordinate_mem_trimmedSupport (tau72_mem N a) (tau72_allowed N a)

theorem tau72_support (N : ℕ) (a : Fin (66 * N)) :
    realCoordinate (tau72 N a) ≤ -(19501 / 100000 : ℝ) ∨
      (98749 / 1000000 : ℝ) ≤ realCoordinate (tau72 N a) := by
  rcases tau72_trimmed_support N a with hn | hp
  · exact Or.inl (by simpa only [neg_div] using hn.2)
  · exact Or.inr hp.1

def umin72 (N : ℕ) : ℝ := 1 / (2 * (66 * (N : ℝ) + 130))

theorem umin72_pos (N : ℕ) : 0 < umin72 N := by
  unfold umin72
  positivity

theorem umin72_le_one (N : ℕ) : umin72 N ≤ 1 := by
  unfold umin72
  rw [div_le_one (by positivity)]
  have h : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

theorem umin72_log_sublinear :
    Filter.Tendsto (fun N : ℕ => -Real.log (umin72 N) / ((72 * N : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
  have h := rational_node_scale_log_sublinear (s := (1 : ℝ)) (A := 132)
    (B := 260) (n0 := 72) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  convert h using 1
  funext N
  unfold umin72
  push_cast
  congr 2 <;> ring

end
end CatalanMeasure.GenD.Signed.Davis
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_injective
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_mem
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_ne_zero
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_allowed
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_trimmed_support
#print axioms CatalanMeasure.GenD.Signed.Davis.tau72_support
#print axioms CatalanMeasure.GenD.Signed.Davis.umin72_pos
#print axioms CatalanMeasure.GenD.Signed.Davis.umin72_le_one

#print axioms CatalanMeasure.GenD.Signed.Davis.umin72_log_sublinear
