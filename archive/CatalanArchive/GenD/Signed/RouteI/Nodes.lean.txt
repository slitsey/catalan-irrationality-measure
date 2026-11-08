module
public import CatalanMeasure.GenD.Signed.RouteI.Literals
public import CatalanMeasure.GenD.Signed.Davis.InverseImageWeights
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Branches
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Support

@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.RouteI
open Set Polynomial CatalanMeasure.GenD.Analytic OAI.InternalCatalan
open CatalanMeasure.Refinement.Trimmed130
noncomputable section

/-! Reuse the actual realP/130/allowedT branch certificate. Degree1013 is
the circle polynomial, and is not a branch-certificate parameter. -/
def tau58 (N : ℕ) : Fin (53*N) → ℝ :=
  inverseQuadratureNodes dc58.toParameters branchCertificate (by norm_num) N

theorem tau58_injective (N : ℕ) : Function.Injective (tau58 N) :=
  inverseQuadratureNodes_injective dc58.toParameters branchCertificate (by norm_num) N

theorem tau58_mem (N : ℕ) (a : Fin (53*N)) : tau58 N a ∈ Ioo (-1:ℝ) 1 :=
  (inverseQuadratureNodes_support dc58.toParameters branchCertificate (by norm_num) N a).1

theorem tau58_ne_zero (N : ℕ) (a : Fin (53*N)) : tau58 N a≠0 :=
  (inverseQuadratureNodes_support dc58.toParameters branchCertificate (by norm_num) N a).2.1

theorem tau58_allowed (N : ℕ) (a : Fin (53*N)) : allowedT (tau58 N a) :=
  (inverseQuadratureNodes_support dc58.toParameters branchCertificate (by norm_num) N a).2.2

theorem tau58_support (N : ℕ) (a : Fin (53*N)) :
    G58 (realCoordinate (tau58 N a)) := by
  rcases coordinate_mem_trimmedSupport (tau58_mem N a) (tau58_allowed N a) with hn | hp
  · exact Or.inl (by simpa only [neg_div] using hn.2)
  · exact Or.inr hp.1

end
end CatalanMeasure.GenD.Signed.RouteI
#print axioms CatalanMeasure.GenD.Signed.RouteI.tau58_injective
#print axioms CatalanMeasure.GenD.Signed.RouteI.tau58_mem
#print axioms CatalanMeasure.GenD.Signed.RouteI.tau58_ne_zero
#print axioms CatalanMeasure.GenD.Signed.RouteI.tau58_allowed
#print axioms CatalanMeasure.GenD.Signed.RouteI.tau58_support

