module
public import CatalanMeasure.Parametric.PopulationFixedFields
public import CatalanMeasure.Parametric.MixedLogs
public import CatalanMeasure.Parametric.PopulationMajorant
public import CatalanMeasure.PopulationFields
@[expose] public section
namespace CatalanMeasure.Parametric
open Set Finset Real OAI.InternalCatalan Polynomial
open scoped BigOperators
noncomputable section

theorem sum_Ioi_fin_cast {a b : ℕ} (h : a=b) (F : Fin a → Fin a → ℝ) :
    (∑ i : Fin b,∑ j ∈ Ioi i,F (Fin.cast h.symm i) (Fin.cast h.symm j))=
      ∑ i : Fin a,∑ j ∈ Ioi i,F i j :=by subst b;rfl

def populationPhysicalConstant (P : Parameters) (N p : ℕ) : ℝ :=
  (((P.C N-1:ℕ):ℝ)/(P.n N:ℝ)+(p:ℝ)*((p:ℝ)-1)/(2*(P.n N:ℝ)^2))*Real.log 2

def populationPhysicalFreeField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 2 x+2/(P.n N:ℝ)*Real.log (1+x^2)

def populationPhysicalFixedField (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  paramPopulationRowField P N 2 x+1/(P.n N:ℝ)*Real.log (1+x^2)

def populationPhysicalColumnField (P : Parameters) (N m : ℕ) (s : ℝ) : ℝ :=
  (P.b N:ℝ)/(P.n N:ℝ)*Real.log s+(P.q N:ℝ)/(P.n N:ℝ)*Real.log (1-s)+
    (m:ℝ)/(P.n N:ℝ)*Real.log (1+s)

set_option maxHeartbeats 1200000 in
end
end CatalanMeasure.Parametric
