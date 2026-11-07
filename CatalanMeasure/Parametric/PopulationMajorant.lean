module
public import CatalanMeasure.Parametric.MixedMajorant
public import CatalanMeasure.Parametric.FirstSheetBounds
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial Finset Set OAI.InternalCatalan Real
open scoped BigOperators
noncomputable section

def populationTwoProduct (P : Parameters) (N : ℕ) {p m : ℕ} (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  (∏ j, (1+s j))^m*|∏ i : Fin (P.n N),∏ j ∈ Ioi i,((z j)⁻¹-(z i)⁻¹)| *
    (∏ i,|z i|^(P.g N))*(∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s

def paramSheetOneWeight (P : Parameters) (N : ℕ) (x : ℝ) : ℝ :=
  (1+x^2)^(((P.n N:ℝ)-1)/2)*|x|^((P.g N:ℤ)-((P.n N-1:ℕ):ℤ))

def populationOneProduct (P : Parameters) (N : ℕ) {p m : ℕ} (hpm : p+m=P.n N)
    (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ) : ℝ :=
  let z : Fin (P.n N) → ℝ :=fun c =>Fin.append x y (Fin.cast hpm.symm c)
  (∏ j, (1+s j))^m*(∏ i,paramSheetOneWeight P N (z i))*
    (∏ j,paramRowNodeWeight P N (y j))*paramPinPrincipal P N x s/
      (2:ℝ)^((P.n N).choose 2)

end
end CatalanMeasure.Parametric
