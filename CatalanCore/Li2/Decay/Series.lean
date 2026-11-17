module
public import CatalanCore.Li2.Decay.Atoms
public import CatalanCore.Li2.Decay.WindowSpec
@[expose] public section
/-! Canonical Li2 functional, lattice tail and lattice coefficients. Definitions only; analytic identities live in Contour/Assembly. -/
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators Polynomial
namespace CatalanCore.Li2.Decay
noncomputable def functional (z : ℝ) (n : ℕ) (t : ℝ) (T : ℂ[X]) : ℂ :=
  (∑' x : ℕ, (z:ℂ)^(x+1)*deriv (fun u : ℂ => u*weight n u*T.eval u) ((x+1:ℕ):ℂ)) +
  (t:ℂ)*∑ j ∈ Finset.Icc (n+1) (4*n), (atomWeight z n j:ℂ)*T.eval (-(j:ℂ))
noncomputable def latticeTail (z : ℝ) (n N : ℕ) (T : ℂ[X]) : ℂ :=
  ∑' k : ℕ, (z:ℂ)^(N+1+k)*
    deriv (fun u : ℂ => u*weight n u*T.eval u) ((N+1+k:ℕ):ℂ)
noncomputable def latticeA (z : ℝ) (n x : ℕ) : ℂ :=
  (z:ℂ)^x*deriv (fun u : ℂ => u*weight n u) (x:ℂ)
noncomputable def latticeB (z : ℝ) (n x : ℕ) : ℂ :=
  (z:ℂ)^x*(x:ℂ)*weight n x
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.functional
#print axioms CatalanCore.Li2.Decay.latticeTail
#print axioms CatalanCore.Li2.Decay.latticeA
#print axioms CatalanCore.Li2.Decay.latticeB
