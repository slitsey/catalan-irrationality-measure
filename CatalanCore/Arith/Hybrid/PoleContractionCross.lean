module
public import CatalanCore.Arith.Hybrid.PoleContraction
@[expose] public section
open Finset
namespace CatalanCore.Arith.Hybrid

/-- **Two-source pole contraction (leading cross-cell block).**  For two different sources, with
coefficient vectors `v` (on `ι`) and `w` (on `κ`), pole values `f`, `g` and shifts `t`, `t'`,
the exact reciprocal expansion `1/(d+εk) = 1/d - εk/(d(d+εk))` gives the leading
`(A B' - B A')/(n ε d)` term, with `A = ∑ v f`, `B = ∑ v`, `A' = ∑ w g`, `B' = ∑ w`, and an
explicit remainder with only the unit denominators `d`, `d + ε(t' - t)`.
`contracted_pole_exact` is the same-source case `w = v`, `g = f`, `t' = t` (there the leading term
vanishes). -/
theorem contracted_pole_cross {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ]
    (v f t : ι→K) (w g t' : κ→K) (n eps d : K) (hn : n≠0) (heps : eps≠0) (hd : d≠0)
    (hshift : ∀i j,d+eps*(t' j-t i)≠0) :
    (∑i,∑j,v i*w j*(f i-g j)/(n*eps*(d+eps*(t' j-t i)))) =
      ((∑i,v i*f i)*(∑j,w j)-(∑i,v i)*(∑j,w j*g j))/(n*eps*d)
      -(∑i,∑j,v i*w j*(f i-g j)*(t' j-t i)/(n*d*(d+eps*(t' j-t i)))) := by
  have point (i j) : v i*w j*(f i-g j)/(n*eps*(d+eps*(t' j-t i))) =
      v i*w j*(f i-g j)/(n*eps*d)
      -v i*w j*(f i-g j)*(t' j-t i)/(n*d*(d+eps*(t' j-t i))) := by
    field_simp [hn,heps,hd,hshift i j]
    <;> ring
  simp_rw [point]
  simp only [Finset.sum_sub_distrib,←Finset.sum_div]
  congr 1
  congr 1
  simp only [mul_sub, Finset.sum_sub_distrib]
  have e1 : (∑i,∑j,v i*w j*f i)=(∑i,v i*f i)*(∑j,w j) := by
    rw [Finset.sum_mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl
    intro j _; ring
  have e2 : (∑i,∑j,v i*w j*g j)=(∑i,v i)*(∑j,w j*g j) := by
    rw [Finset.sum_mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl
    intro j _; ring
  rw [e1, e2]

#print axioms contracted_pole_cross
end CatalanCore.Arith.Hybrid
