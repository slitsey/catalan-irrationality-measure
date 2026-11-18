module
public import CatalanCore.Li2.DecayCert.Lattice.Primitive.Calculus
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem latticeOwn_coordinate (Y s : ℝ) (hY : 0 < Y) (hs : s ∈ Icc 0 Y) :
    2*s/Y-1 ∈ Icc (-1:ℝ) 1 ∧
    (Y/2:ℂ)+(Y/2:ℂ)*((2*s/Y-1:ℝ):ℂ)=(s:ℂ) := by
  constructor
  · have h0 : (0:ℝ) ≤ 2*s/Y := div_nonneg (by linarith [hs.1]) hY.le
    have h1 : 2*s/Y ≤ 2 := (div_le_iff₀ hY).mpr (by linarith [hs.2])
    constructor <;> linarith
  · push_cast
    field_simp [hY.ne']
    ring

theorem ownUPoly_eval {σ1 σ2 : Measure ℂ} {Y : ℝ} (d : LatticeMomentData σ1 σ2 Y) (s : ℝ) :
    (ownUPoly d).eval s=∑ k ∈ Finset.range d.N,
      d.c (k+1)*(Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (2*s/Y-1)/(k+1:ℕ) := by
  rw [ownUPoly,Polynomial.eval_comp]
  simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
  have he : -1+(2/Y)*s=2*s/Y-1 := by ring
  rw [he,Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  ring

theorem latticeOwn_source {σ1 σ2 : Measure ℂ} {Y : ℝ} (d : LatticeMomentData σ1 σ2 Y)
    (hY : 0 < Y) (s : ℝ) (hs : s ∈ Icc 0 Y) :
    Integrable (fun u => Real.log ‖(s:ℂ)-u‖) σ1 ∧
      U σ1 (s:ℂ)=d.c 0*Real.log (4/Y)+(ownUPoly d).eval s := by
  have hh : (Y/2:ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hY.ne') (by norm_num)
  have hcoord := latticeOwn_coordinate Y s hY hs
  have hp := CatalanCore.Lai.DecayEnergy.potC_seg_inside (M:=(Y/2:ℂ)) hh d.nonneg hcoord.1
  rw [hcoord.2,← d.first_measure] at hp
  refine ⟨hp.1,?_⟩
  have hn : ‖(Y/2:ℂ)‖=Y/2 := by
    rw [norm_div,Complex.norm_two,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY]
  have h4 : Real.log (4:ℝ)=2*Real.log 2 := by
    rw [show (4:ℝ)=2*2 by norm_num,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    ring
  have hl : Real.log (Y/2)-Real.log 2= -Real.log (4/Y) := by
    rw [Real.log_div hY.ne' (by norm_num : (2:ℝ) ≠ 0),Real.log_div (by norm_num : (4:ℝ) ≠ 0) hY.ne',h4]
    ring
  have hpval := hp.2
  change P σ1 (s:ℂ)=_ at hpval
  rw [hn] at hpval
  rw [U,hpval,ownUPoly_eval]
  have hsum : (∑ k ∈ Finset.range d.N,
      (Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (2*s/Y-1)*d.c (k+1)/(k+1:ℕ))=
      ∑ k ∈ Finset.range d.N,d.c (k+1)*(Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (2*s/Y-1)/(k+1:ℕ) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum]
  linear_combination -(d.c 0)*hl
#print axioms latticeOwn_coordinate
#print axioms ownUPoly_eval
#print axioms latticeOwn_source
end
end CatalanCore.Li2.DecayCert
