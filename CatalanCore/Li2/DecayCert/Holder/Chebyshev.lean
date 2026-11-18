module
public import CatalanCore.Li2.DecayCert.Compile
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open Polynomial.Chebyshev
noncomputable section

theorem cheb_T_complex_bound (z : ℂ) (Z Φ : ℝ) (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z)
    (hΦ : 1 ≤ Φ) (hrel : Φ^2=2*Z*Φ+1) (n : ℕ) :
    ‖(Chebyshev.T ℂ (n:ℤ)).eval z‖ ≤ Φ^n := by
  have hp : 0 ≤ Φ := zero_le_one.trans hΦ
  have hZΦ : Z ≤ Φ := by nlinarith [mul_nonneg hZ hp]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using hz.trans hZΦ
  | more n ih0 ih1 =>
    have he : ((n+2:ℕ):ℤ)=(n:ℤ)+2 := by omega
    have he1 : ((n+1:ℕ):ℤ)=(n:ℤ)+1 := by omega
    rw [he,T_add_two]
    simp only [eval_sub,eval_mul,eval_ofNat,eval_X]
    calc
      ‖2*z*(Chebyshev.T ℂ ((n:ℤ)+1)).eval z-(Chebyshev.T ℂ (n:ℤ)).eval z‖ ≤
          ‖2*z*(Chebyshev.T ℂ ((n:ℤ)+1)).eval z‖+‖(Chebyshev.T ℂ (n:ℤ)).eval z‖ := norm_sub_le _ _
      _ = 2*‖z‖*‖(Chebyshev.T ℂ ((n:ℤ)+1)).eval z‖+‖(Chebyshev.T ℂ (n:ℤ)).eval z‖ := by simp only [norm_mul,Complex.norm_two]
      _ ≤ 2*Z*Φ^(n+1)+Φ^n := by rw [← he1]; gcongr
      _ = Φ^n*(2*Z*Φ+1) := by rw [pow_succ]; ring
      _ = Φ^(n+2) := by rw [← hrel,pow_add]

theorem cheb_U_complex_bound (z : ℂ) (Z Φ : ℝ) (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z)
    (hΦ : 1 ≤ Φ) (hrel : Φ^2=2*Z*Φ+1) (n : ℕ) :
    ‖(Chebyshev.U ℂ (n:ℤ)).eval z‖ ≤ (n+1:ℕ)*Φ^n := by
  have hp : 0 ≤ Φ := zero_le_one.trans hΦ
  have hZΦ : Z ≤ Φ := by nlinarith [mul_nonneg hZ hp]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    simp only [Nat.cast_one,U_one,eval_mul,eval_ofNat,eval_X,norm_mul,Complex.norm_two,pow_one]
    norm_num
    linarith
  | more n ih0 ih1 =>
    have he : ((n+2:ℕ):ℤ)=(n:ℤ)+2 := by omega
    have he1 : ((n+1:ℕ):ℤ)=(n:ℤ)+1 := by omega
    rw [he,U_add_two]
    simp only [eval_sub,eval_mul,eval_ofNat,eval_X]
    calc
      ‖2*z*(U ℂ ((n:ℤ)+1)).eval z-(U ℂ (n:ℤ)).eval z‖ ≤
          ‖2*z*(U ℂ ((n:ℤ)+1)).eval z‖+‖(U ℂ (n:ℤ)).eval z‖ := norm_sub_le _ _
      _ = 2*‖z‖*‖(U ℂ ((n:ℤ)+1)).eval z‖+‖(U ℂ (n:ℤ)).eval z‖ := by simp only [norm_mul,Complex.norm_two]
      _ ≤ 2*Z*((n+2:ℕ)*Φ^(n+1))+(n+1:ℕ)*Φ^n := by rw [← he1]; gcongr
      _ ≤ (n+2+1:ℕ)*Φ^(n+2) := by
        have hbase : 2*Z*(n+2:ℕ)*Φ+(n+1:ℕ) ≤ (n+2+1:ℕ)*Φ^2 := by
          rw [hrel]
          push_cast
          nlinarith [mul_nonneg hZ hp]
        have hh := mul_le_mul_of_nonneg_left hbase (pow_nonneg hp n)
        simpa only [pow_add,pow_succ,pow_two] using (by convert hh using 1 <;> ring)

theorem cheb_T_derivative_real_bound (n : ℕ) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    |(Polynomial.derivative (Chebyshev.T ℝ (n:ℤ))).eval x| ≤ (n:ℝ)^2 := by
  have hh := abs_iterate_derivative_T_real_le (n:ℤ) 1 (abs_le.mpr hx)
  simp only [Function.iterate_one,T_derivative_eq_U,eval_mul,eval_intCast,U_eval_one] at hh
  push_cast at hh
  have hr : (n:ℝ)*((n:ℝ)-1+1)=(n:ℝ)^2 := by ring
  rw [hr] at hh
  simpa only [T_derivative_eq_U,eval_mul,eval_intCast,Int.cast_natCast,eval_natCast] using hh
#print axioms cheb_T_complex_bound
#print axioms cheb_U_complex_bound
#print axioms cheb_T_derivative_real_bound
end
end CatalanCore.Li2.DecayCert
