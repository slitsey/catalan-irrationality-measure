module
public import CatalanCore.Li2.DecayCert.Lattice.Primitive.Calculus
public import Mathlib.Analysis.Calculus.Deriv.ZPow
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem mp_real_succ (σ : Measure ℂ) (y0 s : ℝ) (K : ℕ) :
    mp σ (y0:ℂ) (s:ℂ) (K+1)=mp σ (y0:ℂ) (s:ℂ) K+
      (moment σ (y0:ℂ) (K+1)).re/((K+1:ℕ)*(s-y0)^(K+1)) := by
  have hden : (K+1:ℕ)*((s:ℂ)-(y0:ℂ))^(K+1)=
      ((((K+1:ℕ):ℝ)*(s-y0)^(K+1):ℝ):ℂ) := by push_cast; rfl
  simp only [mp,Finset.sum_range_succ,Complex.add_re]
  rw [hden,Complex.div_ofReal_re]
  ring

theorem multipolePrimitive_step (σ : Measure ℂ) (y0 s : ℝ) (K : ℕ) (hK : 0 < K) :
    multipolePrimitive σ y0 s (K+1)=multipolePrimitive σ y0 s K+
      (moment σ (y0:ℂ) (K+1)).re*(s-y0)^(-(K:ℤ))/(((K+1:ℕ):ℝ)*(-(K:ℝ))) := by
  simp only [multipolePrimitive,if_pos hK,if_pos (Nat.succ_pos K),
    Finset.sum_Icc_succ_top (by omega : 2 ≤ K+1)]
  rw [show (1:ℤ)-((K+1:ℕ):ℤ)= -(K:ℤ) by omega]
  rw [show (1:ℝ)-((K+1:ℕ):ℝ)= -(K:ℝ) by push_cast; ring]
  ring

theorem multipolePrimitive_hasDerivAt (σ : Measure ℂ) (y0 : ℝ) (hy : y0 < 0)
    (s : ℝ) (hs : 0 ≤ s) (K : ℕ) :
    HasDerivAt (fun x => multipolePrimitive σ y0 x K) (mp σ (y0:ℂ) (s:ℂ) K) s := by
  have hx : 0 < s-y0 := by linarith
  have hfre : HasDerivAt (fun x : ℝ => (x-y0)*Real.log (x-y0)-(x-y0)) (Real.log (s-y0)) s := by
    have hd := (((hasDerivAt_id s).sub_const y0).mul (((hasDerivAt_id s).sub_const y0).log hx.ne')).sub
      ((hasDerivAt_id s).sub_const y0)
    convert hd using 1 <;> (try rfl) <;> simp only [id_eq,mul_one] <;> field_simp [hx.ne'] <;> ring
  induction K with
  | zero =>
    have hm : mp σ (y0:ℂ) (s:ℂ) 0= -σ.real univ*Real.log (s-y0) := by
      simp only [mp,Finset.range_zero,Finset.sum_empty,Complex.zero_re,add_zero,
        ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx]
    rw [hm]
    convert hfre.const_mul (-σ.real univ) using 1
    funext x
    simp only [multipolePrimitive,Nat.lt_irrefl,ite_false,add_zero]
    norm_num
  | succ K ih =>
    by_cases hzero : K=0
    · subst K
      have hlog := ((hasDerivAt_id s).sub_const y0).log hx.ne'
      have hd := ih.add (hlog.const_mul (moment σ (y0:ℂ) 1).re)
      convert hd using 1
      · funext x
        simp [multipolePrimitive]
      · rw [mp_real_succ]
        simp only [Nat.zero_add,Nat.cast_one,pow_one,one_mul,mul_one,id_eq] <;> ring
    · have hK : 0 < K := Nat.pos_of_ne_zero hzero
      have hKn : (K:ℝ) ≠ 0 := by exact_mod_cast hzero
      let a := (moment σ (y0:ℂ) (K+1)).re
      have hdterm : HasDerivAt
          (fun x : ℝ => a*(x-y0)^(-(K:ℤ))/(((K+1:ℕ):ℝ)*(-(K:ℝ))))
          (a/(((K+1:ℕ):ℝ)*(s-y0)^(K+1))) s := by
        have hd := (((hasDerivAt_zpow (-(K:ℤ)) (s-y0) (Or.inl hx.ne')).comp s
          ((hasDerivAt_id s).sub_const y0)).const_mul a).div_const (((K+1:ℕ):ℝ)*(-(K:ℝ)))
        convert hd using 1
        · rfl
        · simp only [mul_one,Int.cast_neg,Int.cast_natCast]
          rw [show (-(K:ℤ))-1= -((K+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
          field_simp [hx.ne',hKn] <;> ring
      convert ih.add hdterm using 1
      · funext x
        simpa only [a,Pi.add_apply] using multipolePrimitive_step σ y0 x K hK
      · rw [mp_real_succ] <;> rfl
#print axioms mp_real_succ
#print axioms multipolePrimitive_step
#print axioms multipolePrimitive_hasDerivAt
end
end CatalanCore.Li2.DecayCert
