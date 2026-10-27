module
public import CatalanCore.Uniform.NV.PairSpace
public import CatalanCore.Uniform.NV.StepGeometry
@[expose] public section
open Polynomial Finset
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K]

noncomputable def shiftBy (L : K) (p : K[X]) : K[X] := p.comp (X+C L)
@[simp] theorem eval_shiftBy (L : K) (p : K[X]) (x : K) :
    (shiftBy L p).eval x = p.eval (x+L) := by simp [shiftBy]
@[simp] theorem natDegree_shiftBy (L : K) (p : K[X]) :
    (shiftBy L p).natDegree = p.natDegree := by
  rw [shiftBy,natDegree_comp,natDegree_X_add_C,mul_one]
@[simp] theorem leadingCoeff_shiftBy (L : K) (p : K[X]) :
    (shiftBy L p).leadingCoeff = p.leadingCoeff := by
  rw [shiftBy,leadingCoeff_comp (by simp), (monic_X_add_C L).leadingCoeff,one_pow,mul_one]

noncomputable def stepWronskian (L : K) (q p : K[X]) : K[X] :=
  shiftBy L q*p-q*shiftBy L p

theorem natDegree_stepWronskian_lt (L : K) (q p : K[X]) (hW : stepWronskian L q p ≠ 0) :
    (stepWronskian L q p).natDegree < q.natDegree+p.natDegree := by
  have hq : q ≠ 0 := by intro h; apply hW; simp [stepWronskian,shiftBy,h]
  have hp : p ≠ 0 := by intro h; apply hW; simp [stepWronskian,shiftBy,h]
  have hsq : shiftBy L q ≠ 0 := by
    intro h
    have he := leadingCoeff_shiftBy L q
    rw [h,leadingCoeff_zero] at he
    exact hq (leadingCoeff_eq_zero.mp he.symm)
  have hsp : shiftBy L p ≠ 0 := by
    intro h
    have he := leadingCoeff_shiftBy L p
    rw [h,leadingCoeff_zero] at he
    exact hp (leadingCoeff_eq_zero.mp he.symm)
  have hd : (shiftBy L q*p).natDegree = q.natDegree+p.natDegree := by
    rw [natDegree_mul hsq hp,natDegree_shiftBy]
  have hd' : (q*shiftBy L p).natDegree = q.natDegree+p.natDegree := by
    rw [natDegree_mul hq hsp,natDegree_shiftBy]
  have hlt := degree_sub_lt_left (p := shiftBy L q*p) (q := q*shiftBy L p)
    (by rw [degree_eq_natDegree (mul_ne_zero hsq hp),degree_eq_natDegree (mul_ne_zero hq hsp),hd,hd'])
    (mul_ne_zero hsq hp) (by simp only [leadingCoeff_mul,leadingCoeff_shiftBy])
  apply (natDegree_lt_iff_degree_lt hW).2
  simpa only [stepWronskian,degree_eq_natDegree (mul_ne_zero hsq hp),hd] using hlt

/-- Both top terms cancel for an arbitrary translation step. -/
theorem natDegree_stepWronskian_le (L : K) (q p : K[X]) (t : ℕ)
    (hq : q.natDegree ≤ t) (hp : p.natDegree ≤ t) (hW : stepWronskian L q p ≠ 0) :
    (stepWronskian L q p).natDegree ≤ 2*t-2 := by
  have hlt := natDegree_stepWronskian_lt L q p hW
  by_cases hpt : p.natDegree = t
  · have hp0 : p ≠ 0 := by intro hz; simp [hz,stepWronskian,shiftBy] at hW
    have hc : p.coeff t ≠ 0 := by rw [← hpt,coeff_natDegree];exact leadingCoeff_ne_zero.mpr hp0
    let q0 := C (p.coeff t)*q-C (q.coeff t)*p
    have hq0 : q0.natDegree ≤ t-1 := by
      apply natDegree_le_pred
      · exact (natDegree_sub_le _ _).trans (max_le
          ((natDegree_C_mul_le _ _).trans hq) ((natDegree_C_mul_le _ _).trans hp))
      · simp [q0,mul_comm]
    have he : stepWronskian L q0 p = C (p.coeff t)*stepWronskian L q p := by
      simp only [q0,stepWronskian,shiftBy,sub_comp,mul_comp,C_comp]
      ring
    have hw0 : stepWronskian L q0 p ≠ 0 := by rw [he];exact mul_ne_zero (C_ne_zero.mpr hc) hW
    have hd := natDegree_stepWronskian_lt L q0 p hw0
    rw [he,natDegree_C_mul hc] at hd
    omega
  · omega

noncomputable def stepDefect (L : K) (D A q p : K[X]) : K[X] :=
  D*stepWronskian L q p-A*p*shiftBy L p

theorem natDegree_stepDefect_le (L : K) (D A q p : K[X]) (d t : ℕ)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (hq : q.natDegree ≤ t) (hp : p.natDegree ≤ t) :
    (stepDefect L D A q p).natDegree ≤ 2*t+d-2 := by
  have hr : (A*p*shiftBy L p).natDegree ≤ 2*t+d-2 := by
    have hs := natDegree_shiftBy L p
    have h1 := natDegree_mul_le (p := A) (q := p)
    have h2 := natDegree_mul_le (p := A*p) (q := shiftBy L p)
    omega
  by_cases hw : stepWronskian L q p = 0
  · simpa [stepDefect,hw] using hr
  have hpos : 0 < t := by have := natDegree_stepWronskian_lt L q p hw;omega
  have hleft := natDegree_stepWronskian_le L q p t hq hp hw
  have hm := natDegree_mul_le (p := D) (q := stepWronskian L q p)
  exact (natDegree_sub_le _ _).trans (max_le (by omega) hr)

theorem stepDefect_eval_zero (L : K) (D A q p : K[X]) (x f0 f1 : K)
    (h0 : q.eval x = f0*p.eval x) (h1 : q.eval (x+L) = f1*p.eval (x+L))
    (hf : D.eval x*(f1-f0) = A.eval x) : (stepDefect L D A q p).eval x = 0 := by
  simp only [stepDefect,stepWronskian,eval_sub,eval_mul,eval_shiftBy,h0,h1]
  linear_combination hf*p.eval x*p.eval (x+L)

theorem stepDefect_derivative_eval_zero (L : K) (D A q p : K[X]) (x f0 f1 t0 t1 : K)
    (h0 : q.eval x = f0*p.eval x) (h1 : q.eval (x+L) = f1*p.eval (x+L))
    (hj0 : q.derivative.eval x = f0*p.derivative.eval x+t0*p.eval x)
    (hj1 : q.derivative.eval (x+L) = f1*p.derivative.eval (x+L)+t1*p.eval (x+L))
    (hf : D.eval x*(f1-f0) = A.eval x)
    (ht : D.derivative.eval x*(f1-f0)+D.eval x*(t1-t0) = A.derivative.eval x) :
    (stepDefect L D A q p).derivative.eval x = 0 := by
  simp only [stepDefect,stepWronskian,shiftBy,derivative_sub,derivative_mul,
    derivative_comp,derivative_add,derivative_X,derivative_C,add_zero,
    eval_sub,eval_add,eval_mul,eval_comp,eval_X,eval_C,eval_one,h0,h1,hj0,hj1]
  linear_combination ht*p.eval x*p.eval (x+L)+
    hf*(p.derivative.eval x*p.eval (x+L)+p.eval x*p.derivative.eval (x+L))
end CatalanCore.Uniform.NV

