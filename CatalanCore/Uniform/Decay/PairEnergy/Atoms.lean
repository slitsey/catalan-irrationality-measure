module

public import CatalanCore.Uniform.Decay.PairEnergy.Poly

@[expose] public section

/-!
# Gaussian rationals, atoms and linear forms (lane D, package D6c)

`QC` is a Gaussian rational with exact arithmetic and a cast `toC` to `ℂ`.  An `Atom` is the real
number `log ‖x + i y‖` or `arg (x + i y)` of a Gaussian rational.  A linear form `LF` is
`c + Σ q_p · atom_p` with rational `c, q_p`; this is the exact symbolic value of a pair energy.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

structure QC where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace QC

def toC (x : QC) : ℂ := ⟨(x.re : ℝ), (x.im : ℝ)⟩
def zero : QC := ⟨0, 0⟩
def one : QC := ⟨1, 0⟩
def ofQ (q : ℚ) : QC := ⟨q, 0⟩
def add (x y : QC) : QC := ⟨x.re + y.re, x.im + y.im⟩
def sub (x y : QC) : QC := ⟨x.re - y.re, x.im - y.im⟩
def neg (x : QC) : QC := ⟨-x.re, -x.im⟩
def mul (x y : QC) : QC := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def nsq (x : QC) : ℚ := x.re * x.re + x.im * x.im
def inv (x : QC) : QC := ⟨x.re / x.nsq, -x.im / x.nsq⟩
def div (x y : QC) : QC := mul x (inv y)
def qmul (q : ℚ) (x : QC) : QC := ⟨q * x.re, q * x.im⟩
def pow (x : QC) : ℕ → QC
  | 0 => one
  | n + 1 => mul (pow x n) x

@[simp] theorem toC_zero : zero.toC = 0 := by apply Complex.ext <;> simp [toC, zero]
@[simp] theorem toC_one : one.toC = 1 := by apply Complex.ext <;> simp [toC, one]
theorem toC_ofQ (q : ℚ) : (ofQ q).toC = ((q : ℝ) : ℂ) := by apply Complex.ext <;> simp [toC, ofQ]
theorem toC_add (x y : QC) : (add x y).toC = x.toC + y.toC := by
  apply Complex.ext <;> simp [toC, add]
theorem toC_sub (x y : QC) : (sub x y).toC = x.toC - y.toC := by
  apply Complex.ext <;> simp [toC, sub]
theorem toC_neg (x : QC) : (neg x).toC = -x.toC := by apply Complex.ext <;> simp [toC, neg]
theorem toC_mul (x y : QC) : (mul x y).toC = x.toC * y.toC := by
  apply Complex.ext <;> simp [toC, mul]
theorem toC_qmul (q : ℚ) (x : QC) : (qmul q x).toC = ((q : ℝ) : ℂ) * x.toC := by
  apply Complex.ext <;> simp [toC, qmul]
theorem toC_inv (x : QC) : (inv x).toC = x.toC⁻¹ := by
  apply Complex.ext
  · simp [toC, inv, nsq, Complex.inv_re, Complex.normSq_apply, div_eq_mul_inv]
  · simp [toC, inv, nsq, Complex.inv_im, Complex.normSq_apply, div_eq_mul_inv]
theorem toC_div (x y : QC) : (div x y).toC = x.toC / y.toC := by
  rw [div, toC_mul, toC_inv, div_eq_mul_inv]
theorem toC_pow (x : QC) (n : ℕ) : (pow x n).toC = x.toC ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => rw [pow, toC_mul, ih, pow_succ]

@[simp] theorem toC_re (x : QC) : x.toC.re = (x.re : ℝ) := rfl
@[simp] theorem toC_im (x : QC) : x.toC.im = (x.im : ℝ) := rfl

end QC

/-- Real constants `log ‖w‖` and `arg w` of a Gaussian rational `w`. -/
inductive Atom
  | logC (w : QC)
  | argC (w : QC)
  deriving DecidableEq, Repr

noncomputable def Atom.val : Atom → ℝ
  | .logC w => Real.log ‖w.toC‖
  | .argC w => Complex.arg w.toC

/-- Linear forms `c + Σ q_p atom_p`. -/
structure LF where
  c : ℚ
  terms : List (ℚ × Atom)

noncomputable def termsVal : List (ℚ × Atom) → ℝ
  | [] => 0
  | (q, a) :: l => (q : ℝ) * a.val + termsVal l

noncomputable def LF.val (f : LF) : ℝ := (f.c : ℝ) + termsVal f.terms

def LF.zero : LF := ⟨0, []⟩
def LF.add (f g : LF) : LF := ⟨f.c + g.c, f.terms ++ g.terms⟩
def LF.smul (q : ℚ) (f : LF) : LF := ⟨q * f.c, f.terms.map fun p => (q * p.1, p.2)⟩
def LF.const (q : ℚ) : LF := ⟨q, []⟩
/-- A term, dropped if its coefficient vanishes (so `log 0` atoms never appear with weight 0). -/
def LF.term (q : ℚ) (a : Atom) : LF := if q = 0 then ⟨0, []⟩ else ⟨0, [(q, a)]⟩

theorem termsVal_append (l m : List (ℚ × Atom)) : termsVal (l ++ m) = termsVal l + termsVal m := by
  induction l with
  | nil => simp [termsVal]
  | cons p l ih => simp only [List.cons_append, termsVal, ih]; ring

theorem termsVal_map (q : ℚ) (l : List (ℚ × Atom)) :
    termsVal (l.map fun p => (q * p.1, p.2)) = q * termsVal l := by
  induction l with
  | nil => simp [termsVal]
  | cons p l ih => simp only [List.map_cons, termsVal, ih]; push_cast; ring

@[simp] theorem LF.val_zero : LF.zero.val = 0 := by simp [LF.zero, LF.val, termsVal]
theorem LF.val_add (f g : LF) : (f.add g).val = f.val + g.val := by
  simp only [LF.add, LF.val, termsVal_append]; push_cast; ring
theorem LF.val_smul (q : ℚ) (f : LF) : (f.smul q).val = q * f.val := by
  simp only [LF.smul, LF.val, termsVal_map]; push_cast; ring
theorem LF.val_const (q : ℚ) : (LF.const q).val = q := by simp [LF.const, LF.val, termsVal]
theorem LF.val_term (q : ℚ) (a : Atom) : (LF.term q a).val = q * a.val := by
  unfold LF.term
  split_ifs with h
  · subst h; simp [LF.val, termsVal]
  · simp [LF.val, termsVal]

/-- Structural sum `Σ_{k<n} f k`. -/
def sumR (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_eq (f : ℕ → ℚ) (n : ℕ) : sumR f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumR]
  | succ n ih => rw [sumR, ih, Finset.sum_range_succ]

end CatalanCore.Uniform.Decay.PairEnergy
