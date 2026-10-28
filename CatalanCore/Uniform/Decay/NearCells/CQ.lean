module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# Gaussian rationals for kernel evaluation (lane D, package D6b)

`CQ` is a pair of rationals with a cast `toC` to `ℂ`; every operation commutes with the cast.
-/

namespace CatalanCore.Uniform.Decay.NearCells

structure CQ where
  re : ℚ
  im : ℚ

namespace CQ

def toC (z : CQ) : ℂ := ⟨(z.re : ℝ), (z.im : ℝ)⟩

def zero : CQ := ⟨0, 0⟩
def one : CQ := ⟨1, 0⟩
def ofQ (q : ℚ) : CQ := ⟨q, 0⟩
def add (a b : CQ) : CQ := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : CQ) : CQ := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : CQ) : CQ := ⟨-a.re, -a.im⟩
def mul (a b : CQ) : CQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def smul (q : ℚ) (a : CQ) : CQ := ⟨q * a.re, q * a.im⟩
def nsq (a : CQ) : ℚ := a.re * a.re + a.im * a.im
def inv (a : CQ) : CQ := ⟨a.re / a.nsq, -a.im / a.nsq⟩
def div (a b : CQ) : CQ := mul a (inv b)
def pow (a : CQ) : ℕ → CQ
  | 0 => one
  | n + 1 => mul (pow a n) a

/-- Structural sum `∑_{i<n} f i`. -/
def sumTo (f : ℕ → CQ) : ℕ → CQ
  | 0 => zero
  | n + 1 => add (sumTo f n) (f n)

theorem toC_zero : zero.toC = 0 := by apply Complex.ext <;> simp [toC, zero]
theorem toC_one : one.toC = 1 := by apply Complex.ext <;> simp [toC, one]
theorem toC_ofQ (q : ℚ) : (ofQ q).toC = (q : ℂ) := by apply Complex.ext <;> simp [toC, ofQ]
theorem toC_add (a b : CQ) : (add a b).toC = a.toC + b.toC := by
  apply Complex.ext <;> simp [toC, add]
theorem toC_sub (a b : CQ) : (sub a b).toC = a.toC - b.toC := by
  apply Complex.ext <;> simp [toC, sub]
theorem toC_neg (a : CQ) : (neg a).toC = -a.toC := by
  apply Complex.ext <;> simp [toC, neg]
theorem toC_mul (a b : CQ) : (mul a b).toC = a.toC * b.toC := by
  apply Complex.ext <;> simp [toC, mul]
theorem toC_smul (q : ℚ) (a : CQ) : (smul q a).toC = (q : ℂ) * a.toC := by
  apply Complex.ext <;> simp [toC, smul]
theorem toC_pow (a : CQ) (n : ℕ) : (pow a n).toC = a.toC ^ n := by
  induction n with
  | zero => simp [pow, toC_one]
  | succ n ih => rw [pow, toC_mul, ih, pow_succ]

theorem nsq_cast (a : CQ) : ((a.nsq : ℚ) : ℝ) = Complex.normSq a.toC := by
  simp [nsq, toC, Complex.normSq_apply]

theorem toC_inv (a : CQ) (h : a.nsq ≠ 0) : (inv a).toC = (a.toC)⁻¹ := by
  have h' : Complex.normSq a.toC ≠ 0 := by rw [← nsq_cast]; exact_mod_cast h
  rw [Complex.inv_def]
  apply Complex.ext <;> simp [toC, inv, Complex.normSq_apply, nsq] at h' ⊢ <;> push_cast <;> ring_nf

theorem toC_div (a b : CQ) (h : b.nsq ≠ 0) : (div a b).toC = a.toC / b.toC := by
  rw [div, toC_mul, toC_inv b h, div_eq_mul_inv]

theorem toC_ne_zero {a : CQ} (h : a.nsq ≠ 0) : a.toC ≠ 0 := by
  intro h0
  apply h
  have : Complex.normSq a.toC = 0 := by rw [h0]; simp
  rw [← nsq_cast] at this
  exact_mod_cast this

theorem toC_sumTo (f : ℕ → CQ) (n : ℕ) :
    (sumTo f n).toC = ∑ i ∈ Finset.range n, (f i).toC := by
  induction n with
  | zero => simp [sumTo, toC_zero]
  | succ n ih => rw [sumTo, toC_add, ih, Finset.sum_range_succ]

theorem toC_re (a : CQ) : a.toC.re = (a.re : ℝ) := rfl
theorem toC_im (a : CQ) : a.toC.im = (a.im : ℝ) := rfl

end CQ

end CatalanCore.Uniform.Decay.NearCells
