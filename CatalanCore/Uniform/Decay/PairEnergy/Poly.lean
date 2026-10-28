module

public import CatalanCore.Uniform.Decay.Spline.PolyDensity

@[expose] public section

/-!
# Polynomials as rational coefficient lists (lane D, package D6c)

Horner evaluation `evalL`, with the computable operations `padd`, `psmul`, `pmulX`, `pshift`
(`p(t + x)`), each with its evaluation lemma, and the identification with `ratPoly`.
-/

namespace CatalanCore.Uniform.Decay.PairEnergy

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

/-- Horner evaluation of a rational coefficient list. -/
def evalL : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: l, t => (c : ℝ) + t * evalL l t

def padd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => (a + b) :: padd p q

def psmul (x : ℚ) (p : List ℚ) : List ℚ := p.map (x * ·)

def pmulX (p : List ℚ) : List ℚ := 0 :: p

/-- Coefficients of `t ↦ p (t + x)`. -/
def pshift : List ℚ → ℚ → List ℚ
  | [], _ => []
  | c :: l, x => padd [c] (padd (pmulX (pshift l x)) (psmul x (pshift l x)))

theorem evalL_padd (p q : List ℚ) (t : ℝ) : evalL (padd p q) t = evalL p t + evalL q t := by
  induction p generalizing q with
  | nil => simp [padd, evalL]
  | cons a p ih =>
    cases q with
    | nil => simp [padd, evalL]
    | cons b q => simp only [padd, evalL, ih]; push_cast; ring

theorem evalL_psmul (x : ℚ) (p : List ℚ) (t : ℝ) : evalL (psmul x p) t = x * evalL p t := by
  induction p with
  | nil => simp [psmul, evalL]
  | cons a p ih =>
    simp only [psmul, List.map_cons, evalL] at ih ⊢
    rw [ih]; push_cast; ring

theorem evalL_pmulX (p : List ℚ) (t : ℝ) : evalL (pmulX p) t = t * evalL p t := by
  simp [pmulX, evalL]

theorem evalL_pshift (p : List ℚ) (x : ℚ) (t : ℝ) : evalL (pshift p x) t = evalL p (t + x) := by
  induction p with
  | nil => simp [pshift, evalL]
  | cons c l ih =>
    simp only [pshift, evalL_padd, evalL_pmulX, evalL_psmul, ih, evalL]
    ring

theorem evalL_eq_sum (l : List ℚ) (t : ℝ) (N : ℕ) (hN : l.length ≤ N) :
    evalL l t = ∑ k ∈ range N, ((l.getD k 0 : ℚ) : ℝ) * t ^ k := by
  induction l generalizing N with
  | nil => simp [evalL]
  | cons c l ih =>
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by simp at hN; omega⟩
    rw [Finset.sum_range_succ']
    simp only [evalL, List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    have := ih N' (by simp at hN; omega)
    rw [this, Finset.mul_sum]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => by ring

theorem ratPoly_eq_evalL (l : List ℚ) (t : ℝ) : ratPoly l t = evalL l t := by
  unfold ratPoly
  rw [evalL_eq_sum l t (l.length - 1 + 1) (by omega)]
  rfl

theorem continuous_evalL (l : List ℚ) : Continuous (evalL l) := by
  induction l with
  | nil => simpa [evalL] using continuous_const
  | cons c l ih => simp only [evalL]; fun_prop

end CatalanCore.Uniform.Decay.PairEnergy
