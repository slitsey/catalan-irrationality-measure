module

public import Mathlib.Tactic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# The zeta(5) content profile: definitions and the bounds of ZC21

Design `(s, κ, α, λ) = (5, 6, 3/40, 37/40)`, `H = 23/20`.

The profile is defined by the closed formula `R = x·F + Q` of CONTENT-LEDGER §B7
(`Qc` is `Q_closed`), generically over a floor field `K` so that the same definition is used
over `ℝ` (analysis) and over `ℚ` (the computable piece evaluator, `Profile.Pieces`).

* `Fs`  : the sawtooth `F = 4λ + 2λ{x} − 12λ{αx}`.
* `Qc`  : `½[τ(τ−σ) − (τ−σ)₊ + η(1−η)] + 9 tn(1−2tn) − 3 ε_f ε_g (min(te,tn) − 2 te tn)` with
  `τ={2Hx}`, `σ={2x}`, `η={2λx}`, `te = min({x},1−{x})`, `tn = min({αx},1−{αx})`.
* `Qc_ge`, `Qc_le` : `−1/2 ≤ Q ≤ 13/8` (ZC21, first half).
-/

namespace CatalanCore.Zeta5.Profile

section Gen

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- `λ = 37/40`. -/
def lam : K := 37 / 40
/-- `α = 3/40`. -/
def al : K := 3 / 40
/-- `H = 23/20`. -/
def hh : K := 23 / 20

/-- The sawtooth `F(x) = 4λ + 2λ{x} − 12λ{αx}`. -/
def Fs (x : K) : K := 4 * lam + 2 * lam * Int.fract x - 12 * lam * Int.fract (al * x)

/-- `min({x}, 1 − {x})`. -/
def tri (x : K) : K := min (Int.fract x) (1 - Int.fract x)

/-- `+1` if `{x} < 1/2`, else `−1`. -/
def sg (x : K) : K := if Int.fract x < 1 / 2 then 1 else -1

/-- The first bracket of `Q`. -/
def Q1 (x : K) : K :=
  (Int.fract (2 * hh * x) * (Int.fract (2 * hh * x) - Int.fract (2 * x))
    - max 0 (Int.fract (2 * hh * x) - Int.fract (2 * x))
    + Int.fract (2 * lam * x) * (1 - Int.fract (2 * lam * x))) / 2

/-- The second part of `Q`. -/
def Q2 (x : K) : K :=
  9 * tri (al * x) * (1 - 2 * tri (al * x))
    - 3 * sg x * sg (al * x) * (min (tri x) (tri (al * x)) - 2 * tri x * tri (al * x))

/-- `Q_closed`. -/
def Qc (x : K) : K := Q1 x + Q2 x

/-- The profile `R(x) = x F(x) + Q(x)`. -/
def Rg (x : K) : K := x * Fs x + Qc x

lemma tri_nonneg (x : K) : 0 ≤ tri x := by
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  unfold tri
  exact le_min h0 (by linarith)

lemma tri_le_half (x : K) : tri x ≤ 1 / 2 := by
  unfold tri
  rcases le_total (Int.fract x) (1 - Int.fract x) with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

omit [IsStrictOrderedRing K] in
lemma sg_sq (x : K) : sg x = 1 ∨ sg x = -1 := by
  unfold sg; split_ifs <;> simp

lemma Q1_bounds (x : K) : -1 / 8 ≤ Q1 x ∧ Q1 x ≤ 1 / 8 := by
  have ht0 := Int.fract_nonneg (2 * hh * x)
  have ht1 := Int.fract_lt_one (2 * hh * x)
  have hs0 := Int.fract_nonneg (2 * x)
  have hs1 := Int.fract_lt_one (2 * x)
  have he0 := Int.fract_nonneg (2 * lam * x)
  have he1 := Int.fract_lt_one (2 * lam * x)
  unfold Q1
  generalize Int.fract (2 * hh * x) = t at *
  generalize Int.fract (2 * x) = s at *
  generalize Int.fract (2 * lam * x) = e at *
  have hA : -1 / 4 ≤ t * (t - s) - max 0 (t - s) ∧ t * (t - s) - max 0 (t - s) ≤ 0 := by
    rcases le_total s t with h | h
    · rw [max_eq_right (by linarith)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 ht1.le),
        mul_nonneg ht0 (sub_nonneg.2 ht1.le), sq_nonneg (t - 1/2), mul_nonneg hs0 (sub_nonneg.2 ht1.le)]
    · rw [max_eq_left (by linarith)]
      constructor <;> nlinarith [mul_nonneg ht0 (sub_nonneg.2 h), mul_nonneg ht0 (sub_nonneg.2 ht1.le),
        sq_nonneg (t - 1/2), mul_nonneg ht0 (sub_nonneg.2 hs1.le), mul_nonneg (sub_nonneg.2 h) (sub_nonneg.2 hs1.le)]
  have hB : 0 ≤ e * (1 - e) ∧ e * (1 - e) ≤ 1 / 4 :=
    ⟨mul_nonneg he0 (by linarith), by nlinarith [sq_nonneg (e - 1/2)]⟩
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]

lemma Q2_bounds (x : K) : -3 / 8 ≤ Q2 x ∧ Q2 x ≤ 3 / 8 + 9 / 8 := by
  have hn0 := tri_nonneg (al * x)
  have hn1 := tri_le_half (al * x)
  have he0 := tri_nonneg x
  have he1 := tri_le_half x
  unfold Q2
  generalize tri (al * x) = n at *
  generalize tri x = a at *
  have hP : 0 ≤ 9 * n * (1 - 2 * n) ∧ 9 * n * (1 - 2 * n) ≤ 9 / 8 :=
    ⟨by nlinarith [mul_nonneg hn0 (sub_nonneg.2 hn1)], by nlinarith [sq_nonneg (n - 1/4)]⟩
  have hM : 0 ≤ min a n - 2 * a * n ∧ min a n - 2 * a * n ≤ 1 / 8 := by
    rcases le_total a n with h | h
    · rw [min_eq_left h]
      constructor <;> nlinarith [mul_nonneg he0 (sub_nonneg.2 hn1), sq_nonneg (a - 1/4),
        mul_nonneg he0 (sub_nonneg.2 h)]
    · rw [min_eq_right h]
      constructor <;> nlinarith [mul_nonneg hn0 (sub_nonneg.2 he1), sq_nonneg (n - 1/4),
        mul_nonneg hn0 (sub_nonneg.2 h)]
  have hsg : sg x * sg (al * x) = 1 ∨ sg x * sg (al * x) = -1 := by
    rcases sg_sq x with h | h <;> rcases sg_sq (al * x) with h' | h' <;> simp [h, h']
  have e1 : 9 * n * (1 - 2 * n) - 3 * sg x * sg (al * x) * (min a n - 2 * a * n)
      = 9 * n * (1 - 2 * n) - 3 * (sg x * sg (al * x)) * (min a n - 2 * a * n) := by ring
  rw [e1]
  rcases hsg with h | h <;> rw [h] <;> constructor <;> linarith [hP.1, hP.2, hM.1, hM.2]

/-- ZC21: `−1/2 ≤ Q`. -/
theorem Qc_ge (x : K) : -1 / 2 ≤ Qc x := by
  have := Q1_bounds x; have := Q2_bounds x; unfold Qc; linarith

/-- ZC21: `Q ≤ 13/8`. -/
theorem Qc_le (x : K) : Qc x ≤ 13 / 8 := by
  have := Q1_bounds x; have := Q2_bounds x; unfold Qc; linarith

end Gen

end CatalanCore.Zeta5.Profile
