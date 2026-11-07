module

public import CatalanCore.Frame.Spec
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Support data (lane H, wave H2; ledger S01, S04, N9)

A **datum** is a finite set of shifts `s ∈ ℚ ∩ (0, 1]`, each with two integers `a_s, b_s`, not both zero,
`∑ a_s = 0`.  The **order** of `s` is `1` if `b_s = 0`, else `2`, and `d = ∑ w(s)`.

`F(z) = ∑ [a_s ψ(z + s) + b_s ψ′(z + s)]`, `δ(z) = F(z + 1) - F(z) = ∑ [a_s/(z+s) - b_s/(z+s)²]`,
`ξ = F′(0) = ∑ [a_s ζ(2, s) - 2 b_s ζ(3, s)]`.

The Löwner data of the datum are the two sequences
`f_t = ∑_{k<t} δ(k)` and `e_t = -∑_{k<t} δ′(k)`, so that `Φ(T)[x, y] = (f_y - f_x)/(y - x)` and
`Φ(T)[c, c] = T - e_c`.  The pair `(𝖣, A)` with `𝖣 = ∏ (z + s)^{w(s)}`, `A = 𝖣 δ` is determined by the
datum (`Support.NV`).

`Reference` is the reference frame of S04: a simple-pole `Frame` whose atoms match the head atoms of the
datum (F1, F2) and are separated (F3).  `Datum.plane2 v u` is the integer form of the plane 2 datum
(N9), for integers `v ≠ 0 ≠ u`: `S = {1, ½}`, `a = (u, -u)`, `b = (v, 0)`.

Everything here is generic in the datum: no weight, shift set or bound is fixed except in `plane2`, whose
only parameters are the integers `(v, u)`.
-/

open Polynomial Finset

namespace CatalanCore.Uniform.Support

/-- The Hurwitz series `ζ(3, μ) = ∑_{n ≥ 0} 1/(n + μ)³`. -/
noncomputable def hurwitzTail3 (μ : ℚ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + (μ : ℝ)) ^ 3

/-- A support datum (S01). -/
structure Datum where
  /-- number of shifts -/
  n : ℕ
  hn : 0 < n
  /-- shifts `s ∈ (0, 1]` -/
  s : Fin n → ℚ
  /-- the simple-pole integers `a_s` -/
  a : Fin n → ℤ
  /-- the double-pole integers `b_s` -/
  b : Fin n → ℤ
  hs : ∀ i, 0 < s i ∧ s i ≤ 1
  hinj : Function.Injective s
  hab : ∀ i, a i ≠ 0 ∨ b i ≠ 0
  hbal : ∑ i, a i = 0

namespace Datum

variable (D : Datum)

/-- The order `w(s)` of a shift: `1` if `b_s = 0`, else `2`. -/
def w (i : Fin D.n) : ℕ := if D.b i = 0 then 1 else 2

theorem w_pos (i : Fin D.n) : 1 ≤ D.w i := by unfold w; split_ifs <;> omega

theorem w_le (i : Fin D.n) : D.w i ≤ 2 := by unfold w; split_ifs <;> omega

/-- Total order `d = ∑ w(s)`. -/
def d : ℕ := ∑ i, D.w i

/-- `δ(x) = ∑ [a_s/(x+s) - b_s/(x+s)²]`. -/
def delta (x : ℚ) : ℚ := ∑ i, ((D.a i : ℚ) / (x + D.s i) - (D.b i : ℚ) / (x + D.s i) ^ 2)

/-- `δ′(x) = ∑ [-a_s/(x+s)² + 2 b_s/(x+s)³]`. -/
def delta1 (x : ℚ) : ℚ :=
  ∑ i, (-(D.a i : ℚ) / (x + D.s i) ^ 2 + 2 * (D.b i : ℚ) / (x + D.s i) ^ 3)

/-- `f_t = ∑_{k<t} δ(k)`. -/
def f (t : ℕ) : ℚ := ∑ k ∈ range t, D.delta k

/-- `e_t = -∑_{k<t} δ′(k)`. -/
def e (t : ℕ) : ℚ := -∑ k ∈ range t, D.delta1 k

/-- `ξ = F′(0) = ∑ [a_s ζ(2, s) - 2 b_s ζ(3, s)]`. -/
noncomputable def xi : ℝ :=
  ∑ i, ((D.a i : ℝ) * CatalanCore.hurwitzTail2 (D.s i) - 2 * (D.b i : ℝ) * hurwitzTail3 (D.s i))

/-- `𝖣(z) = ∏ (z + s)^{w(s)}`. -/
noncomputable def Dpoly : ℚ[X] := ∏ i, (X + C (D.s i)) ^ D.w i

/-- `∏_{j ≠ i} (z + s_j)^{w_j}`. -/
noncomputable def Dexc (i : Fin D.n) : ℚ[X] := ∏ j ∈ univ.erase i, (X + C (D.s j)) ^ D.w j

/-- `A = 𝖣 δ`, as the explicit polynomial `∑ [a_s 𝖣/(z+s) - b_s 𝖣/(z+s)²]`. -/
noncomputable def Apoly : ℚ[X] :=
  ∑ i, (C (D.a i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1)) -
    C (D.b i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 2)))

end Datum

/-! ### Reference frames (S04) -/

/-- A reference frame for a datum (S04): a simple-pole frame `𝔉` and a crossing abscissa `x*` such that

* (F1) every shift of the datum is a shift of `𝔉`, and every double shift has its own helper shift of `𝔉`
  that is not a shift of the datum;
* (F2) the atoms `x_{s,n} = -s - n` of the datum right of `x*` are matched by the atoms of `𝔉` with the same
  label, and the helper atom `(s*, n)` is at distance at most `1/2` from `x_{s,n}`, on the same side of `x*`;
* (F3) atoms of `𝔉` are at least `gap > 0` apart. -/
structure Reference (D : Datum) where
  Fr : Frame
  /-- crossing abscissa -/
  xstar : ℚ
  /-- matched shift of `𝔉` -/
  idx : Fin D.n → Fin Fr.d
  /-- helper shift of `𝔉` for a double shift -/
  helper : Fin D.n → Fin Fr.d
  gap : ℚ
  hgap : 0 < gap
  F1_idx : ∀ i, Fr.μ (idx i) = D.s i
  F1_helper : ∀ i, D.b i ≠ 0 → ∀ j, Fr.μ (helper i) ≠ D.s j
  F1_helper_inj : ∀ i j, D.b i ≠ 0 → D.b j ≠ 0 → helper i = helper j → i = j
  F2_dist : ∀ i, D.b i ≠ 0 → |Fr.μ (helper i) - D.s i| ≤ 1 / 2
  F2_side : ∀ i, D.b i ≠ 0 → ∀ n : ℕ,
    (xstar < -D.s i - n ↔ xstar < -Fr.μ (helper i) - n)
  F3_sep : ∀ (i j : Fin Fr.d) (m n : ℕ), (i, m) ≠ (j, n) →
    gap ≤ |(-Fr.μ i - m) - (-Fr.μ j - n)|

/-! ### The plane 2 datum (N9) -/

/-- The integer form of the plane 2 datum, `S = {1, ½}`, `a = (u, -u)`, `b = (v, 0)`, for integers
`v ≠ 0 ≠ u`; `b = u/v` is the weight ratio, and primes dividing `v` never enter. -/
@[reducible] def Datum.plane2 (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : Datum where
  n := 2
  hn := by norm_num
  s := ![1, 1 / 2]
  a := ![u, -u]
  b := ![v, 0]
  hs := by intro i; fin_cases i <;> norm_num
  hinj := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  hab := by
    intro i; fin_cases i
    · exact Or.inr (by simpa using hv)
    · exact Or.inl (by simpa using hu)
  hbal := by simp

namespace Datum

theorem plane2_w_zero (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : (plane2 v u hv hu).w 0 = 2 := by
  simp [w, plane2, hv]

theorem plane2_w_one (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : (plane2 v u hv hu).w 1 = 1 := by
  simp [w, plane2]

theorem plane2_d (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) : (plane2 v u hv hu).d = 3 := by
  simp [d, Fin.sum_univ_two, plane2_w_zero v u hv hu, plane2_w_one v u hv hu]

/-- `𝖣 = (z + 1)²(z + ½)` for the plane 2 datum. -/
theorem plane2_Dpoly (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    (plane2 v u hv hu).Dpoly = (X + 1) ^ 2 * (X + C (1 / 2 : ℚ)) := by
  simp [Dpoly, Fin.prod_univ_two, plane2_w_zero v u hv hu, plane2_w_one v u hv hu, plane2]

/-- `A = -(v + u/2) z - (v + u)/2` for the plane 2 datum. -/
theorem plane2_Apoly (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) :
    (plane2 v u hv hu).Apoly = C (-((v : ℚ) + u / 2)) * X - C (((v : ℚ) + u) / 2) := by
  simp only [Apoly, Dexc, Fin.sum_univ_two, plane2_w_zero v u hv hu, plane2_w_one v u hv hu, plane2]
  have e0 : (univ.erase (0 : Fin 2)) = {1} := by decide
  have e1 : (univ.erase (1 : Fin 2)) = {0} := by decide
  simp only [Apoly, Dexc, Fin.sum_univ_two, e0, e1, Finset.prod_singleton, plane2_w_zero v u hv hu,
    plane2_w_one v u hv hu]
  simp [plane2]
  have h2 : (2 : ℚ[X]) * C (2⁻¹ : ℚ) = 1 := by
    rw [← map_ofNat C 2, ← C_mul]; norm_num
  have hu2 : C ((u : ℚ) / 2) = (u : ℚ[X]) * C (2⁻¹ : ℚ) := by
    rw [div_eq_mul_inv, C_mul]; simp
  have hvu2 : C (((v : ℚ) + u) / 2) = ((v : ℚ[X]) + u) * C (2⁻¹ : ℚ) := by
    rw [div_eq_mul_inv, C_mul]; simp
  rw [hu2, hvu2]
  linear_combination ((u : ℚ[X]) * (X + 1)) * h2
end Datum
end CatalanCore.Uniform.Support
