module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic

@[expose] public section
namespace CatalanMeasure.GenD.Analytic.GaussianHorner
open Polynomial
noncomputable section

def plus (a b : ℤ × ℤ) : ℤ × ℤ := (a.1 + b.1, a.2 + b.2)
def times (a b : ℤ × ℤ) : ℤ × ℤ :=
  (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def castPair (a : ℤ × ℤ) : ℂ := ⟨(a.1 : ℝ), (a.2 : ℝ)⟩

theorem castPair_plus (a b : ℤ × ℤ) : castPair (plus a b) = castPair a + castPair b := by
  apply Complex.ext <;> simp [castPair, plus]

theorem castPair_times (a b : ℤ × ℤ) : castPair (times a b) = castPair a * castPair b := by
  apply Complex.ext <;> simp [castPair, times, Complex.mul_re, Complex.mul_im]

theorem castPair_real (a : ℤ) : castPair (a, 0) = (a : ℂ) := by
  apply Complex.ext <;> simp [castPair]

def valueStep (c : ℤ × ℤ) (q : ℤ) (state : (ℤ × ℤ) × ℤ) (a : ℤ) : (ℤ × ℤ) × ℤ :=
  (plus (times c state.1) (a * state.2, 0), state.2 * q)

/-- One general homogeneous-Horner invariant, shared by point evaluation and
the coefficient translation tower. No numerical computation is trusted. -/
theorem homogeneous_fold_invariant {S : Type*} (step : S → ℤ → S)
    (value : S → ℂ) (power : S → ℤ) {q : ℤ} (hq : q ≠ 0) (c : ℂ)
    (hv : ∀ s a, value (step s a) = c * value s + (a : ℂ) * (power s : ℂ))
    (hp : ∀ s a, power (step s a) = power s * q)
    (as : List ℤ) (s : S) (H : ℂ) (h : value s * (q : ℂ) = (power s : ℂ) * H) :
    value (as.foldl step s) * (q : ℂ) = (power (as.foldl step s) : ℂ) *
      as.foldl (fun (v : ℂ) (a : ℤ) => c / (q : ℂ) * v + (a : ℂ)) H := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  induction as generalizing s H with
  | nil => simpa only [List.foldl_nil] using h
  | cons a as ih =>
    simp only [List.foldl_cons]
    apply ih
    rw [hv, hp, Int.cast_mul]
    calc
      (c * value s + (a : ℂ) * (power s : ℂ)) * (q : ℂ) =
          c * (value s * (q : ℂ)) + (power s : ℂ) * (q : ℂ) * (a : ℂ) := by ring
      _ = c * ((power s : ℂ) * H) + (power s : ℂ) * (q : ℂ) * (a : ℂ) := by rw [h]
      _ = _ := by field_simp [hqC] <;> ring

theorem fold_power {S : Type*} (step : S → ℤ → S) (power : S → ℤ) (q : ℤ)
    (hp : ∀ s a, power (step s a) = power s * q) (as : List ℤ) (s : S) :
    power (as.foldl step s) = power s * q ^ as.length := by
  induction as generalizing s with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, List.length_cons, ih, hp, pow_succ]
    ring

theorem point_value_sound (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0) (as : List ℤ) :
    castPair (as.foldl (valueStep c q) ((0, 0), 1)).1 * (q : ℂ) =
      (q : ℂ) ^ as.length *
        as.foldl (fun (v : ℂ) (a : ℤ) => castPair c / (q : ℂ) * v + (a : ℂ)) 0 := by
  have hv : ∀ s a, castPair (valueStep c q s a).1 =
      castPair c * castPair s.1 + (a : ℂ) * (s.2 : ℂ) := by
    intro s a
    simp only [valueStep, castPair_plus, castPair_times, castPair_real, Int.cast_mul]
  have hp : ∀ s a, (valueStep c q s a).2 = s.2 * q := fun _ _ => rfl
  have ht := homogeneous_fold_invariant (valueStep c q) (fun s => castPair s.1)
    (fun s => s.2) hq (castPair c) hv hp as ((0, 0), 1) 0 (by rw [castPair_real]; simp)
  have hpower := fold_power (valueStep c q) (fun s => s.2) q hp as ((0, 0), 1)
  rw [hpower, one_mul, Int.cast_pow] at ht
  exact ht

def evalPairs : List (ℤ × ℤ) → ℂ → ℂ
  | [], _ => 0
  | a :: as, z => castPair a + z * evalPairs as z

theorem evalPairs_append_zero (as : List (ℤ × ℤ)) (z : ℂ) :
    evalPairs (as ++ [(0, 0)]) z = evalPairs as z := by
  induction as with
  | nil => simp [evalPairs, castPair_real]
  | cons a as ih => simp [evalPairs, ih]

theorem evalPairs_zip_linear (as bs : List (ℤ × ℤ))
    (hlen : as.length = bs.length) (c : ℤ × ℤ) (z : ℂ) :
    evalPairs ((as.zip bs).map (fun vw => plus vw.1 (times c vw.2))) z =
      evalPairs as z + castPair c * evalPairs bs z := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp_all [evalPairs]
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlen' : as.length = bs.length := by simpa using hlen
      simp only [List.zip_cons_cons, List.map_cons, evalPairs, castPair_plus, castPair_times]
      rw [ih bs hlen']
      ring

theorem evalPairs_modifyHead_add (as : List (ℤ × ℤ)) (hne : as ≠ []) (a : ℤ) (z : ℂ) :
    evalPairs (as.modifyHead (fun v => plus v (a, 0))) z = evalPairs as z + (a : ℂ) := by
  cases as with
  | nil => contradiction
  | cons b bs =>
    simp only [List.modifyHead_cons, evalPairs, castPair_plus, castPair_real]
    ring

def shiftStep (c : ℤ × ℤ) (q : ℤ) (state : List (ℤ × ℤ) × ℤ) (a : ℤ) :
    List (ℤ × ℤ) × ℤ :=
  let shifted := (((0, 0)::state.1).zip (state.1++[(0, 0)])).map
    (fun vw => plus vw.1 (times c vw.2))
  (shifted.modifyHead (fun v => plus v (a * state.2, 0)), state.2 * q)

theorem evalPairs_shiftStep (c : ℤ × ℤ) (q : ℤ) (state : List (ℤ × ℤ) × ℤ)
    (a : ℤ) (z : ℂ) :
    evalPairs (shiftStep c q state a).1 z =
      (z + castPair c) * evalPairs state.1 z + (a : ℂ) * (state.2 : ℂ) := by
  let shifted := (((0, 0)::state.1).zip (state.1++[(0, 0)])).map
    (fun vw => plus vw.1 (times c vw.2))
  have hlen : ((0, 0)::state.1).length = (state.1++[(0, 0)]).length := by simp
  have hnonempty : shifted ≠ [] := by
    intro he
    have ht := congrArg List.length he
    simp [shifted] at ht
  change evalPairs (shifted.modifyHead (fun v => plus v (a * state.2, 0))) z = _
  rw [evalPairs_modifyHead_add shifted hnonempty]
  change evalPairs (((((0, 0)::state.1).zip (state.1++[(0, 0)])).map
    (fun vw => plus vw.1 (times c vw.2)))) z + ((a * state.2 : ℤ) : ℂ) = _
  rw [evalPairs_zip_linear _ _ hlen c z, evalPairs_append_zero]
  simp only [evalPairs, castPair_real, Int.cast_zero, zero_add, Int.cast_mul]
  ring

/-- Every checked translated coefficient list denotes exactly the translated
polynomial value, for all complex evaluation variables simultaneously. -/
theorem translation_value_sound (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0)
    (as : List ℤ) (z : ℂ) :
    evalPairs (as.foldl (shiftStep c q) ([], 1)).1 z * (q : ℂ) =
      (q : ℂ) ^ as.length *
        as.foldl (fun (v : ℂ) (a : ℤ) => (z + castPair c) / (q : ℂ) * v + (a : ℂ)) 0 := by
  have hv : ∀ state a, evalPairs (shiftStep c q state a).1 z =
      (z + castPair c) * evalPairs state.1 z + (a : ℂ) * (state.2 : ℂ) :=
    fun state a => evalPairs_shiftStep c q state a z
  have hp : ∀ state a, (shiftStep c q state a).2 = state.2 * q := fun _ _ => rfl
  have ht := homogeneous_fold_invariant (shiftStep c q) (fun state => evalPairs state.1 z)
    (fun state => state.2) hq (z + castPair c) hv hp as ([], 1) 0 (by simp [evalPairs])
  have hpower := fold_power (shiftStep c q) (fun state => state.2) q hp as ([], 1)
  rw [hpower, one_mul, Int.cast_pow] at ht
  exact ht

def polynomialOfPairs : List (ℤ × ℤ) → ℂ[X]
  | [] => 0
  | a :: as => Polynomial.C (castPair a) + Polynomial.X * polynomialOfPairs as

theorem polynomialOfPairs_eval (as : List (ℤ × ℤ)) (z : ℂ) :
    (polynomialOfPairs as).eval z = evalPairs as z := by
  induction as with
  | nil => simp [polynomialOfPairs, evalPairs]
  | cons a as ih => simp [polynomialOfPairs, evalPairs, ih]

def normHorner : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: as, r => a + r * normHorner as r

theorem evalPairs_norm_le {as : List (ℤ × ℤ)} {U : List ℝ}
    (h : List.Forall₂ (fun a u => ‖castPair a‖ ≤ u) as U) {r : ℝ}
    (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) : ‖evalPairs as z‖ ≤ normHorner U r := by
  induction h with
  | nil => simp [evalPairs, normHorner]
  | @cons a u as U ha h ih =>
    simp only [evalPairs, normHorner]
    calc
      _ ≤ ‖castPair a‖ + ‖z‖ * ‖evalPairs as z‖ := by
        simpa only [norm_mul] using norm_add_le (castPair a) (z * evalPairs as z)
      _ ≤ u + r * normHorner U r :=
        add_le_add ha (mul_le_mul hz ih (norm_nonneg _) hr)

def weightedPairs : ℤ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | _, [] => []
  | n, a :: as => times (n, 0) a :: weightedPairs (n + 1) as

theorem polynomialOfPairs_weighted (n : ℤ) (as : List (ℤ × ℤ)) :
    polynomialOfPairs (weightedPairs n as) =
      Polynomial.C (n : ℂ) * polynomialOfPairs as + Polynomial.X * (polynomialOfPairs as).derivative := by
  induction as generalizing n with
  | nil => simp [weightedPairs, polynomialOfPairs]
  | cons a as ih =>
    simp only [weightedPairs, polynomialOfPairs, castPair_times, castPair_real,
      Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
      Polynomial.derivative_X, zero_add, one_mul]
    rw [ih]
    push_cast
    simp only [map_mul, map_add, map_one]
    ring

theorem polynomialOfPairs_derivative (as : List (ℤ × ℤ)) :
    (polynomialOfPairs as).derivative = polynomialOfPairs (weightedPairs 1 as.tail) := by
  cases as with
  | nil => simp [polynomialOfPairs, weightedPairs]
  | cons a as =>
    simpa [polynomialOfPairs] using (polynomialOfPairs_weighted 1 as).symm

theorem polynomialOfPairs_derivative_norm_le {as : List (ℤ × ℤ)} {U : List ℝ}
    (h : List.Forall₂ (fun a u => ‖castPair a‖ ≤ u) (weightedPairs 1 as.tail) U)
    {r : ℝ} (hr : 0 ≤ r) (z : ℂ) (hz : ‖z‖ ≤ r) :
    ‖(polynomialOfPairs as).derivative.eval z‖ ≤ normHorner U r := by
  rw [polynomialOfPairs_derivative, polynomialOfPairs_eval]
  exact evalPairs_norm_le h hr z hz

def scaleIntCoefficients : ℤ → ℤ → List ℤ → List ℤ
  | _, _, [] => []
  | c, r, a :: as => c * a :: scaleIntCoefficients (c * r) r as

theorem evalPairs_scaleIntCoefficients (c r : ℤ) (as : List ℤ) (z : ℂ) :
    evalPairs ((scaleIntCoefficients c r as).map (fun a => (a, 0))) z =
      (c : ℂ) * evalPairs (as.map (fun a => (a, 0))) ((r : ℂ) * z) := by
  induction as generalizing c with
  | nil => simp [scaleIntCoefficients, evalPairs]
  | cons a as ih =>
    simp only [scaleIntCoefficients, List.map_cons, evalPairs, castPair_real]
    rw [ih]
    push_cast
    ring

theorem reverse_fold_horner (as : List ℤ) (z : ℂ) :
    as.reverse.foldl (fun (v : ℂ) (a : ℤ) => z * v + (a : ℂ)) 0 =
      evalPairs (as.map (fun a => (a, 0))) z := by
  induction as with
  | nil => simp [evalPairs]
  | cons a as ih =>
    simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.map_cons, evalPairs, castPair_real]
    rw [ih]
    ring

theorem point_value_polynomial_sound (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0) (as : List ℤ) :
    castPair (as.reverse.foldl (valueStep c q) ((0, 0), 1)).1 * (q : ℂ) =
      (q : ℂ) ^ as.length *
        (polynomialOfPairs (as.map (fun a => (a, 0)))).eval (castPair c / (q : ℂ)) := by
  have ht := point_value_sound c hq as.reverse
  simpa only [List.length_reverse, reverse_fold_horner, polynomialOfPairs_eval] using ht

theorem translation_polynomial_value_sound (c : ℤ × ℤ) {q : ℤ} (hq : q ≠ 0)
    (as : List ℤ) (z : ℂ) :
    (polynomialOfPairs (as.reverse.foldl (shiftStep c q) ([], 1)).1).eval z * (q : ℂ) =
      (q : ℂ) ^ as.length *
        (polynomialOfPairs (as.map (fun a => (a, 0)))).eval ((z + castPair c) / (q : ℂ)) := by
  have ht := translation_value_sound c hq as.reverse z
  simpa only [List.length_reverse, reverse_fold_horner, polynomialOfPairs_eval] using ht

end
end CatalanMeasure.GenD.Analytic.GaussianHorner
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_plus
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_times
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.castPair_real
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.homogeneous_fold_invariant
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.fold_power
#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.point_value_sound

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_append_zero

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_zip_linear

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_modifyHead_add

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_shiftStep

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.translation_value_sound

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.polynomialOfPairs_eval

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_norm_le

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.polynomialOfPairs_weighted

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.polynomialOfPairs_derivative

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.polynomialOfPairs_derivative_norm_le

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.evalPairs_scaleIntCoefficients

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.reverse_fold_horner

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.point_value_polynomial_sound

#print axioms CatalanMeasure.GenD.Analytic.GaussianHorner.translation_polynomial_value_sound
