module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.Moments

@[expose] public section

open Polynomial Finset

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k]

/-- The polynomial used in the complete-field corank proof. -/
noncomputable def scaledNumeratorLinear (D Cc : k[X]) (s : Finset k) (w : k → k) :
    k[X] →ₗ[k] k[X] where
  toFun P := D ^ 2 * Cc * numeratorLinear s w P
  map_add' P Q := by simp [map_add, mul_add]
  map_smul' c P := by
    rw [map_smul]
    simp only [smul_eq_C_mul, RingHom.id_apply]
    ring

lemma scaledNumerator_eval_low (D Cc : k[X]) (s : Finset k) (w : k → k)
    (P : k[X]) (u : k) (hD : D.eval u = 0) :
    (scaledNumeratorLinear D Cc s w P).eval u = 0 := by
  simp [scaledNumeratorLinear, hD]

lemma scaledNumerator_derivative_eval_low (D Cc : k[X]) (s : Finset k) (w : k → k)
    (P : k[X]) (u : k) (hD : D.eval u = 0) :
    (scaledNumeratorLinear D Cc s w P).derivative.eval u = 0 := by
  simp [scaledNumeratorLinear, derivative_mul, derivative_pow, hD]

lemma scaledNumerator_second_eval_low (D E R Cc : k[X]) (s : Finset k)
    (w : k → k) (P : k[X]) (u z : k) (hu : u ∈ s)
    (hJ : rootProduct s = D * E) (hD : D.eval u = 0)
    (hw : w u = -z * R.eval u / (D.derivative.eval u) ^ 2)
    (hunit : D.derivative.eval u * E.eval u * R.eval u * Cc.eval u = -1) :
    (scaledNumeratorLinear D Cc s w P).derivative.derivative.eval u =
      2 * z * P.eval u := by
  have hd : D.derivative.eval u ≠ 0 := by
    intro h
    simp [h] at hunit
  have hB : (numeratorLinear s w P).eval u =
      (-z * R.eval u / (D.derivative.eval u) ^ 2) * P.eval u *
        (D.derivative.eval u * E.eval u) := by
    change (numerator s (fun a => w a * P.eval a)).eval u = _
    rw [eval_numerator s _ hu, hJ, derivative_mul]
    simp [hw, hD]
  have he : (scaledNumeratorLinear D Cc s w P).derivative.derivative.eval u =
      2 * (D.derivative.eval u) ^ 2 * Cc.eval u * (numeratorLinear s w P).eval u := by
    simp [scaledNumeratorLinear, derivative_mul, derivative_pow, hD]
    ring_nf
    simp
  rw [he, hB]
  calc
    _ = -2 * z * P.eval u *
        (D.derivative.eval u * E.eval u * R.eval u * Cc.eval u) := by
      field_simp <;> ring
    _ = _ := by rw [hunit]; ring

lemma scaledNumerator_eval_high (D E R Cc : k[X]) (s : Finset k)
    (w : k → k) (P : k[X]) (u e : k) (hu : u ∈ s)
    (hJ : rootProduct s = D * E) (hE : E.eval u = 0)
    (hw : w u = e * R.eval u / (D.eval u) ^ 2)
    (hunit : D.eval u * E.derivative.eval u * R.eval u * Cc.eval u = -1) :
    (scaledNumeratorLinear D Cc s w P).eval u = -e * P.eval u := by
  have hd : D.eval u ≠ 0 := by intro h; simp [h] at hunit
  have hB : (numeratorLinear s w P).eval u =
      (e * R.eval u / (D.eval u) ^ 2) * P.eval u *
        (D.eval u * E.derivative.eval u) := by
    change (numerator s (fun a => w a * P.eval a)).eval u = _
    rw [eval_numerator s _ hu, hJ, derivative_mul]
    simp [hw, hE]
  change (D ^ 2 * Cc * numeratorLinear s w P).eval u = _
  rw [eval_mul, eval_mul, eval_pow, hB]
  calc
    _ = e * P.eval u * (D.eval u * E.derivative.eval u * R.eval u * Cc.eval u) := by
      field_simp <;> ring
    _ = _ := by rw [hunit]; ring

lemma scaledNumerator_eval_tail (D Cc : k[X]) (s : Finset k) (w : k → k)
    (P : k[X]) (u : k) (hC : Cc.eval u = 0) :
    (scaledNumeratorLinear D Cc s w P).eval u = 0 := by
  simp [scaledNumeratorLinear, hC]

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
