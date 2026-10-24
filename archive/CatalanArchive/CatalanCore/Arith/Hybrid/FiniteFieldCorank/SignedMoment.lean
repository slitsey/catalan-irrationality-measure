module

public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.JetGeometry
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.Interpolant
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.KernelSpace

@[expose] public section

open Polynomial Matrix Module Finset

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k] {ell n : ℕ}

noncomputable def pencilWeight (J : JetGeometry k ell n) (D R : k[X]) (z : k) (a : k) : k :=
  if a ∈ J.low then -z * R.eval a / (D.derivative.eval a) ^ 2
  else J.eps a * R.eval a / (D.eval a) ^ 2

/-- The complete-field interpolation identity proves corank three for the actual
signed moment pencil. All geometry assumptions concern finite support data. -/
theorem signed_moment_corank
    [CharP k ell] [Fact ell.Prime]
    (J : JetGeometry k ell n) (hn : 3 ≤ n) (hnell : n < ell)
    (D E R Cc : k[X])
    (hdisj : Disjoint J.low J.high)
    (hJ : rootProduct (J.low ∪ J.high) = D * E)
    (hfull : D * E * R * Cc = X ^ ell - X)
    (hD : ∀ a ∈ J.low, D.eval a = 0)
    (hE : ∀ a ∈ J.high, E.eval a = 0)
    (hC : ∀ a ∈ J.tail, Cc.eval a = 0)
    (hbudget : 2 * D.natDegree + Cc.natDegree + (J.low ∪ J.high).card ≤ ell + 2 * n)
    (h2 : (2 : k) ≠ 0) (z : k) :
    finrank k (LinearMap.ker
      (momentMatrix (J.low ∪ J.high) (pencilWeight J D R z) n).mulVecLin) ≤ 3 := by
  classical
  let s := J.low ∪ J.high
  let w := pencilWeight J D R z
  let M := momentMatrix s w n
  let V := kernelPolynomialSpace M
  letI : FiniteDimensional k V := by dsimp [V]; infer_instance
  let F : V →ₗ[k] k[X] :=
    (scaledNumeratorLinear D Cc s w).comp V.subtype
  have hPdeg : ∀ P : V, (P : k[X]).natDegree ≤ n - 1 := by
    intro P
    have hh := kernelPolynomialSpace_degree M (by omega : 1 ≤ n) P
    omega
  have hFdeg : ∀ P : V, (F P).natDegree ≤ ell + n - 1 := by
    intro P
    have hm : ∀ j < n, ∑ a ∈ s, (w a * (P : k[X]).eval a) * a ^ j = 0 := by
      intro j hj
      exact kernelPolynomialSpace_moments s w P j hj
    have hb := natDegree_numerator_le_of_moments s (fun a => w a * (P : k[X]).eval a) n hm
    have hc : n < s.card := by
      dsimp [s]
      rw [Finset.card_union_of_disjoint hdisj]
      have hl := J.low_card
      have hh := J.high_card
      omega
    have ht : (F P).natDegree ≤
        2 * D.natDegree + Cc.natDegree + (numerator s (fun a => w a * (P : k[X]).eval a)).natDegree := by
      change (D ^ 2 * Cc * numerator s (fun a => w a * (P : k[X]).eval a)).natDegree ≤ _
      have h1 := natDegree_mul_le (p := D ^ 2 * Cc)
        (q := numerator s (fun a => w a * (P : k[X]).eval a))
      have h2' := natDegree_mul_le (p := D ^ 2) (q := Cc)
      simp only [natDegree_pow] at h2'
      omega
    change 2 * D.natDegree + Cc.natDegree + s.card ≤ ell + 2 * n at hbudget
    omega
  have hell : (ell : k) = 0 := (CharP.cast_eq_zero_iff k ell ell).2 dvd_rfl
  have huL : ∀ a ∈ J.low,
      D.derivative.eval a * E.eval a * R.eval a * Cc.eval a = -1 := by
    intro a ha
    have he := congrArg (fun P : k[X] => P.derivative.eval a) hfull
    simpa [derivative_mul, derivative_sub, derivative_X_pow, hD a ha, hell] using he
  have huH : ∀ a ∈ J.high,
      D.eval a * E.derivative.eval a * R.eval a * Cc.eval a = -1 := by
    intro a ha
    have he := congrArg (fun P : k[X] => P.derivative.eval a) hfull
    simpa [derivative_mul, derivative_sub, derivative_X_pow, hE a ha, hell] using he
  have hfin := J.finrank_le_three hn hnell V F z hPdeg hFdeg h2
    (fun P a ha => scaledNumerator_eval_low D Cc s w P a (hD a ha))
    (fun P a ha => scaledNumerator_derivative_eval_low D Cc s w P a (hD a ha))
    (fun P a ha => scaledNumerator_second_eval_low D E R Cc s w P a z
      (Finset.mem_union_left _ ha) hJ (hD a ha)
      (by simp [w, pencilWeight, ha]) (huL a ha))
    (fun P a ha => scaledNumerator_eval_high D E R Cc s w P a (J.eps a)
      (Finset.mem_union_right _ ha) hJ (hE a ha)
      (by have hnl : a ∉ J.low := fun hl => Finset.disjoint_left.1 hdisj hl ha
          simp [w, pencilWeight, hnl]) (huH a ha))
    (fun P a ha => scaledNumerator_eval_tail D Cc s w P a (hC a ha))
  rw [finrank_kernelPolynomialSpace] at hfin
  exact hfin

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
