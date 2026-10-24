module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.RootFactor
public import CatalanArchive.CatalanCore.Polynomial.ShiftRatio

@[expose] public section

open Polynomial Finset Module

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k] {ell n : ℕ}

/-- Only finite support geometry is needed by the three-constraint corank proof. -/
structure JetGeometry (k : Type*) [Field k] (ell n : ℕ) where
  low : Finset k
  high : Finset k
  lowAdj : Finset k
  highAdj : Finset k
  tail : Finset k
  jump : k
  eps : k → k
  low_card : n ≤ low.card
  high_card : n ≤ high.card
  low_frob : ∀ a ∈ low, a ^ ell = a
  high_unit : ∀ a ∈ high, eps a ≠ 0
  low_adj : ∀ a ∈ lowAdj, a ∈ low ∧ a + 1 ∈ low
  high_adj : ∀ a ∈ highAdj, a ∈ high ∧ a + 1 ∈ high ∧ eps a = eps (a + 1)
  tail_adj : ∀ a ∈ tail, a + 1 ∈ tail ∨ a + 1 ∈ low
  disj_lh : Disjoint lowAdj highAdj
  disj_lt : Disjoint lowAdj tail
  disj_ht : Disjoint highAdj tail
  degree_count : 3 * lowAdj.card + highAdj.card + tail.card = ell + 2 * n - 5
  jump_l : jump ∉ lowAdj
  jump_h : jump ∉ highAdj
  jump_t : jump ∉ tail
  jump_high : jump ∈ high
  jump_succ_high : jump + 1 ∈ high

noncomputable def JetGeometry.factor (J : JetGeometry k ell n) : k[X] :=
  (rootProduct J.lowAdj) ^ 3 * rootProduct J.highAdj * rootProduct J.tail

lemma JetGeometry.factor_degree (J : JetGeometry k ell n) :
    J.factor.natDegree = ell + 2 * n - 5 := by
  have hL := (rootProduct_monic J.lowAdj).pow 3
  have hH := rootProduct_monic J.highAdj
  have hT := rootProduct_monic J.tail
  rw [JetGeometry.factor, natDegree_mul (hL.mul hH).ne_zero hT.ne_zero,
    natDegree_mul hL.ne_zero hH.ne_zero, natDegree_pow,
    natDegree_rootProduct, natDegree_rootProduct, natDegree_rootProduct]
  have hc := J.degree_count
  omega

lemma JetGeometry.factor_eval (J : JetGeometry k ell n) : J.factor.eval J.jump ≠ 0 := by
  simp only [JetGeometry.factor, eval_mul, eval_pow]
  exact mul_ne_zero (mul_ne_zero
    (pow_ne_zero _ (rootProduct_eval_ne_zero J.lowAdj J.jump J.jump_l))
    (rootProduct_eval_ne_zero J.highAdj J.jump J.jump_h))
    (rootProduct_eval_ne_zero J.tail J.jump J.jump_t)

/-- A finite support jet configuration gives a uniform dimension bound three. -/
theorem JetGeometry.finrank_le_three
    [CharP k ell] [Fact ell.Prime]
    (J : JetGeometry k ell n) (hn : 3 ≤ n) (hnell : n < ell)
    (V : Submodule k k[X]) [FiniteDimensional k V]
    (F : V →ₗ[k] k[X]) (z : k)
    (hP : ∀ P : V, (P : k[X]).natDegree ≤ n - 1)
    (hF : ∀ P : V, (F P).natDegree ≤ ell + n - 1)
    (h2 : (2 : k) ≠ 0)
    (hL0 : ∀ P : V, ∀ a ∈ J.low, (F P).eval a = 0)
    (hL1 : ∀ P : V, ∀ a ∈ J.low, (F P).derivative.eval a = 0)
    (hL2 : ∀ P : V, ∀ a ∈ J.low,
      (F P).derivative.derivative.eval a = 2 * z * (P : k[X]).eval a)
    (hH : ∀ P : V, ∀ a ∈ J.high,
      (F P).eval a = -J.eps a * (P : k[X]).eval a)
    (hT : ∀ P : V, ∀ a ∈ J.tail, (F P).eval a = 0) :
    finrank k V ≤ 3 := by
  classical
  have hdiv : ∀ P : V, J.factor ∣ wronskian (F P) P := by
    intro P
    let W := wronskian (F P) (P : k[X])
    have hLd : (rootProduct J.lowAdj) ^ 3 ∣ W := by
      apply rootProduct_pow_dvd
      intro a ha
      have hla := J.low_adj a ha
      have hj := wronskian_jets (F P) P a z
        (hL0 P a hla.1) (hL0 P _ hla.2)
        (hL1 P a hla.1) (hL1 P _ hla.2)
        (hL2 P a hla.1) (hL2 P _ hla.2)
      exact cube_dvd_of_jets W a h2 hj.1 hj.2.1 hj.2.2
    have hHd : rootProduct J.highAdj ∣ W := by
      have h := rootProduct_pow_dvd J.highAdj 1 W (by
        intro a ha
        rw [pow_one, dvd_iff_isRoot]
        have hha := J.high_adj a ha
        apply wronskian_eval_of_same_values (F P) P a (-J.eps a)
        · exact hH P a hha.1
        · simpa [hha.2.2] using hH P _ hha.2.1)
      simpa using h
    have hTd : rootProduct J.tail ∣ W := by
      have h := rootProduct_pow_dvd J.tail 1 W (by
        intro a ha
        rw [pow_one, dvd_iff_isRoot]
        rw [IsRoot, eval_wronskian, hT P a ha]
        have hs : (F P).eval (a + 1) = 0 := by
          rcases J.tail_adj a ha with ht | hl
          · exact hT P _ ht
          · exact hL0 P _ hl
        simp [hs])
      simpa using h
    exact ((rootProducts_isCoprime J.lowAdj J.tail J.disj_lt).pow_left.mul_left
      (rootProducts_isCoprime J.highAdj J.tail J.disj_ht)).mul_dvd
      (((rootProducts_isCoprime J.lowAdj J.highAdj J.disj_lh).pow_left).mul_dvd hLd hHd) hTd
  have hrigid : ∀ P : V, P ≠ 0 → wronskian (F P) P ≠ 0 := by
    intro P hP0
    have hp0 : (P : k[X]) ≠ 0 := by
      intro h
      apply hP0
      exact Subtype.ext h
    have hpdeg : (P : k[X]).natDegree < n := by have := hP P; omega
    have hu : ∃ a ∈ J.low, (P : k[X]).eval a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ J.low h
        (hpdeg.trans_le J.low_card))
    obtain ⟨a, ha, hPa⟩ := hu
    have hf0 : F P ≠ 0 := by
      intro hz
      apply hp0
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ J.high
      · intro b hb
        have he := hH P b hb
        rw [hz, eval_zero] at he
        exact (mul_eq_zero.mp he.symm).resolve_left (neg_ne_zero.mpr (J.high_unit b hb))
      · exact hpdeg.trans_le J.high_card
    exact CatalanCore.PolynomialShift.cross_shift_ne_zero (F P) P hp0 hf0
      (hpdeg.trans hnell) (by have := hF P; omega)
      a (J.low_frob a ha) hPa (hL0 P a ha) (hL1 P a ha)
  apply CatalanCore.Arith.Hybrid.FiniteFieldCorank.finrank_le_three V F ell n hn J.jump J.factor hP hF J.factor_degree J.factor_eval hdiv
  · intro P he
    rw [eval_wronskian, hH P _ J.jump_succ_high, hH P _ J.jump_high, he]
    simp
  · exact hrigid

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
