module

public import CatalanCore.Arith.Hybrid.LemmaE.Cong

@[expose] public section

/-!
# Congruence of determinants and adjugates of integral polynomial matrices
-/

open Polynomial Finset Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

variable {p : ℕ} [Fact p.Prime]

lemma gn_zsmul_le (n : ℤ) (f : ℚ[X]) : gn p (n • f) ≤ gn p f := by
  have : n • f = C (n : ℚ) * f := by simp [zsmul_eq_mul]
  rw [this, gn_mul, gn_C]
  have h : (padicNorm p (n : ℚ) : ℝ) ≤ 1 := by exact_mod_cast padicNorm.of_int n
  calc _ ≤ 1 * gn p f := mul_le_mul_of_nonneg_right h (gn_nonneg p f)
    _ = gn p f := one_mul _

lemma Int1.zsmul {f : ℚ[X]} (hf : Int1 p f) (n : ℤ) : Int1 p (n • f) :=
  (gn_zsmul_le n f).trans hf

lemma Cng.zsmul {f f' : ℚ[X]} (h : Cng p f f') (n : ℤ) : Cng p (n • f) (n • f') := by
  unfold Cng at *
  rw [← smul_sub]
  exact lt_of_le_of_lt (gn_zsmul_le n _) h

section Det

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem det_int1 {M : Matrix n n ℚ[X]} (h : ∀ i j, Int1 p (M i j)) : Int1 p M.det := by
  rw [Matrix.det_apply]
  apply Int1.sum
  intro σ _
  rw [Units.smul_def]
  exact (Int1.prod fun i _ => h (σ i) i).zsmul _

/-- Congruent integral matrices have congruent determinants. -/
theorem det_cng {M M' : Matrix n n ℚ[X]} (h : ∀ i j, Int1 p (M i j))
    (h' : ∀ i j, Int1 p (M' i j)) (hc : ∀ i j, Cng p (M i j) (M' i j)) :
    Cng p M.det M'.det := by
  rw [Matrix.det_apply, Matrix.det_apply]
  apply Cng.sum
  intro σ _
  rw [Units.smul_def, Units.smul_def]
  exact (Cng.prod (fun i _ => h (σ i) i) (fun i _ => h' (σ i) i) fun i _ => hc (σ i) i).zsmul _

/-- Congruent integral matrices have congruent adjugates. -/
theorem adj_cng {M M' : Matrix n n ℚ[X]} (h : ∀ i j, Int1 p (M i j))
    (h' : ∀ i j, Int1 p (M' i j)) (hc : ∀ i j, Cng p (M i j) (M' i j)) (i j : n) :
    Cng p (M.adjugate i j) (M'.adjugate i j) := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  have key : ∀ (N : Matrix n n ℚ[X]) (k l : n), Int1 p (N.updateRow j (Pi.single i 1) k l) →
      True := fun _ _ _ _ => trivial
  apply det_cng
  · intro k l
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      by_cases hl : i = l
      · subst hl; simp [Int1.one]
      · simp [Pi.single_apply, hl, Int1.zero]
    · simpa [Matrix.updateRow_ne hk] using h k l
  · intro k l
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      by_cases hl : i = l
      · subst hl; simp [Int1.one]
      · simp [Pi.single_apply, hl, Int1.zero]
    · simpa [Matrix.updateRow_ne hk] using h' k l
  · intro k l
    by_cases hk : k = j
    · subst hk
      simp only [Matrix.updateRow_self]
      exact Cng.refl _
    · simpa [Matrix.updateRow_ne hk] using hc k l


/-- Adjugate entries of integral matrices are integral. -/
theorem adj_int1 {M : Matrix n n ℚ[X]} (h : ∀ i j, Int1 p (M i j)) (i j : n) :
    Int1 p (M.adjugate i j) := by
  rw [Matrix.adjugate_apply]
  apply det_int1
  intro k l
  by_cases hk : k = j
  · subst hk
    simp only [Matrix.updateRow_self]
    by_cases hl : i = l
    · subst hl; simp [Int1.one]
    · simp [hl, Int1.zero]
  · simpa [Matrix.updateRow_ne hk] using h k l

end Det

end CatalanCore.Arith.Hybrid.LemmaE
