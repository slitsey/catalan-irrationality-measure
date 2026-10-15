module
public import CatalanMeasure.Parametric.SecondaryTentRowCancellation
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial
noncomputable section

/-- A sharper ordinary degree bound records the input's actual cap. -/
theorem secondaryTent_rowInput_natDegree_le {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (n m : ℕ) (I : K[X])
    (hmn : m ≤ n) (hI : I.natDegree ≤ m) :
    (secondaryTentRowInput n I).natDegree ≤ n+m := by
  rw [secondaryTent_rowInput_padding h2 m n I hmn hI]
  have hmul := natDegree_mul_le
    (p := (2*X : K[X])^(n-m)) (q := secondaryTentRowInput m I)
  have hB : (2*X : K[X]).natDegree ≤ 1 := by
    simpa using (natDegree_mul_le (p := (2 : K[X])) (q := X)).trans
      (by simpa using (natDegree_X_le (R := K)))
  have hpow := natDegree_pow_le_of_le (n-m) hB
  have ht := secondaryTent_rowInput_natDegree m I
  omega

/-- The three denominator-free `t` channels after collecting their scalar
input combinations. Only the `z²` channel needs the shared infinity cap. -/
def secondaryTentRowRegularNumerator {K : Type*} [CommSemiring K]
    (p n : ℕ) (S₀ S₁ S₂ : K[X]) : K[X] :=
  secondaryTentRowInput n S₀ + X^p * secondaryTentRowInput n S₁ +
    X^(2*p) * secondaryTentRowInput n S₂

/-- One input cap suffices for both natural source numerators: it acts on
the single collected `z²` channel rather than imposing two degree flags. -/
theorem secondaryTent_row_regular_shared_cap {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (p n m : ℕ) (S₀ S₁ S₂ : K[X])
    (hnp : n+1=p) (hmn : m ≤ n) (hS₂ : S₂.natDegree ≤ m) :
    (secondaryTentRowRegularNumerator p n S₀ S₁ S₂).natDegree ≤ 2*p+n+m := by
  have h₀ := secondaryTent_rowInput_natDegree n S₀
  have h₁ := secondaryTent_rowInput_natDegree n S₁
  have h₂ := secondaryTent_rowInput_natDegree_le h2 n m S₂ hmn hS₂
  have hmul₁ := natDegree_mul_le (p := (X : K[X])^p)
    (q := secondaryTentRowInput n S₁)
  have hmul₂ := natDegree_mul_le (p := (X : K[X])^(2*p))
    (q := secondaryTentRowInput n S₂)
  simp only [natDegree_X_pow] at hmul₁ hmul₂
  unfold secondaryTentRowRegularNumerator
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le <;> omega
  · omega

/-- Degree payment for the already cancelled bulk numerator. The small
eta0 input has homogeneous degree `f=N-1`; the small kernel inputs have
degree `k=g-1`. -/
theorem secondaryTent_row_bulk_degree {K : Type*} [Field K]
    (p g b f k n m : ℕ) (β : K) (R F B C : K[X])
    (hnp : n+1=p) (hfp : b+f+1=p) (hkg : k+1=g) (hpb : p ≤ 2*b)
    (hR : R.natDegree ≤ 2*p+n+m) (hF : F.natDegree ≤ 2*f)
    (hB : B.natDegree ≤ 2*k) (hC : C.natDegree ≤ 2*k) :
    (secondaryTentRowBulkNumerator p g b β R F B C).natDegree ≤ 2*g+2*p+n+m := by
  have hq : (X^2+1 : K[X]).natDegree ≤ 2 := by
    simpa using (natDegree_X_pow_add_C (n := 2) (r := (1:K))).le
  have hl : (X-1 : K[X]).natDegree ≤ 1 := by
    simpa using natDegree_X_sub_C_le (1:K)
  have hqg := natDegree_pow_le_of_le g hq
  have hlb := natDegree_pow_le_of_le (2*b-p) hl
  have h₀ := natDegree_mul_le (p := (X^2+1 : K[X])^g) (q := R)
  have hβ₁ := natDegree_mul_le (p := (X^2+1 : K[X])^g) (q := X^p)
  have hβ₂ := natDegree_mul_le (p := (X^2+1 : K[X])^g * X^p) (q := Polynomial.C β)
  have hβ₃ := natDegree_mul_le (p := (X^2+1 : K[X])^g * X^p * Polynomial.C β)
    (q := (X-1)^(2*b-p))
  have hβ₄ := natDegree_mul_le
    (p := (X^2+1 : K[X])^g * X^p * Polynomial.C β * (X-1)^(2*b-p)) (q := F)
  have h₁ := natDegree_mul_le (p := (X : K[X])^p) (q := B)
  have h₂ := natDegree_mul_le (p := (X : K[X])^(2*p)) (q := C)
  simp only [natDegree_X_pow, natDegree_C, add_zero] at hβ₁ hβ₂ h₁ h₂
  unfold secondaryTentRowBulkNumerator
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · apply (natDegree_add_le _ _).trans
      apply max_le <;> omega
    · omega
  · omega

/-- With the literal source relations, the shared infinity flag pays the
exact numerator degree needed for the row's upper endpoint `18N-1`. -/
theorem secondaryTent_row_bulk_degree_actual {K : Type*} [Field K]
    (h2 : (2:K) ≠ 0) (N p g b f k n m : ℕ) (β : K)
    (S₀ S₁ S₂ F B C : K[X])
    (hnp : n+1=p) (hN : f+1=N) (hfp : b+N=p) (hkg : k+1=g)
    (hgp : g+4*p=27*N) (hmp : m+8*N+2=2*p)
    (hpb : p ≤ 2*b) (hmn : m ≤ n) (hS₂ : S₂.natDegree ≤ m) :
    (secondaryTentRowBulkNumerator p g b β
      (secondaryTentRowRegularNumerator p n S₀ S₁ S₂)
      (secondaryTentRowInput f F) (secondaryTentRowInput k B)
      (secondaryTentRowInput k C)).natDegree + 3*p+3 ≤ 46*N := by
  have hd := secondaryTent_row_bulk_degree p g b f k n m β
    (secondaryTentRowRegularNumerator p n S₀ S₁ S₂)
    (secondaryTentRowInput f F) (secondaryTentRowInput k B)
    (secondaryTentRowInput k C) hnp (by omega) hkg hpb
    (secondaryTent_row_regular_shared_cap h2 p n m S₀ S₁ S₂ hnp hmn hS₂)
    (secondaryTent_rowInput_natDegree f F) (secondaryTent_rowInput_natDegree k B)
    (secondaryTent_rowInput_natDegree k C)
  omega

end
end CatalanMeasure.Parametric
