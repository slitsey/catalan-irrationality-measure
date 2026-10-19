module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Prime
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The rank principle: rank mod a prime element bounds the divisibility of the determinant

Let `R` be a domain, `ϖ` a prime element, and `φ : R →+* K` a ring map to a field with
`φ x = 0 ↔ ϖ ∣ x`.  If `B` is an `n × n` matrix over `R` whose reduction `B.map φ` has rank at most
`n - k`, then `ϖ ^ k ∣ det B` (`dvd_det_of_rank`).

No Smith normal form is used: induction on `n`, with the (Bareiss) pivot identity
`b ^ n * det B = b * det (b * D - c * r)` and the nullity comparison of a matrix with its Schur
complement; the domain hypothesis is used to cancel the pivot.
-/

open Matrix Finset

namespace CatalanCore.Linalg

section Field

variable {K : Type*} [Field K] {n : ℕ}

/-- The Schur complement (scaled by the pivot). -/
def pivotComp {R : Type*} [CommRing R] (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => A 0 0 * A i.succ j.succ - A i.succ 0 * A 0 j.succ

/-- Passing to the Schur complement lowers the rank by at least one. -/
lemma rank_pivotComp_add_one (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hb : A 0 0 ≠ 0) :
    (pivotComp A).rank + 1 ≤ A.rank := by
  -- nullity comparison
  have hmap : ∀ x ∈ LinearMap.ker A.mulVecLin, (fun i : Fin n => x i.succ) ∈
      LinearMap.ker (pivotComp A).mulVecLin := by
    intro x hx
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    have h0 := congrFun hx 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.zero_apply] at h0
    funext i
    have hi := congrFun hx i.succ
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.zero_apply] at hi
    simp only [Matrix.mulVec, dotProduct, pivotComp, Matrix.of_apply, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib]
    have e1 : ∑ j : Fin n, A 0 0 * A i.succ j.succ * x j.succ =
        A 0 0 * ∑ j : Fin n, A i.succ j.succ * x j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have e2 : ∑ j : Fin n, A i.succ 0 * A 0 j.succ * x j.succ =
        A i.succ 0 * ∑ j : Fin n, A 0 j.succ * x j.succ := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [e1, e2]
    have s0 : ∑ j : Fin n, A 0 j.succ * x j.succ = -(A 0 0 * x 0) := by linear_combination h0
    have s1 : ∑ j : Fin n, A i.succ j.succ * x j.succ = -(A i.succ 0 * x 0) := by
      linear_combination hi
    rw [s0, s1]; ring
  let T : LinearMap.ker A.mulVecLin →ₗ[K] LinearMap.ker (pivotComp A).mulVecLin :=
    ((LinearMap.funLeft K K (Fin.succ : Fin n → Fin (n + 1))).comp
      (LinearMap.ker A.mulVecLin).subtype).codRestrict _ (fun x => hmap x.1 x.2)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hx' : (fun i : Fin n => (x : Fin (n + 1) → K) i.succ) = 0 := by
      exact congrArg Subtype.val hx
    have hxk := x.2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hxk
    have h0 := congrFun hxk 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.zero_apply] at h0
    have : ∀ j : Fin n, (x : Fin (n + 1) → K) j.succ = 0 := fun j => congrFun hx' j
    simp only [this, mul_zero, Finset.sum_const_zero, add_zero] at h0
    have hx0 : (x : Fin (n + 1) → K) 0 = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hb
      · exact h
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => this j) i
    exact hx0
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have rn1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have rn2 := LinearMap.finrank_range_add_finrank_ker (pivotComp A).mulVecLin
  simp only [Module.finrank_fin_fun] at rn1 rn2
  unfold Matrix.rank
  omega

end Field

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- **Bareiss pivot identity.** -/
lemma pivot_det (B : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    B 0 0 ^ n * B.det = B 0 0 * (pivotComp B).det := by
  set b := B 0 0 with hb
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) R := Matrix.of fun i j =>
    if j = 0 then (if i = 0 then 1 else 0)
    else if i = 0 then -B 0 j else if i = j then b else 0
  have hU : U.BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    have hi0 : 0 < i := lt_of_le_of_lt (Fin.zero_le _) hij
    have hi : i ≠ 0 := hi0.ne'
    have hne : i ≠ j := ne_of_gt hij
    by_cases hj : j = 0
    · subst hj; simp [U, hi]
    · simp [U, hj, hi, hne]
  have hdetU : U.det = b ^ n := by
    rw [Matrix.det_of_isUpperTriangular hU, Fin.prod_univ_succ]
    simp only [U, Matrix.of_apply, ite_true]
    rw [Finset.prod_congr rfl (g := fun _ => b)]
    · simp
    · intro i _
      have : i.succ ≠ 0 := Fin.succ_ne_zero i
      simp [this]
  have h0j : ∀ j : Fin n, (B * U) 0 j.succ = 0 := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [U, Fin.succ_ne_zero, hb]
    ring
  have h00 : (B * U) 0 0 = b := by
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    simp [U, Fin.succ_ne_zero, hb]
  have hsub : (B * U).submatrix Fin.succ Fin.succ = pivotComp B := by
    ext i j
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ]
    simp [U, Fin.succ_ne_zero, hb, pivotComp, Fin.succ_inj]
    ring
  have hd := Matrix.det_succ_row_zero (B * U)
  rw [Fin.sum_univ_succ] at hd
  simp only [h0j, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, h00, Fin.succAbove_zero, hsub] at hd
  rw [Matrix.det_mul, hdetU] at hd
  linear_combination hd

end Ring
section Main

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K]

/-- **The rank principle.**  `ϖ` a prime of the domain `R`, `φ : R →+* K` with kernel `(ϖ)`.
If the reduction of the `n × n` matrix `B` has rank `≤ n - k`, then `ϖ ^ k ∣ det B`. -/
theorem dvd_det_of_rank (φ : R →+* K) {ϖ : R} (hϖ : Prime ϖ) (hker : ∀ x, φ x = 0 ↔ ϖ ∣ x) :
    ∀ (n k : ℕ) (B : Matrix (Fin n) (Fin n) R), (B.map φ).rank + k ≤ n → ϖ ^ k ∣ B.det := by
  intro n
  induction n with
  | zero =>
    intro k B h
    have : k = 0 := by omega
    subst this; simp
  | succ n ih =>
    intro k B h
    by_cases hall : ∀ i j, φ (B i j) = 0
    · -- all entries divisible by `ϖ`
      choose B1 hB1 using fun i j => (hker _).1 (hall i j)
      have : B = ϖ • Matrix.of B1 := by
        ext i j; simp [hB1 i j]
      rw [this, Matrix.det_smul]
      simp only [Fintype.card_fin]
      exact (pow_dvd_pow ϖ (by omega)).mul_right _
    · replace hall : ∃ i j, φ (B i j) ≠ 0 := by
        by_contra hc
        exact hall (fun i j => by_contra fun h => hc ⟨i, j, h⟩)
      obtain ⟨i0, j0, hij⟩ := hall
      set σ := Equiv.swap (0 : Fin (n + 1)) i0
      set τ := Equiv.swap (0 : Fin (n + 1)) j0
      set B2 := B.submatrix σ τ with hB2
      have hB200 : B2 0 0 = B i0 j0 := by simp [hB2, σ, τ]
      have hdet : B2.det = (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) * B.det := by
        have h1 : B2 = (B.submatrix σ id).submatrix id τ := rfl
        rw [h1, Matrix.det_permute', Matrix.det_permute]; push_cast; ring
      have hrank : (B2.map φ).rank = (B.map φ).rank := by
        have : B2.map φ = (B.map φ).submatrix σ τ := rfl
        rw [this, Matrix.rank_submatrix]
      have hb : φ (B2 0 0) ≠ 0 := by rw [hB200]; exact hij
      -- Schur complement
      have hmap : (pivotComp B2).map φ = pivotComp (B2.map φ) := by
        ext i j; simp [pivotComp]
      have hr := rank_pivotComp_add_one (B2.map φ) (by simpa using hb)
      have h2 : ϖ ^ k ∣ (pivotComp B2).det := by
        apply ih
        rw [hmap]; omega
      have h3 : ϖ ^ k ∣ B2 0 0 ^ n * B2.det := by
        rw [pivot_det]; exact h2.mul_left _
      have hnd : ¬ ϖ ∣ B2 0 0 ^ n := fun hd =>
        (hb ((hker _).2 (hϖ.dvd_of_dvd_pow hd)))
      have h4 : ϖ ^ k ∣ B2.det := hϖ.pow_dvd_of_dvd_mul_left k hnd h3
      rw [hdet] at h4
      have hs : ∀ τ' : Equiv.Perm (Fin (n + 1)), ((Equiv.Perm.sign τ' : ℤˣ) : ℤ) = 1 ∨
          ((Equiv.Perm.sign τ' : ℤˣ) : ℤ) = -1 := by
        intro τ'
        rcases Int.units_eq_one_or (Equiv.Perm.sign τ') with h | h <;> simp [h]
      rcases hs σ with h | h <;> rcases hs τ with h' | h' <;> rw [h, h'] at h4 <;>
        simpa using h4

end Main

end CatalanCore.Linalg
