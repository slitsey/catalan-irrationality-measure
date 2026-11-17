module

public import CatalanCore.Linalg.RoundedInterval
public import CatalanCore.Linalg.RankDvd
public import Mathlib.Tactic.FieldSimp

@[expose] public section
namespace CatalanCore.Linalg

/-- Reciprocal endpoints are exact rationals; rounding happens only after multiplication.
This is the four-endpoint direct quotient, with no rounded intermediate inverse. -/
def directQuotI (b : ℕ) (J K : QInterval) : QInterval :=
  mulI b J ⟨1/K.hi, 1/K.lo⟩

private theorem reciprocal_endpoints (lo hi y : ℝ)
    (hy : lo ≤ y ∧ y ≤ hi) (hz : hi < 0 ∨ 0 < lo) :
    1/hi ≤ 1/y ∧ 1/y ≤ 1/lo := by
  rcases hz with hn | hp
  · have hyn : y < 0 := hy.2.trans_lt hn
    constructor
    · have h := one_div_le_one_div_of_le (neg_pos.mpr hn) (neg_le_neg hy.2)
      simpa only [one_div, inv_neg, neg_neg] using neg_le_neg h
    · have h := one_div_le_one_div_of_le (neg_pos.mpr hyn) (neg_le_neg hy.1)
      simpa only [one_div, inv_neg, neg_neg] using neg_le_neg h
  · exact ⟨one_div_le_one_div_of_le (hp.trans_le hy.1) hy.2,
      one_div_le_one_div_of_le hp hy.1⟩

theorem directQuotI_contains (b : ℕ) (J K : QInterval) (x y : ℝ)
    (hx : intervalContains J x) (hy : intervalContains K y)
    (hz : excludesZero K = true) : intervalContains (directQuotI b J K) (x/y) := by
  have hzQ : K.hi < 0 ∨ 0 < K.lo := by simpa [excludesZero] using hz
  have hzR : (K.hi : ℝ) < 0 ∨ 0 < (K.lo : ℝ) := by exact_mod_cast hzQ
  have hr : intervalContains (⟨1/K.hi,1/K.lo⟩ : QInterval) (1/y) := by
    simpa only [intervalContains, Rat.cast_div, Rat.cast_one] using
      reciprocal_endpoints K.lo K.hi y hy hzR
  simpa only [directQuotI, div_eq_mul_inv, one_div, one_mul] using
    mulI_contains b J ⟨1/K.hi,1/K.lo⟩ x (1/y) hx hr

theorem ne_zero_of_interval_excludes (J : QInterval) (x : ℝ)
    (hx : intervalContains J x) (hz : excludesZero J = true) : x ≠ 0 := by
  have hzQ : J.hi < 0 ∨ 0 < J.lo := by simpa [excludesZero] using hz
  have hzR : (J.hi : ℝ) < 0 ∨ 0 < (J.lo : ℝ) := by exact_mod_cast hzQ
  rcases hzR with hn | hp
  · exact ne_of_lt (hx.2.trans_lt hn)
  · exact ne_of_gt (hp.trans_le hx.1)

def schurField {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) : Matrix (Fin n) (Fin n) K :=
  fun i j => M i.succ j.succ - (M i.succ 0 / M 0 0) * M 0 j.succ

/-- Exact Schur determinant, reusing the established Bareiss pivot identity. -/
theorem det_eq_pivot_mul_schur {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) K) (hp : M 0 0 ≠ 0) :
    M.det = M 0 0 * (schurField M).det := by
  have he : pivotComp M = M 0 0 • schurField M := by
    ext i j
    simp only [pivotComp, Matrix.of_apply, schurField, Matrix.smul_apply, smul_eq_mul]
    field_simp
    <;> ring
  have hd := pivot_det M
  rw [he, Matrix.det_smul, Fintype.card_fin] at hd
  apply mul_left_cancel₀ (pow_ne_zero n hp)
  calc
    M 0 0 ^ n * M.det = M 0 0 * (M 0 0 ^ n * (schurField M).det) := hd
    _ = M 0 0 ^ n * (M 0 0 * (schurField M).det) := by ring

def schurI (b : ℕ) {n : ℕ}
    (M : Matrix (Fin (n+1)) (Fin (n+1)) QInterval) : Matrix (Fin n) (Fin n) QInterval :=
  fun i j => subI b (M i.succ j.succ)
    (mulI b (directQuotI b (M i.succ 0) (M 0 0)) (M 0 j.succ))

def matrixContains {n : ℕ} (A : Matrix (Fin n) (Fin n) QInterval)
    (M : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j, intervalContains (A i j) (M i j)

theorem schurI_contains (b : ℕ) {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) QInterval)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (h : matrixContains A M) (hp : excludesZero (A 0 0) = true) :
    matrixContains (schurI b A) (schurField M) := by
  intro i j
  exact subI_contains b _ _ _ _ (h i.succ j.succ)
    (mulI_contains b _ _ _ _
      (directQuotI_contains b _ _ _ _ (h i.succ 0) (h 0 0) hp) (h 0 j.succ))

/-- Pivot choice is a generic parameter. A structural List adapter may choose a
stable row move, a swap, or the identity. Its permutation sign is always included. -/
def intervalGaussWith (b : ℕ)
    (choose : (n : ℕ) → Matrix (Fin n) (Fin n) QInterval → Equiv.Perm (Fin n)) :
    (n : ℕ) → Matrix (Fin n) (Fin n) QInterval → Option QInterval
  | 0, _ => some (singletonI 1)
  | n+1, A =>
    let σ := choose (n+1) A
    let B := A.submatrix σ id
    if excludesZero (B 0 0) then
      (intervalGaussWith b choose n (schurI b B)).map
        (fun J => mulI b (singletonI (((Equiv.Perm.sign σ : ℤ) : ℚ)⁻¹))
          (mulI b (B 0 0) J))
    else none

theorem intervalGaussWith_contains (b : ℕ)
    (choose : (n : ℕ) → Matrix (Fin n) (Fin n) QInterval → Equiv.Perm (Fin n)) :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) QInterval)
      (M : Matrix (Fin n) (Fin n) ℝ) (J : QInterval),
      intervalGaussWith b choose n A = some J → matrixContains A M →
      intervalContains J M.det := by
  intro n
  induction n with
  | zero =>
    intro A M J he h
    simp only [intervalGaussWith, Option.some.injEq] at he
    subst J
    simp [intervalContains, singletonI, Matrix.det_isEmpty]
  | succ n ih =>
    intro A M J he h
    let σ := choose (n+1) A
    let B := A.submatrix σ id
    let N := M.submatrix σ id
    have hBN : matrixContains B N := fun i j => h (σ i) j
    change (if excludesZero (B 0 0) then
      (intervalGaussWith b choose n (schurI b B)).map
        (fun J => mulI b (singletonI (((Equiv.Perm.sign σ : ℤ) : ℚ)⁻¹))
          (mulI b (B 0 0) J)) else none) = some J at he
    split at he
    next hp =>
      cases hr : intervalGaussWith b choose n (schurI b B) with
      | none => simp only [hr, Option.map_none] at he; cases he
      | some R =>
        simp only [hr, Option.map_some, Option.some.injEq] at he
        subst J
        have hd := ih (schurI b B) (schurField N) R hr (schurI_contains b B N hBN hp)
        have hdet := det_eq_pivot_mul_schur N
          (ne_zero_of_interval_excludes (B 0 0) (N 0 0) (hBN 0 0) hp)
        have hperm : N.det = ((Equiv.Perm.sign σ : ℤ) : ℝ) * M.det := Matrix.det_permute σ M
        have hs : (((Equiv.Perm.sign σ : ℤ) : ℝ)) ≠ 0 := by
          exact_mod_cast (Units.ne_zero (Equiv.Perm.sign σ))
        have hsign : intervalContains (singletonI (((Equiv.Perm.sign σ : ℤ) : ℚ)⁻¹))
            ((((Equiv.Perm.sign σ : ℤ) : ℝ))⁻¹) := by
          simp [intervalContains, singletonI]
        have hg := mulI_contains b _ _ _ _ hsign
          (mulI_contains b _ _ _ _ (hBN 0 0) hd)
        have hv : (((Equiv.Perm.sign σ : ℤ) : ℝ))⁻¹ *
            (N 0 0 * (schurField N).det) = M.det := by
          rw [← hdet, hperm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
        rw [hv] at hg
        exact hg
    next => cases he

end CatalanCore.Linalg
