module

public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Binomial-weight Hankel step recursion (GD)

For `W_{N,M}(x) = C(N,x) C(M,x)` on `x = 0..N` (`N ≤ M`), the Hankel determinant `H_k` of the
Gram matrix in the falling-factorial basis satisfies
`H_k(W_{N,M}) · ∏_{i=1}^{k-1} i (N+M+1-i) = C(N+M,N) ((k-1)!)² (NM)^{k-1} H_{k-1}(W_{N-1,M-1})`.
Ingredients: Pearson relation, summation by parts, action on falling factorials, and a
block-triangular Gram determinant.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Hankel

/-- The binomial weight. -/
def Wt (N M x : ℕ) : ℚ := (N.choose x : ℚ) * (M.choose x : ℚ)

/-- Weighted inner product on `x = 0..N`. -/
def ip (N M : ℕ) (f g : ℚ → ℚ) : ℚ := ∑ x ∈ range (N + 1), Wt N M x * f x * g x

/-- The operator `L f x = (N-x)(M-x) Δf(x) + x² (f(x-1) - f(x))`. -/
def Lop (N M : ℕ) (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  ((N : ℚ) - x) * ((M : ℚ) - x) * (f (x + 1) - f x) + x ^ 2 * (f (x - 1) - f x)

/-- Falling factorial `(x)_i`. -/
noncomputable def ff (i : ℕ) (x : ℚ) : ℚ := (descPochhammer ℚ i).eval x

lemma ff_zero (x : ℚ) : ff 0 x = 1 := by simp [ff]

lemma ff_succ (i : ℕ) (x : ℚ) : ff (i + 1) x = ff i x * (x - i) := by
  simp [ff, descPochhammer_succ_right]

lemma ff_shift (i : ℕ) (x : ℚ) : ff (i + 1) x = x * ff i (x - 1) := by
  induction i with
  | zero => simp [ff_succ, ff_zero]
  | succ i ih =>
    rw [ff_succ (i + 1) x, ih, ff_succ i (x - 1)]
    push_cast; ring

lemma ff_diff (i : ℕ) (x : ℚ) : ff (i + 1) (x + 1) - ff (i + 1) x = (i + 1) * ff i x := by
  induction i with
  | zero => simp [ff_succ, ff_zero]
  | succ i ih =>
    rw [ff_succ (i + 1) (x + 1), ff_succ (i + 1) x, ff_succ i (x + 1), ff_succ i x]
    rw [ff_succ i (x + 1), ff_succ i x] at ih
    push_cast at *
    linear_combination (x - i) * ih

/-- Pearson relation. -/
lemma pearson {N M : ℕ} (hnm : N ≤ M) {y : ℕ} (hy : y < N) :
    Wt N M y * (((N : ℚ) - y) * ((M : ℚ) - y)) = Wt N M (y + 1) * ((y : ℚ) + 1) ^ 2 := by
  have h1 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq N y)
  have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq M y)
  push_cast [Nat.cast_sub hy.le, Nat.cast_sub (hy.le.trans hnm)] at h1 h2
  unfold Wt
  linear_combination (-(M.choose (y + 1) : ℚ) * ((y : ℚ) + 1)) * h1
    - ((N.choose y : ℚ) * ((N : ℚ) - y)) * h2

/-- `W̃ = NM · W_{N-1,M-1}`. -/
lemma tilde {n m : ℕ} (hnm : n ≤ m) {y : ℕ} (hy : y ≤ n) :
    Wt (n + 1) (m + 1) y * ((((n + 1 : ℕ) : ℚ) - y) * (((m + 1 : ℕ) : ℚ) - y)) =
      ((n + 1 : ℚ) * (m + 1)) * Wt n m y := by
  have h1 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq n y)
  have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq m y)
  push_cast [Nat.cast_sub (show y ≤ n + 1 by omega), Nat.cast_sub (show y ≤ m + 1 by omega)]
    at h1 h2
  unfold Wt
  push_cast
  linear_combination (-((m + 1).choose y : ℚ) * ((m : ℚ) + 1 - y)) * h1
    - ((n.choose y : ℚ) * ((n : ℚ) + 1)) * h2

/-- Summation by parts. -/
theorem ip_L {N M : ℕ} (hnm : N ≤ M) (f g : ℚ → ℚ) :
    ip N M (Lop N M f) g = -∑ y ∈ range N,
      Wt N M y * (((N : ℚ) - y) * ((M : ℚ) - y)) * ((f (y + 1) - f y) * (g (y + 1) - g y)) := by
  unfold ip Lop
  have e : ∀ x : ℕ, Wt N M x * (((N : ℚ) - x) * ((M : ℚ) - x) * (f (x + 1) - f x) +
        (x : ℚ) ^ 2 * (f (x - 1) - f x)) * g x =
      Wt N M x * (((N : ℚ) - x) * ((M : ℚ) - x)) * (f (x + 1) - f x) * g x +
        Wt N M x * (x : ℚ) ^ 2 * (f (x - 1) - f x) * g x := fun x => by ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun x : ℕ => Wt N M x * (((N : ℚ) - x) * ((M : ℚ) - x)) *
    (f (x + 1) - f x) * g x) N, Finset.sum_range_succ' (fun x : ℕ => Wt N M x * (x : ℚ) ^ 2 *
    (f ((x : ℚ) - 1) - f x) * g x) N]
  simp only [sub_self, mul_zero, zero_mul, add_zero, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' := Finset.mem_range.1 hy
  have hp := pearson hnm hy'
  push_cast
  have : Wt N M (y + 1) * ((y : ℚ) + 1) ^ 2 * (f ((y : ℚ) + 1 - 1) - f ((y : ℚ) + 1)) *
      g ((y : ℚ) + 1) = Wt N M y * (((N : ℚ) - y) * ((M : ℚ) - y)) *
      (f y - f (y + 1)) * g (y + 1) := by
    rw [add_sub_cancel_right, ← hp]
  rw [this]; ring

lemma L_ff (N M j : ℕ) (x : ℚ) :
    Lop N M (ff (j + 1)) x = -((j + 1) * ((N + M + 1 : ℚ) - (j + 1))) * ff (j + 1) x +
      (j + 1) * ((N : ℚ) * M - j * ((N + M + 1 : ℚ) - (j + 1))) * ff j x := by
  unfold Lop
  have h1 := ff_diff j x
  have h2 := ff_diff j (x - 1)
  rw [sub_add_cancel] at h2
  have h3 := ff_shift j x
  have h4 := ff_succ j x
  linear_combination (((N : ℚ) - x) * ((M : ℚ) - x)) * h1 - x ^ 2 * h2
    + ((j + 1) * x) * h3 + (((j : ℚ) + 1) * ((N + M + 1 : ℚ) - (j + 1)) - ((j + 1) * x)) * h4

lemma mass (N M : ℕ) : ip N M (ff 0) (ff 0) = ((N + M).choose N : ℚ) := by
  have h2 : (N + M).choose N = ∑ k ∈ range (N + 1), N.choose k * M.choose k := by
    rw [add_comm N M, Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only
    rw [Nat.choose_symm (Finset.mem_range_succ_iff.1 hk), mul_comm]
  rw [h2]; push_cast
  simp [ip, Wt, ff_zero]

lemma ip_sum_left (N M : ℕ) (s : Finset ℕ) (a : ℕ → ℚ) (F : ℕ → ℚ → ℚ) (g : ℚ → ℚ) :
    ip N M (fun x => ∑ c ∈ s, a c * F c x) g = ∑ c ∈ s, a c * ip N M (F c) g := by
  unfold ip
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ => by ring

/-- `λ_{i+1}`. -/
def lam (S : ℚ) (i : ℕ) : ℚ := (i + 1) * (S - (i + 1))
/-- `μ_{i+1}`. -/
def mu (S p : ℚ) (i : ℕ) : ℚ := (i + 1) * (p - i * (S - (i + 1)))

/-- Entries of the bidiagonal change of basis. -/
def Pent (S p : ℚ) : ℕ → ℕ → ℚ
  | 0, c => if c = 0 then 1 else 0
  | i + 1, c => if c = i + 1 then -lam S i else if c = i then mu S p i else 0

/-- `1, Lφ_1, Lφ_2, …`. -/
noncomputable def bf (N M : ℕ) : ℕ → ℚ → ℚ
  | 0 => ff 0
  | i + 1 => Lop N M (ff (i + 1))

lemma bf_eq (N M j a : ℕ) (ha : a ≤ j) (x : ℚ) :
    bf N M a x = ∑ c ∈ range (j + 1), Pent ((N + M + 1 : ℚ)) ((N : ℚ) * M) a c * ff c x := by
  cases a with
  | zero =>
    simp [bf, Pent]
  | succ i =>
    have : ∀ c, Pent ((N + M + 1 : ℚ)) ((N : ℚ) * M) (i + 1) c * ff c x =
        (if c = i + 1 then -lam ((N + M + 1 : ℚ)) i * ff (i + 1) x else 0) +
          (if c = i then mu ((N + M + 1 : ℚ)) ((N : ℚ) * M) i * ff i x else 0) := by
      intro c
      by_cases h1 : c = i + 1
      · subst h1; simp [Pent]
      · by_cases h2 : c = i
        · subst h2; simp [Pent]
        · simp [Pent, h1, h2]
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    simp only [show i + 1 < j + 1 from by omega, show i < j + 1 from by omega, ↓reduceIte]
    simp only [bf, L_ff, lam, mu]

/-- Gram matrix in the falling-factorial basis. -/
noncomputable def gram (N M k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b => ip N M (ff a) (ff b)

/-- The Hankel determinant `H_k(W_{N,M})`. -/
noncomputable def hk (N M k : ℕ) : ℚ := (gram N M k).det

lemma hk_zero (N M : ℕ) : hk N M 0 = 1 := by simp [hk]

lemma PG_eq (N M j : ℕ) :
    (Matrix.of fun a c : Fin (j + 1) => Pent ((N + M + 1 : ℚ)) ((N : ℚ) * M) a c) * gram N M (j + 1) =
      Matrix.of fun a b : Fin (j + 1) => ip N M (bf N M a) (ff b) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, gram]
  rw [Fin.sum_univ_eq_sum_range (fun c => Pent ((N + M + 1 : ℚ)) ((N : ℚ) * M) a c *
    ip N M (ff c) (ff b)) (j + 1)]
  rw [← ip_sum_left]
  congr 1
  funext x
  exact (bf_eq N M j a (by omega) x).symm

lemma detP (N M j : ℕ) :
    (Matrix.of fun a c : Fin (j + 1) => Pent ((N + M + 1 : ℚ)) ((N : ℚ) * M) a c).det =
      (-1) ^ j * ∏ i ∈ range j, lam ((N + M + 1 : ℚ)) i := by
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, Fin.val_zero, Fin.val_succ, Pent]
    simp only [↓reduceIte, one_mul]
    rw [Fin.prod_univ_eq_prod_range (fun i => -lam ((N + M + 1 : ℚ)) i) j]
    simp [Finset.prod_neg]
  · intro a b hab
    simp only [Matrix.of_apply]
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    cases a with
    | zero =>
      have : b ≠ 0 := Nat.pos_iff_ne_zero.1 (Fin.lt_def.1 hab)
      simp [Pent, this]
    | succ i =>
      have : b > i + 1 := Fin.lt_def.1 hab
      have h1 : b ≠ i + 1 := by omega
      have h2 : b ≠ i := by omega
      simp [Pent, h1, h2]

lemma prod_succ_cast (j : ℕ) : ∏ a : Fin j, ((a : ℕ) + 1 : ℚ) = (j.factorial : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => ((i : ℚ) + 1)) j]
  exact_mod_cast Finset.prod_range_add_one_eq_factorial j

lemma col_zero (N M : ℕ) (hnm : N ≤ M) (i : ℕ) :
    ip N M (bf N M (i + 1)) (ff 0) = 0 := by
  simp only [bf]
  rw [ip_L hnm]
  simp [ff_zero]

/-- The step identity. -/
theorem step (n m j : ℕ) (hnm : n ≤ m) :
    hk (n + 1) (m + 1) (j + 1) * ∏ i ∈ range j,
        lam (((n + 1 : ℕ) : ℚ) + ((m + 1 : ℕ) : ℚ) + 1) i =
      (((n + 1) + (m + 1)).choose (n + 1) : ℚ) * (j.factorial : ℚ) ^ 2 *
        (((n + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ)) ^ j * hk n m j := by
  have hPG := congrArg Matrix.det (PG_eq (n + 1) (m + 1) j)
  rw [Matrix.det_mul, detP] at hPG
  set H' : Matrix (Fin (j + 1)) (Fin (j + 1)) ℚ :=
    Matrix.of fun a b : Fin (j + 1) => ip (n + 1) (m + 1) (bf (n + 1) (m + 1) a) (ff b) with hH'
  have hsub : H'.submatrix (0 : Fin (j + 1)).succAbove Fin.succ =
      (-(((n + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ))) •
        (Matrix.diagonal (fun a : Fin j => ((a : ℕ) + 1 : ℚ)) * gram n m j *
          Matrix.diagonal (fun a : Fin j => ((a : ℕ) + 1 : ℚ))) := by
    ext a b
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero, hH', Matrix.of_apply, Fin.val_succ,
      bf, Matrix.smul_apply, smul_eq_mul]
    rw [ip_L (by omega : n + 1 ≤ m + 1)]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, gram, Matrix.of_apply]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    simp only [ff_diff]
    unfold ip
    have : ∀ y ∈ range (n + 1), Wt (n + 1) (m + 1) y * ((((n + 1 : ℕ) : ℚ) - y) *
        (((m + 1 : ℕ) : ℚ) - y)) * (((a : ℕ) + 1) * ff a y * (((b : ℕ) + 1) * ff b y)) =
        ((n + 1 : ℚ) * (m + 1)) * (((a : ℕ) + 1) * ((b : ℕ) + 1)) *
          (Wt n m y * ff a y * ff b y) := fun y hy => by
      have t := tilde hnm (show y ≤ n by have := Finset.mem_range.1 hy; omega)
      linear_combination (((a : ℕ) + 1) * ff a y * (((b : ℕ) + 1) * ff b y)) * t
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    push_cast
    ring
  have hdetH : H'.det = (((n + 1) + (m + 1)).choose (n + 1) : ℚ) *
      ((-(((n + 1 : ℕ) : ℚ) * ((m + 1 : ℕ) : ℚ))) ^ j * ((j.factorial : ℚ) ^ 2 * hk n m j)) := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have h0 : ∀ i : Fin j, H' i.succ 0 = 0 := fun i => col_zero (n + 1) (m + 1) (by omega) i
    simp only [h0, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero]
    have h00 : H' 0 0 = (((n + 1) + (m + 1)).choose (n + 1) : ℚ) := by
      simpa [hH', bf] using mass (n + 1) (m + 1)
    rw [h00, hsub, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    simp only [Fintype.card_fin, prod_succ_cast, hk]
    ring
  rw [hdetH] at hPG
  have hne : ((-1 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hne
  rw [neg_pow] at hPG
  unfold hk at hPG ⊢
  linear_combination hPG

end CatalanCore.Bordered.Hankel
