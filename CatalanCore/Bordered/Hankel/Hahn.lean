module

public import CatalanCore.Bordered.Hankel.Binomial

/-!
# Hahn-weight Hankel step recursion

For the Hahn weight `W_{α,β,N}(y) = C(α+y,y) C(β+N-y,N-y)` on `y = 0..N`, the Hankel determinant
`H_k` of the Gram matrix in the falling-factorial basis satisfies
`H_{j+1}(W_{α,β,n+1}) · ∏_{i<j} (i+1)(α+β+i+2)
   = C(α+β+n+2, n+1) (j!)² ((α+1)(β+1))^j H_j(W_{α+1,β+1,n})`.
This is the Hahn analogue of `Binomial.lean` (same ingredients: Pearson relation, summation by
parts, action of the Hahn operator on falling factorials, mass, block-triangular determinant).
It is used for `v_j = (S-j) c_j = (2m+1)! · W_{2m+1,0,N}` in the hybrid `κ_S`; the binomial weight
`C(N,x) C(M,x)` is not a special case (it would need negative `α`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Hankel

/-- The Hahn weight. -/
def WtH (α β N y : ℕ) : ℚ := ((α + y).choose y : ℚ) * ((β + N - y).choose (N - y) : ℚ)

/-- Weighted inner product on `y = 0..N`. -/
def ipH (α β N : ℕ) (f g : ℚ → ℚ) : ℚ := ∑ y ∈ range (N + 1), WtH α β N y * f y * g y

/-- The Hahn operator `L f y = (y+α+1)(N-y) Δf(y) + y(β+N+1-y)(f(y-1) - f(y))`. -/
def LopH (α β N : ℕ) (f : ℚ → ℚ) (x : ℚ) : ℚ :=
  (x + α + 1) * ((N : ℚ) - x) * (f (x + 1) - f x) +
    x * ((β : ℚ) + N + 1 - x) * (f (x - 1) - f x)

/-- Pearson relation. -/
lemma pearsonH (α β : ℕ) {N y : ℕ} (hy : y < N) :
    WtH α β N y * (((y : ℚ) + α + 1) * ((N : ℚ) - y)) =
      WtH α β N (y + 1) * (((y : ℚ) + 1) * ((β : ℚ) + N - y)) := by
  obtain ⟨s, rfl⟩ : ∃ s, N = y + s + 1 := ⟨N - y - 1, by omega⟩
  have e1 : β + (y + s + 1) - y = β + s + 1 := by omega
  have e2 : y + s + 1 - y = s + 1 := by omega
  have e3 : β + (y + s + 1) - (y + 1) = β + s := by omega
  have e4 : y + s + 1 - (y + 1) = s := by omega
  have h1 := congrArg (Nat.cast : ℕ → ℚ) (Nat.add_one_mul_choose_eq (α + y) y)
  have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.add_one_mul_choose_eq (β + s) s)
  simp only [WtH, e1, e2, e3, e4]
  push_cast at h1 h2 ⊢
  rw [show α + (y + 1) = α + y + 1 by omega]
  linear_combination (((β + s + 1).choose (s + 1) : ℚ) * (s + 1)) * h1
    - ((((α + y + 1).choose (y + 1)) : ℚ) * (y + 1)) * h2

/-- `W̃ = (α+1)(β+1) · W_{α+1,β+1,n}`. -/
lemma tildeH (α β : ℕ) {n y : ℕ} (hy : y ≤ n) :
    WtH α β (n + 1) y * (((y : ℚ) + α + 1) * (((n + 1 : ℕ) : ℚ) - y)) =
      ((α + 1 : ℚ) * (β + 1)) * WtH (α + 1) (β + 1) n y := by
  obtain ⟨t, rfl⟩ : ∃ t, n = y + t := ⟨n - y, by omega⟩
  have e1 : β + (y + t + 1) - y = β + t + 1 := by omega
  have e2 : y + t + 1 - y = t + 1 := by omega
  have e3 : β + 1 + (y + t) - y = β + t + 1 := by omega
  have e4 : y + t - y = t := by omega
  have h1 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_mul_succ_eq (α + y) y)
  have h2 := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq (β + t + 1) t)
  have e5 : α + y + 1 - y = α + 1 := by omega
  have e6 : β + t + 1 - t = β + 1 := by omega
  rw [e5] at h1
  rw [e6] at h2
  simp only [WtH, e1, e2, e3, e4]
  push_cast at h1 h2 ⊢
  rw [show α + 1 + y = α + y + 1 by omega]
  linear_combination (((β + t + 1).choose (t + 1) : ℚ) * (t + 1)) * h1
    + ((((α + y + 1).choose y) : ℚ) * (α + 1)) * h2

/-- Summation by parts. -/
theorem ipH_L (α β N : ℕ) (f g : ℚ → ℚ) :
    ipH α β N (LopH α β N f) g = -∑ y ∈ range N,
      WtH α β N y * (((y : ℚ) + α + 1) * ((N : ℚ) - y)) *
        ((f (y + 1) - f y) * (g (y + 1) - g y)) := by
  unfold ipH LopH
  have e : ∀ x : ℕ, WtH α β N x * (((x : ℚ) + α + 1) * ((N : ℚ) - x) * (f (x + 1) - f x) +
        (x : ℚ) * ((β : ℚ) + N + 1 - x) * (f (x - 1) - f x)) * g x =
      WtH α β N x * (((x : ℚ) + α + 1) * ((N : ℚ) - x)) * (f (x + 1) - f x) * g x +
        WtH α β N x * ((x : ℚ) * ((β : ℚ) + N + 1 - x)) * (f (x - 1) - f x) * g x :=
    fun x => by ring
  simp_rw [e, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ (fun x : ℕ => WtH α β N x * (((x : ℚ) + α + 1) * ((N : ℚ) - x)) *
    (f (x + 1) - f x) * g x) N, Finset.sum_range_succ' (fun x : ℕ => WtH α β N x *
    ((x : ℚ) * ((β : ℚ) + N + 1 - x)) * (f ((x : ℚ) - 1) - f x) * g x) N]
  simp only [sub_self, mul_zero, zero_mul, add_zero, Nat.cast_zero, zero_sub]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hy' := Finset.mem_range.1 hy
  have hp := pearsonH α β hy'
  push_cast
  have : WtH α β N (y + 1) * (((y : ℚ) + 1) * ((β : ℚ) + N + 1 - ((y : ℚ) + 1))) *
      (f ((y : ℚ) + 1 - 1) - f ((y : ℚ) + 1)) * g ((y : ℚ) + 1) =
      WtH α β N y * (((y : ℚ) + α + 1) * ((N : ℚ) - y)) *
      (f y - f (y + 1)) * g (y + 1) := by
    rw [add_sub_cancel_right]
    have e : WtH α β N (y + 1) * (((y : ℚ) + 1) * ((β : ℚ) + N + 1 - ((y : ℚ) + 1))) =
      WtH α β N (y + 1) * (((y : ℚ) + 1) * ((β : ℚ) + N - y)) := by ring
    rw [e, ← hp]
  rw [this]; ring

lemma L_ffH (α β N j : ℕ) (x : ℚ) :
    LopH α β N (ff (j + 1)) x = -((j + 1) * ((α : ℚ) + β + j + 2)) * ff (j + 1) x +
      (j + 1) * (((α : ℚ) + 1) * N + j * ((N : ℚ) - α - j - 1)) * ff j x := by
  unfold LopH
  have h1 := ff_diff j x
  have h2 := ff_diff j (x - 1)
  rw [sub_add_cancel] at h2
  have h3 := ff_shift j x
  have h4 := ff_succ j x
  linear_combination (((x + α + 1) * ((N : ℚ) - x))) * h1 - (x * ((β : ℚ) + N + 1 - x)) * h2
    + ((j + 1) * ((β : ℚ) + N + 1 - x)) * h3 + ((j + 1) * ((α : ℚ) + j + 1 - N + x)) * h4


lemma hockeyH (β N : ℕ) : ∑ t ∈ range (N + 1), (β + t).choose t = (β + N + 1).choose N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, show β + (N + 1) + 1 = (β + N + 1) + 1 by omega,
      Nat.choose_succ_succ' (β + N + 1) N, show β + (N + 1) = β + N + 1 by omega, add_comm]

/-- Convolution `∑_y C(α+y,y) C(β+N-y,N-y) = C(α+β+N+1,N)` (Pascal induction). -/
lemma massH_nat (α : ℕ) : ∀ β N : ℕ,
    ∑ y ∈ range (N + 1), (α + y).choose y * (β + N - y).choose (N - y) =
      (α + β + N + 1).choose N := by
  induction α with
  | zero =>
    intro β N
    have h := Finset.sum_range_reflect (fun t => (β + t).choose t) (N + 1)
    simp only [zero_add, Nat.choose_self, one_mul]
    rw [← hockeyH β N, ← h]
    refine Finset.sum_congr rfl fun y hy => ?_
    have := Finset.mem_range.1 hy
    rw [show N + 1 - 1 - y = N - y by omega, show β + N - y = β + (N - y) by omega]
  | succ α ih =>
    intro β N
    induction N with
    | zero => simp
    | succ N ihN =>
      have key : ∑ y ∈ range (N + 1 + 1), (α + 1 + y).choose y * (β + (N + 1) - y).choose (N + 1 - y) =
          ∑ y ∈ range (N + 1 + 1), (α + y).choose y * (β + (N + 1) - y).choose (N + 1 - y) +
          ∑ y ∈ range (N + 1), (α + 1 + y).choose y * (β + N - y).choose (N - y) := by
        rw [Finset.sum_range_succ' _ (N + 1),
          Finset.sum_range_succ' (fun y => (α + y).choose y * (β + (N + 1) - y).choose (N + 1 - y))
            (N + 1)]
        have hrec : ∀ y ∈ range (N + 1),
            (α + 1 + (y + 1)).choose (y + 1) * (β + (N + 1) - (y + 1)).choose (N + 1 - (y + 1)) =
            (α + (y + 1)).choose (y + 1) * (β + (N + 1) - (y + 1)).choose (N + 1 - (y + 1)) +
            (α + 1 + y).choose y * (β + N - y).choose (N - y) := by
          intro y hy
          have := Finset.mem_range.1 hy
          rw [show β + (N + 1) - (y + 1) = β + N - y by omega,
            show N + 1 - (y + 1) = N - y by omega,
            show α + 1 + (y + 1) = (α + 1 + y) + 1 by omega,
            show α + (y + 1) = α + 1 + y by omega, Nat.choose_succ_succ' (α + 1 + y) y]
          ring
        rw [Finset.sum_congr rfl hrec, Finset.sum_add_distrib]
        simp only [Nat.add_zero, Nat.choose_zero_right, one_mul]
        ring
      rw [key, ih β (N + 1), ihN]
      rw [show α + 1 + β + (N + 1) + 1 = (α + β + N + 2) + 1 by omega,
        show α + β + (N + 1) + 1 = α + β + N + 2 by omega,
        show α + 1 + β + N + 1 = α + β + N + 2 by omega, Nat.choose_succ_succ' (α + β + N + 2) N,
        add_comm]

lemma massH (α β N : ℕ) : ipH α β N (ff 0) (ff 0) = ((α + β + N + 1).choose N : ℚ) := by
  rw [← massH_nat α β N]; push_cast
  simp [ipH, WtH, ff_zero]

lemma ipH_sum_left (α β N : ℕ) (s : Finset ℕ) (a : ℕ → ℚ) (F : ℕ → ℚ → ℚ) (g : ℚ → ℚ) :
    ipH α β N (fun x => ∑ c ∈ s, a c * F c x) g = ∑ c ∈ s, a c * ipH α β N (F c) g := by
  unfold ipH
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x _ => by ring

/-- `λ_{i+1}` for the Hahn operator. -/
def lamH (α β i : ℕ) : ℚ := ((i : ℚ) + 1) * ((α : ℚ) + β + i + 2)
/-- `μ_{i+1}` for the Hahn operator. -/
def muH (α N i : ℕ) : ℚ :=
  ((i : ℚ) + 1) * (((α : ℚ) + 1) * N + i * ((N : ℚ) - α - i - 1))

/-- Entries of the bidiagonal change of basis. -/
def PentH (α β N : ℕ) : ℕ → ℕ → ℚ
  | 0, c => if c = 0 then 1 else 0
  | i + 1, c => if c = i + 1 then -lamH α β i else if c = i then muH α N i else 0

/-- `1, Lφ_1, Lφ_2, …`. -/
noncomputable def bfH (α β N : ℕ) : ℕ → ℚ → ℚ
  | 0 => ff 0
  | i + 1 => LopH α β N (ff (i + 1))

lemma bfH_eq (α β N j a : ℕ) (ha : a ≤ j) (x : ℚ) :
    bfH α β N a x = ∑ c ∈ range (j + 1), PentH α β N a c * ff c x := by
  cases a with
  | zero => simp [bfH, PentH]
  | succ i =>
    have : ∀ c, PentH α β N (i + 1) c * ff c x =
        (if c = i + 1 then -lamH α β i * ff (i + 1) x else 0) +
          (if c = i then muH α N i * ff i x else 0) := by
      intro c
      by_cases h1 : c = i + 1
      · subst h1; simp [PentH]
      · by_cases h2 : c = i
        · subst h2; simp [PentH]
        · simp [PentH, h1, h2]
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_range]
    simp only [show i + 1 < j + 1 from by omega, show i < j + 1 from by omega, ↓reduceIte]
    simp only [bfH, L_ffH, lamH, muH]

/-- Gram matrix in the falling-factorial basis. -/
noncomputable def gramH (α β N k : ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun a b => ipH α β N (ff a) (ff b)

/-- The Hankel determinant `H_k(W_{α,β,N})`. -/
noncomputable def hkH (α β N k : ℕ) : ℚ := (gramH α β N k).det

lemma hkH_zero (α β N : ℕ) : hkH α β N 0 = 1 := by simp [hkH]

lemma PGH_eq (α β N j : ℕ) :
    (Matrix.of fun a c : Fin (j + 1) => PentH α β N a c) * gramH α β N (j + 1) =
      Matrix.of fun a b : Fin (j + 1) => ipH α β N (bfH α β N a) (ff b) := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.of_apply, gramH]
  rw [Fin.sum_univ_eq_sum_range (fun c => PentH α β N a c * ipH α β N (ff c) (ff b)) (j + 1)]
  rw [← ipH_sum_left]
  congr 1
  funext x
  exact (bfH_eq α β N j a (by omega) x).symm

lemma detPH (α β N j : ℕ) :
    (Matrix.of fun a c : Fin (j + 1) => PentH α β N a c).det =
      (-1) ^ j * ∏ i ∈ range j, lamH α β i := by
  rw [Matrix.det_of_isLowerTriangular]
  · rw [Fin.prod_univ_succ]
    simp only [Matrix.of_apply, Fin.val_zero, Fin.val_succ, PentH]
    simp only [↓reduceIte, one_mul]
    rw [Fin.prod_univ_eq_prod_range (fun i => -lamH α β i) j]
    simp [Finset.prod_neg]
  · intro a b hab
    simp only [Matrix.of_apply]
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    cases a with
    | zero =>
      have : b ≠ 0 := Nat.pos_iff_ne_zero.1 (Fin.lt_def.1 hab)
      simp [PentH, this]
    | succ i =>
      have : b > i + 1 := Fin.lt_def.1 hab
      have h1 : b ≠ i + 1 := by omega
      have h2 : b ≠ i := by omega
      simp [PentH, h1, h2]

lemma col_zeroH (α β N : ℕ) (i : ℕ) : ipH α β N (bfH α β N (i + 1)) (ff 0) = 0 := by
  simp only [bfH]
  rw [ipH_L]
  simp [ff_zero]

/-- The step identity. -/
theorem stepH (α β n j : ℕ) :
    hkH α β (n + 1) (j + 1) * ∏ i ∈ range j, lamH α β i =
      ((α + β + (n + 1) + 1).choose (n + 1) : ℚ) * (j.factorial : ℚ) ^ 2 *
        (((α : ℚ) + 1) * ((β : ℚ) + 1)) ^ j * hkH (α + 1) (β + 1) n j := by
  have hPG := congrArg Matrix.det (PGH_eq α β (n + 1) j)
  rw [Matrix.det_mul, detPH] at hPG
  set H' : Matrix (Fin (j + 1)) (Fin (j + 1)) ℚ :=
    Matrix.of fun a b : Fin (j + 1) => ipH α β (n + 1) (bfH α β (n + 1) a) (ff b) with hH'
  have hsub : H'.submatrix (0 : Fin (j + 1)).succAbove Fin.succ =
      (-(((α : ℚ) + 1) * ((β : ℚ) + 1))) •
        (Matrix.diagonal (fun a : Fin j => ((a : ℕ) + 1 : ℚ)) * gramH (α + 1) (β + 1) n j *
          Matrix.diagonal (fun a : Fin j => ((a : ℕ) + 1 : ℚ))) := by
    ext a b
    simp only [Matrix.submatrix_apply, Fin.succAbove_zero, hH', Matrix.of_apply, Fin.val_succ,
      bfH, Matrix.smul_apply, smul_eq_mul]
    rw [ipH_L]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, gramH, Matrix.of_apply]
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    simp only [ff_diff]
    unfold ipH
    have : ∀ y ∈ range (n + 1), WtH α β (n + 1) y * (((y : ℚ) + α + 1) *
        (((n + 1 : ℕ) : ℚ) - y)) * (((a : ℕ) + 1) * ff a y * (((b : ℕ) + 1) * ff b y)) =
        (((α : ℚ) + 1) * (β + 1)) * (((a : ℕ) + 1) * ((b : ℕ) + 1)) *
          (WtH (α + 1) (β + 1) n y * ff a y * ff b y) := fun y hy => by
      have t := tildeH α β (show y ≤ n by have := Finset.mem_range.1 hy; omega)
      linear_combination (((a : ℕ) + 1) * ff a y * (((b : ℕ) + 1) * ff b y)) * t
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
    ring
  have hdetH : H'.det = ((α + β + (n + 1) + 1).choose (n + 1) : ℚ) *
      ((-(((α : ℚ) + 1) * ((β : ℚ) + 1))) ^ j * ((j.factorial : ℚ) ^ 2 * hkH (α + 1) (β + 1) n j)) := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have h0 : ∀ i : Fin j, H' i.succ 0 = 0 := fun i => col_zeroH α β (n + 1) i
    simp only [h0, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul, Finset.sum_const_zero,
      add_zero]
    have h00 : H' 0 0 = ((α + β + (n + 1) + 1).choose (n + 1) : ℚ) := by
      simpa [hH', bfH] using massH α β (n + 1)
    rw [h00, hsub, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    simp only [Fintype.card_fin, prod_succ_cast, hkH]
    ring
  rw [hdetH] at hPG
  have hne : ((-1 : ℚ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ hne
  rw [neg_pow (((α : ℚ) + 1) * ((β : ℚ) + 1)) j] at hPG
  unfold hkH at hPG ⊢
  linear_combination hPG

end CatalanCore.Bordered.Hankel
