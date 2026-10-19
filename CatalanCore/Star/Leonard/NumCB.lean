module

public import CatalanCore.Star.Leonard.DeltaCB
public import CatalanCore.Star.Leonard.LemmaN
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Evaluation of `Num` (package H6): the `(N+1) × N` Cauchy-Binet sum

For `N = K - 1`, the sum over `N`-subsets of `Fin (N+1)` is a sum over the omitted node `a`, and
`V(P_a)² = V_K² / (a! (N-a)!)²`.  With `Σ_a C(N,a)² (x+a)_{2N} = C(2N,N)((x+N)_N)²` (Lemma N):

`det (C_Aᵀ C_B) = V(A) V(B) V_K² ∏_b ρ(b) · C(2N,N) ((x+N)_N)² / N!²`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

lemma Vprod_cons {k : ℕ} (x : F) (w : Fin k → F) :
    Vprod (Fin.cons x w : Fin (k + 1) → F) = (∏ i, (w i - x)) * Vprod w := by
  unfold Vprod
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fin.prod_Ioi_succ]
  simp [Fin.cons_succ]

lemma Vprod_sq_perm {k : ℕ} (v : Fin k → F) (σ : Equiv.Perm (Fin k)) :
    Vprod (v ∘ σ) ^ 2 = Vprod v ^ 2 := by
  have h1 : ∀ w : Fin k → F, Vprod w = (Matrix.vandermonde w).det := fun w => by
    rw [Matrix.det_vandermonde]; rfl
  have h2 : Matrix.vandermonde (v ∘ σ) = (Matrix.vandermonde v).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde]
  rw [h1, h1, h2, Matrix.det_permute]
  have : ((Equiv.Perm.sign σ : ℤˣ) : ℤ) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h3 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : F) ^ 2 = 1 := by
    have := congrArg (Int.cast : ℤ → F) this
    simpa using this
  rw [mul_pow, h3, one_mul]

lemma Vprod_sq_succAbove {k : ℕ} (v : Fin (k + 1) → F) (a : Fin (k + 1)) :
    Vprod v ^ 2 = Vprod (fun i => v (a.succAbove i)) ^ 2 * (∏ i, (v (a.succAbove i) - v a)) ^ 2 := by
  let τ : Fin (k + 1) → Fin (k + 1) := Fin.cons a a.succAbove
  have hinj : Function.Injective τ := by
    intro i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j' => simp [τ] at hij
    | succ i' =>
      induction j using Fin.cases with
      | zero => simp [τ] at hij
      | succ j' =>
        simp [τ] at hij
        exact congrArg Fin.succ hij
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)
  have hcons : (v ∘ σ) = (Fin.cons (v a) (fun i => v (a.succAbove i)) : Fin (k + 1) → F) := by
    funext i
    induction i using Fin.cases with
    | zero => simp [σ, τ]
    | succ i' => simp [σ, τ]
  have := Vprod_sq_perm v σ
  rw [← this, hcons, Vprod_cons, mul_pow, mul_comm]

lemma prod_range_sub_fact [CharZero F] (a : ℕ) :
    ∏ b ∈ Finset.range a, ((a : F) - (b : F)) = ((a.factorial : ℕ) : F) := by
  rw [← Finset.prod_range_reflect (fun b : ℕ => (a : F) - (b : F)) a, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine Finset.prod_congr rfl fun j hj => ?_
  have := Finset.mem_range.1 hj
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma prod_range_sub_sq [CharZero F] (a : ℕ) :
    (∏ b ∈ Finset.range a, ((b : F) - (a : F))) ^ 2 = ((a.factorial : ℕ) : F) ^ 2 := by
  have h : ∏ b ∈ Finset.range a, ((b : F) - (a : F)) = (-1) ^ a * ((a.factorial : ℕ) : F) := by
    have h1 : ∏ b ∈ Finset.range a, ((b : F) - (a : F)) =
        ∏ b ∈ Finset.range a, (-1 : F) * ((a : F) - b) := by
      refine Finset.prod_congr rfl fun b _ => by ring
    rw [h1, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, prod_range_sub_fact]
  rw [h, mul_pow, ← pow_mul, mul_comm a 2, pow_mul]
  simp

lemma prod_Ico_sub_fact [CharZero F] (a N : ℕ) (h : a ≤ N) :
    ∏ b ∈ Finset.Ico (a + 1) (N + 1), ((b : F) - (a : F)) = (((N - a).factorial : ℕ) : F) := by
  rw [Finset.prod_Ico_eq_prod_range, show N + 1 - (a + 1) = N - a by omega,
    ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  push_cast; ring

lemma prod_succAbove_sq [CharZero F] (N : ℕ) (a : Fin (N + 1)) :
    (∏ i : Fin N, ((((a.succAbove i : Fin (N + 1)) : ℕ) : F) - ((a : ℕ) : F))) ^ 2 =
      ((((a : ℕ).factorial * (N - (a : ℕ)).factorial : ℕ)) : F) ^ 2 := by
  have h1 : ∏ i : Fin N, ((((a.succAbove i : Fin (N + 1)) : ℕ) : F) - ((a : ℕ) : F)) =
      ∏ b : Fin (N + 1), (if (b : ℕ) = (a : ℕ) then (1 : F) else (((b : ℕ) : F) - ((a : ℕ) : F))) := by
    rw [Fin.prod_univ_succAbove _ a]
    simp only [if_true]
    rw [one_mul]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [if_neg]
    intro h
    exact Fin.succAbove_ne a i (Fin.ext h)
  rw [h1, Fin.prod_univ_eq_prod_range
    (fun b : ℕ => if b = (a : ℕ) then (1 : F) else ((b : F) - ((a : ℕ) : F))) (N + 1)]
  have ha : (a : ℕ) ≤ N := Nat.lt_succ_iff.1 a.2
  rw [Finset.range_eq_Ico, ← Finset.prod_Ico_consecutive _ (Nat.zero_le (a : ℕ))
    (by omega : (a : ℕ) ≤ N + 1), Finset.prod_eq_prod_Ico_succ_bot (by omega : (a : ℕ) < N + 1)]
  have e1 : ∏ b ∈ Finset.Ico 0 (a : ℕ), (if b = (a : ℕ) then (1 : F) else ((b : F) - ((a : ℕ) : F))) =
      ∏ b ∈ Finset.range (a : ℕ), ((b : F) - ((a : ℕ) : F)) := by
    rw [Finset.range_eq_Ico]
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [if_neg]
    have := (Finset.mem_Ico.1 hb).2
    omega
  have e2 : ∏ b ∈ Finset.Ico ((a : ℕ) + 1) (N + 1),
      (if b = (a : ℕ) then (1 : F) else ((b : F) - ((a : ℕ) : F))) =
        ∏ b ∈ Finset.Ico ((a : ℕ) + 1) (N + 1), ((b : F) - ((a : ℕ) : F)) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [if_neg]
    have := (Finset.mem_Ico.1 hb).1
    omega
  rw [e1, if_pos rfl, one_mul, e2, prod_Ico_sub_fact (a : ℕ) N ha, mul_pow, prod_range_sub_sq]
  push_cast
  ring

/-! ### Sum over `N`-subsets of `Fin (N+1)` = sum over the omitted node -/

lemma sum_subsets_erase {N : ℕ} {M : Type*} [AddCommMonoid M]
    (f : {P : Finset (Fin (N + 1)) // P.card = N} → M) :
    ∑ P, f P = ∑ a : Fin (N + 1), f ⟨Finset.univ.erase a, by simp⟩ := by
  let e : Fin (N + 1) → {P : Finset (Fin (N + 1)) // P.card = N} :=
    fun a => ⟨Finset.univ.erase a, by simp⟩
  have hinj : Function.Injective e := by
    intro a b hab
    have h : Finset.univ.erase a = Finset.univ.erase b := congrArg Subtype.val hab
    by_contra hne
    have : a ∈ Finset.univ.erase b := Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩
    rw [← h] at this
    simp at this
  have hbij : Function.Bijective e := (Fintype.bijective_iff_injective_and_card e).2
    ⟨hinj, by simp [Fintype.card_subtype, Finset.card_univ]⟩
  exact (Fintype.sum_equiv (Equiv.ofBijective e hbij) _ _ (fun a => rfl)).symm

lemma colsOf_erase {N : ℕ} (a : Fin (N + 1)) (i : Fin N) :
    (CatalanCore.colsOf (⟨Finset.univ.erase a, by simp⟩ :
      {P : Finset (Fin (N + 1)) // P.card = N}) i) = a.succAbove i := by
  have h := Finset.orderEmbOfFin_unique (s := Finset.univ.erase a) (k := N) (by simp)
    (f := a.succAbove) (fun x => Finset.mem_erase.2 ⟨Fin.succAbove_ne a x, Finset.mem_univ _⟩)
    (Fin.strictMono_succAbove a)
  exact (congrFun h i).symm

/-- **`Num` in closed form** (Cauchy-Binet over the omitted node + Lemma N). -/
theorem Num_closed [CharZero F] {N : ℕ} (hN : 1 ≤ N) (xs ys : Fin N → F) (x0 : F)
    (hx : ∀ (a : Fin (N + 1)) (i : Fin N), ((a : ℕ) : F) + xs i ≠ 0)
    (hy : ∀ (a : Fin (N + 1)) (i : Fin N), ((a : ℕ) : F) + ys i ≠ 0)
    (hrho : ∀ b : ℕ, ∏ j, (((b : F) + xs j) * ((b : F) + ys j)) =
      ∏ i ∈ Finset.range (2 * N), (x0 + (b : F) + (i : F))) :
    ((Cm (N + 1) xs)ᵀ * Cm (N + 1) ys).det =
      Vprod xs * Vprod ys * Vprod (fun i : Fin (N + 1) => ((i : ℕ) : F)) ^ 2 *
        (∏ b : Fin (N + 1), (∏ i ∈ Finset.range (2 * N), (x0 + ((b : ℕ) : F) + (i : F)))⁻¹) *
        ((((2 * N).choose N : ℕ) : F) * (∏ i ∈ Finset.range N, (x0 + (N : F) + (i : F))) ^ 2 /
          ((N.factorial : ℕ) : F) ^ 2) := by
  rw [delta_CB xs ys hx hy, sum_subsets_erase]
  set pc : ℕ → F := fun b => ∏ i ∈ Finset.range (2 * N), (x0 + (b : F) + (i : F)) with hpc
  have hpc_ne : ∀ b : Fin (N + 1), pc b ≠ 0 := by
    intro b
    rw [hpc]; simp only
    rw [← hrho]
    exact Finset.prod_ne_zero_iff.2 fun j _ => mul_ne_zero (hx b j) (hy b j)
  have hrho' : ∀ b : ℕ, rho xs ys b = (pc b)⁻¹ := fun b => by
    unfold rho; rw [hrho b]
  -- each term
  have hterm : ∀ a : Fin (N + 1),
      Vprod (fun i => (((CatalanCore.colsOf (⟨Finset.univ.erase a, by simp⟩ :
          {P : Finset (Fin (N + 1)) // P.card = N}) i : Fin (N + 1)) : ℕ) : F)) ^ 2 *
        ∏ i : Fin N, rho xs ys ((CatalanCore.colsOf (⟨Finset.univ.erase a, by simp⟩ :
          {P : Finset (Fin (N + 1)) // P.card = N}) i : Fin (N + 1)) : ℕ) =
      Vprod (fun i : Fin (N + 1) => ((i : ℕ) : F)) ^ 2 * (∏ b : Fin (N + 1), (pc b)⁻¹) *
        (((N.choose a : ℕ) : F) ^ 2 * pc a / ((N.factorial : ℕ) : F) ^ 2) := by
    intro a
    simp only [colsOf_erase]
    set v : Fin (N + 1) → F := fun i => ((i : ℕ) : F) with hv
    have hfac : ((((a : ℕ).factorial * (N - (a : ℕ)).factorial : ℕ)) : F) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
    have hNfac : ((N.factorial : ℕ) : F) ≠ 0 := by
      exact_mod_cast (Nat.factorial_pos N).ne'
    have h1 := Vprod_sq_succAbove v a
    have h2 := prod_succAbove_sq (F := F) N a
    have hV : Vprod (fun i : Fin N => (((a.succAbove i : Fin (N + 1)) : ℕ) : F)) ^ 2 =
        Vprod v ^ 2 / ((((a : ℕ).factorial * (N - (a : ℕ)).factorial : ℕ)) : F) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hfac), h1, ← h2]
    have hP : ∏ i : Fin N, rho xs ys ((a.succAbove i : Fin (N + 1)) : ℕ) =
        (∏ b : Fin (N + 1), (pc b)⁻¹) * pc a := by
      have := Fin.prod_univ_succAbove (fun b : Fin (N + 1) => (pc (b : ℕ))⁻¹) a
      simp only [hrho'] 
      rw [this]
      field_simp [hpc_ne a]
    have hC : ((N.choose a : ℕ) : F) * ((a : ℕ).factorial : ℕ) * (((N - (a : ℕ)).factorial : ℕ) : F) =
        ((N.factorial : ℕ) : F) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (Nat.lt_succ_iff.1 a.2)
    rw [hV, hP]
    have hfa : (((a : ℕ).factorial : ℕ) : F) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hfb : (((N - (a : ℕ)).factorial : ℕ) : F) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hCne : ((N.choose a : ℕ) : F) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.1 a.2)).ne'
    rw [← hC]
    push_cast
    field_simp
  simp only [hterm]
  rw [← Finset.mul_sum]
  have hs : ∑ a : Fin (N + 1), (((N.choose a : ℕ) : F) ^ 2 * pc a / ((N.factorial : ℕ) : F) ^ 2) =
      ((((2 * N).choose N : ℕ) : F) * (∏ i ∈ Finset.range N, (x0 + (N : F) + (i : F))) ^ 2 /
        ((N.factorial : ℕ) : F) ^ 2) := by
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun a : ℕ => ((N.choose a : ℕ) : F) ^ 2 * pc a)
      (N + 1)]
    congr 1
    exact lemmaN N hN x0
  rw [hs]
  ring

end CatalanCore.Star.Leonard
