module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public meta import Lean.Elab.Tactic.Omega

@[expose] public section

open scoped BigOperators

namespace CatalanCore.Linalg

private theorem mul_initial {K : Type*} [Field K]
    (x y : HahnSeries ℤ K) (a b : ℤ)
    (hx : ∀ e < a, x.coeff e = 0) (hy : ∀ e < b, y.coeff e = 0) :
    (∀ e < a+b, (x*y).coeff e = 0) ∧ (x*y).coeff (a+b) = x.coeff a*y.coeff b := by
  classical
  constructor
  · intro e he
    rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro uv huv
    rcases Finset.mem_antidiagonal.mp huv with ⟨hu,hv,hs⟩
    change x.coeff uv.1 ≠ 0 at hu
    change y.coeff uv.2 ≠ 0 at hv
    have hau : a ≤ uv.1 := le_of_not_gt (fun h => hu (hx _ h))
    have hbv : b ≤ uv.2 := le_of_not_gt (fun h => hv (hy _ h))
    omega
  · rw [HahnSeries.coeff_mul]
    refine Finset.sum_eq_single (a,b) ?_ ?_
    · intro uv huv hne
      rcases Finset.mem_antidiagonal.mp huv with ⟨hu,hv,hs⟩
      change x.coeff uv.1 ≠ 0 at hu
      change y.coeff uv.2 ≠ 0 at hv
      have hau : a ≤ uv.1 := le_of_not_gt (fun h => hu (hx _ h))
      have hbv : b ≤ uv.2 := le_of_not_gt (fun h => hv (hy _ h))
      have heq : uv = (a,b) := Prod.ext (by omega) (by omega)
      exact False.elim (hne heq)
    · intro hnot
      by_cases ha : x.coeff a = 0
      · simp only [ha, zero_mul]
      by_cases hb : y.coeff b = 0
      · simp only [hb, mul_zero]
      exact False.elim (hnot (Finset.mem_antidiagonal.mpr ⟨ha,hb,rfl⟩))

private theorem prod_initial {K ι : Type*} [Field K]
    (s : Finset ι) (f : ι → HahnSeries ℤ K) (w : ι → ℤ) :
    (∀ i ∈ s, ∀ e < w i, (f i).coeff e = 0) →
    (∀ e < ∑ i ∈ s, w i, (∏ i ∈ s, f i).coeff e = 0) ∧
      (∏ i ∈ s, f i).coeff (∑ i ∈ s, w i) = ∏ i ∈ s, (f i).coeff (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Finset.prod_empty]
    constructor
    · intro e he
      rw [HahnSeries.coeff_one, ite_eq_right (ne_of_lt he)]
    · simp [HahnSeries.coeff_one]
  | @insert i s hi ih =>
    intro h
    have hhead := h i (Finset.mem_insert_self _ _)
    have hrest := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    have hm := mul_initial (f i) (∏ j ∈ s, f j) (w i) (∑ j ∈ s, w j) hhead hrest.1
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact ⟨hm.1,hm.2.trans (congrArg ((f i).coeff (w i)*·) hrest.2)⟩

private theorem coeff_sum {K ι : Type*} [Field K] (s : Finset ι)
    (f : ι → HahnSeries ℤ K) (e : ℤ) :
    (∑ i ∈ s, f i).coeff e = ∑ i ∈ s, (f i).coeff e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, HahnSeries.coeff_add, ih]

/-- Row and column lower potentials determine the first possible determinant
coefficient, including the case where that coefficient itself vanishes. -/
theorem det_potential_coeff {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (HahnSeries ℤ K)) (r c : ι → ℤ)
    (h : ∀ i j e, e < r i+c j → (M i j).coeff e = 0) :
    (∀ e, e < (∑ i, r i)+(∑ j, c j) → M.det.coeff e = 0) ∧
      M.det.coeff ((∑ i, r i)+(∑ j, c j)) =
        Matrix.det (fun i j => (M i j).coeff (r i+c j)) := by
  classical
  let S : ℤ := (∑ i, r i)+(∑ j, c j)
  let N : Matrix ι ι K := fun i j => (M i j).coeff (r i+c j)
  change (∀ e, e<S → M.det.coeff e=0) ∧ M.det.coeff S=N.det
  have hp (σ : Equiv.Perm ι) :=
    prod_initial Finset.univ (fun i => M (σ i) i) (fun i => r (σ i)+c i)
      (fun i _ e he => h (σ i) i e he)
  have hw (σ : Equiv.Perm ι) : (∑ i, (r (σ i)+c i)) = S := by
    rw [Finset.sum_add_distrib, Equiv.sum_comp σ]
  constructor
  · intro e he
    rw [Matrix.det_apply M, coeff_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [HahnSeries.coeff_smul, (hp σ).1 e (by simpa only [hw] using he), smul_zero]
  · rw [Matrix.det_apply M, coeff_sum, Matrix.det_apply N]
    apply Finset.sum_congr rfl
    intro σ _
    change (Equiv.Perm.sign σ • ∏ i, M (σ i) i).coeff S =
      Equiv.Perm.sign σ • ∏ i, (M (σ i) i).coeff (r (σ i)+c i)
    rw [HahnSeries.coeff_smul]
    congr 1
    simpa only [hw] using (hp σ).2

end CatalanCore.Linalg
