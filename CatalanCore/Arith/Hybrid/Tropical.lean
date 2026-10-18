module

public import CatalanCore.Basic.PrimePower
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The tropical bound and weak duality (generic, no `α`)

WP-H5 step 1 (design 9.6).  Two completely generic facts:

* **Lemma trop** (`det_gle`).  Let `M` be a square matrix of polynomials over `ℚ` and `W` a table of
  natural-number weights with `p^{W a b} · coeff ∈ ℤ_(p)` for every coefficient of every entry
  (`GLE p (W a b) (M a b)`).  Then every coefficient of `det M` is `p^{tropVal W}`-integral, where
  `tropVal W` is the maximum, over permutations, of the weight of the permutation.  The proof is a
  multiplicativity statement for the Gauss valuation: no subset expansion and no extension of
  partial permutations is needed (the partial identity carrying `X` is just the entry `X` of
  weight `≥ 0`).
* **Weak duality** (`tropVal_le_dual`).  If `W a b ≤ u a + v b` then `tropVal W ≤ ∑ u + ∑ v`
  (`u, v` rational, half-integers allowed).
-/

open Finset Polynomial

namespace CatalanCore.Arith.Hybrid

open CatalanCore.Basic

/-! ### Tropical value and weak duality -/

section Trop

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The tropical determinant: the maximum weight of a permutation, matching column `b` to row
`σ b`. -/
noncomputable def tropVal (W : ι → ι → ℕ) : ℕ :=
  (Finset.univ : Finset (Equiv.Perm ι)).sup (fun σ => ∑ b, W (σ b) b)

lemma le_tropVal (W : ι → ι → ℕ) (σ : Equiv.Perm ι) : ∑ b, W (σ b) b ≤ tropVal W :=
  Finset.le_sup (f := fun σ : Equiv.Perm ι => ∑ b, W (σ b) b) (Finset.mem_univ σ)

lemma exists_tropVal (W : ι → ι → ℕ) : ∃ σ : Equiv.Perm ι, tropVal W = ∑ b, W (σ b) b := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Equiv.Perm ι))
    Finset.univ_nonempty (fun σ => ∑ b, W (σ b) b)
  exact ⟨σ, hσ⟩

lemma tropVal_le_of_forall {W : ι → ι → ℕ} {B : ℕ} (h : ∀ σ : Equiv.Perm ι, ∑ b, W (σ b) b ≤ B) :
    tropVal W ≤ B := Finset.sup_le fun σ _ => h σ

lemma tropVal_mono {W W' : ι → ι → ℕ} (h : ∀ a b, W a b ≤ W' a b) : tropVal W ≤ tropVal W' :=
  tropVal_le_of_forall fun σ =>
    (Finset.sum_le_sum fun b _ => h (σ b) b).trans (le_tropVal W' σ)

/-- Weak duality. -/
theorem tropVal_le_dual (W : ι → ι → ℕ) (u v : ι → ℚ) (h : ∀ a b, (W a b : ℚ) ≤ u a + v b) :
    (tropVal W : ℚ) ≤ ∑ a, u a + ∑ b, v b := by
  obtain ⟨σ, hσ⟩ := exists_tropVal W
  rw [hσ]
  push_cast
  calc ∑ b, (W (σ b) b : ℚ) ≤ ∑ b, (u (σ b) + v b) := Finset.sum_le_sum fun b _ => h (σ b) b
    _ = ∑ a, u a + ∑ b, v b := by
      rw [Finset.sum_add_distrib]
      congr 1
      exact Equiv.sum_comp σ u

/-- Weak duality with an integer bound read off. -/
theorem tropVal_le_of_dual (W : ι → ι → ℕ) (u v : ι → ℚ) (h : ∀ a b, (W a b : ℚ) ≤ u a + v b)
    {B : ℕ} (hB : ∑ a, u a + ∑ b, v b ≤ B) : tropVal W ≤ B := by
  have := tropVal_le_dual W u v h
  exact_mod_cast this.trans hB

/-- The tropical value of a sum of levels is at most the sum of the tropical values. -/
theorem tropVal_sum_le {κ : Type*} (s : Finset κ) (w : κ → ι → ι → ℕ) :
    tropVal (fun a b => ∑ e ∈ s, w e a b) ≤ ∑ e ∈ s, tropVal (w e) := by
  apply tropVal_le_of_forall
  intro σ
  calc ∑ b, ∑ e ∈ s, w e (σ b) b = ∑ e ∈ s, ∑ b, w e (σ b) b := Finset.sum_comm
    _ ≤ ∑ e ∈ s, tropVal (w e) := Finset.sum_le_sum fun e _ => le_tropVal (w e) σ

end Trop

/-! ### `p^B`-integrality of polynomials over `ℚ` (Gauss valuation) -/

section Gauss

variable {κ : Type*} (p : ℕ) [Fact p.Prime]

/-- `f` has all coefficients in `p^{-B} ℤ_(p)`: the Gauss valuation of `f` is `≥ -B`. -/
def GLE (B : ℕ) (f : ℚ[X]) : Prop := ∀ i, (p : ℚ) ^ B * f.coeff i ∈ LocRing p

variable {p}

lemma gle_of_int (B : ℕ) (f : ℚ[X]) (h : ∀ i, (p : ℚ) ^ B * f.coeff i ∈ LocRing p) : GLE p B f := h

lemma GLE.mono {B B' : ℕ} (h : B ≤ B') {f : ℚ[X]} (hf : GLE p B f) : GLE p B' f := by
  intro i
  have : (p : ℚ) ^ B' * f.coeff i = ((p ^ (B' - B) : ℕ) : ℚ) * ((p : ℚ) ^ B * f.coeff i) := by
    rw [← mul_assoc]
    congr 1
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) ((p ^ (B' - B) : ℕ) : ℤ))
    (hf i)

lemma GLE.zero (B : ℕ) : GLE p B 0 := by
  intro i; simp [(LocRing p).zero_mem]

lemma GLE.add {B : ℕ} {f g : ℚ[X]} (hf : GLE p B f) (hg : GLE p B g) : GLE p B (f + g) := by
  intro i
  rw [coeff_add, mul_add]
  exact (LocRing p).add_mem (hf i) (hg i)

lemma GLE.sum {B : ℕ} {s : Finset κ} {f : κ → ℚ[X]} (h : ∀ k ∈ s, GLE p B (f k)) :
    GLE p B (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GLE.zero (p := p) B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma GLE.zsmul {B : ℕ} {f : ℚ[X]} (hf : GLE p B f) (n : ℤ) : GLE p B (n • f) := by
  intro i
  rw [zsmul_eq_mul, ← C_eq_intCast, coeff_C_mul]
  have : (p : ℚ) ^ B * ((n : ℚ) * f.coeff i) = (n : ℚ) * ((p : ℚ) ^ B * f.coeff i) := by ring
  rw [this]
  exact (LocRing p).mul_mem (int_mem_locRing n) (hf i)

lemma GLE.mul {a b : ℕ} {f g : ℚ[X]} (hf : GLE p a f) (hg : GLE p b g) : GLE p (a + b) (f * g) := by
  intro n
  rw [coeff_mul, Finset.mul_sum]
  apply (LocRing p).sum_mem
  intro x _
  have : (p : ℚ) ^ (a + b) * (f.coeff x.1 * g.coeff x.2)
      = ((p : ℚ) ^ a * f.coeff x.1) * ((p : ℚ) ^ b * g.coeff x.2) := by ring
  rw [this]
  exact (LocRing p).mul_mem (hf _) (hg _)

lemma GLE.one : GLE p 0 (1 : ℚ[X]) := by
  intro i
  rw [coeff_one]
  split_ifs
  · simpa using (LocRing p).one_mem
  · simpa using (LocRing p).zero_mem

lemma GLE.prod {s : Finset κ} {f : κ → ℚ[X]} {B : κ → ℕ} (h : ∀ k ∈ s, GLE p (B k) (f k)) :
    GLE p (∑ k ∈ s, B k) (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GLE.one (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma GLE.X : GLE p 0 (X : ℚ[X]) := by
  intro i
  rw [coeff_X]
  split_ifs
  · simpa using (LocRing p).one_mem
  · simpa using (LocRing p).zero_mem

lemma GLE.C_iff {B : ℕ} {x : ℚ} : GLE p B (C x) ↔ (p : ℚ) ^ B * x ∈ LocRing p := by
  constructor
  · intro h; simpa using h 0
  · intro h i
    rw [coeff_C]
    split_ifs with hi
    · simpa using h
    · simpa using (LocRing p).zero_mem

/-- **Lemma trop.**  If entry `(a, b)` of `M` is `p^{W a b}`-integral then `det M` is
`p^{tropVal W}`-integral (coefficientwise). -/
theorem det_gle {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X]) (W : ι → ι → ℕ)
    (h : ∀ a b, GLE p (W a b) (M a b)) : GLE p (tropVal W) M.det := by
  rw [Matrix.det_apply]
  apply GLE.sum
  intro σ _
  have hprod : GLE p (∑ b, W (σ b) b) (∏ b, M (σ b) b) := GLE.prod fun b _ => h (σ b) b
  have h2 : GLE p (tropVal W) (∏ b, M (σ b) b) := hprod.mono (le_tropVal W σ)
  rw [Units.smul_def]
  exact h2.zsmul _

end Gauss

end CatalanCore.Arith.Hybrid
