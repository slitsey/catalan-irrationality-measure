module

public import CatalanCore.Arith.Hybrid.PrincipalMinor
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section
set_option Elab.async false

/-! # `trop_cell`: the level lemma as one statement (wave H2c; ledger S12)

Lemma 5.1 of `SUPPORT-THEOREM-2026-11-07.md` (and its refinement Lemma 5.1′ of
`DIP-RANK-CLOSED-FORM-2026-11-07.md`) in one theorem for every matrix of polynomials, every prime and every
row.  The entry analysis (which weight `w(x, y)` an entry has, from the levels `V`, `U` of the poles) is the
input `hW`; the lemma is the passage from entry weights to the price of the determinant:

* `trop_cell`: if entry `(a, b)` of `M` is `p^{W a b}`-integral and `W a b ≤ u a + v b` for rational
  potentials `u, v`, then `det M` is `p^B`-integral for every `B ≥ ∑ u + ∑ v` (potentials constant on the
  atoms of a cell are an affine price in `p / r`; half-integers are allowed);
* `trop_cell_sub`: the same for the principal restriction along an embedding (the members of a family: the
  retained common nodes with the full border), with the sums over the retained index set;
* `trop_cell_gauge`: Lemma 5.1′.  If `E₁`, `E₂` have determinant `1` (unimodular row and column operations
  with constant coefficients), the hypotheses are asked of `E₁ M E₂` and the conclusion is for `M`;
  `pivotRowGauge`, `pivotColGauge` are the pivot gauges of 5.1′ (row `x ↦ x - λ_x · row (π x)`, each pivot
  `π x < x` never pivoted itself), with `det = 1` (`det_pivotRowGauge`, `det_pivotColGauge`) and the entries
  of the gauged matrix (`pivotRowGauge_mul_apply`, `mul_pivotColGauge_apply`).

Lemma 5.1 is the case `E₁ = E₂ = 1`; the refined in-fibre weight `2 · 1[V(x) ≠ V(y)]` of 5.1′ (R) and the
zero weight of the pivot entries (iii) are values of `W`, not changes of the lemma. -/

open Finset Polynomial Matrix CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.BankShared.KTerm

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`trop_cell`** (Lemma 5.1). -/
theorem trop_cell (M : Matrix ι ι ℚ[X]) (W : ι → ι → ℕ) (hW : ∀ a b, GLE p (W a b) (M a b))
    (u v : ι → ℚ) (hd : ∀ a b, (W a b : ℚ) ≤ u a + v b) {B : ℕ} (hB : ∑ a, u a + ∑ b, v b ≤ B) :
    GLE p B M.det :=
  (det_gle M W hW).mono (tropVal_le_of_dual W u v hd hB)

/-- **`trop_cell` for a principal restriction**: a member of a family keeps the rows and columns `e a`. -/
theorem trop_cell_sub {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ↪ ι)
    (M : Matrix ι ι ℚ[X]) (W : ι → ι → ℕ) (hW : ∀ a b, GLE p (W a b) (M a b))
    (u v : ι → ℚ) (hd : ∀ a b, (W a b : ℚ) ≤ u a + v b) {B : ℕ}
    (hB : ∑ a : κ, u (e a) + ∑ b : κ, v (e b) ≤ B) :
    GLE p B (M.submatrix e e).det :=
  trop_cell (M.submatrix e e) (fun a b => W (e a) (e b)) (fun a b => hW (e a) (e b))
    (fun a => u (e a)) (fun b => v (e b)) (fun a b => hd (e a) (e b)) hB

/-- **Lemma 5.1′**: the price of `det M` from the entries of a gauged matrix `E₁ M E₂`, `det E₁ = det E₂ = 1`. -/
theorem trop_cell_gauge (M E₁ E₂ : Matrix ι ι ℚ[X]) (h₁ : E₁.det = 1) (h₂ : E₂.det = 1)
    (W : ι → ι → ℕ) (hW : ∀ a b, GLE p (W a b) ((E₁ * M * E₂) a b))
    (u v : ι → ℚ) (hd : ∀ a b, (W a b : ℚ) ≤ u a + v b) {B : ℕ} (hB : ∑ a, u a + ∑ b, v b ≤ B) :
    GLE p B M.det := by
  have h : (E₁ * M * E₂).det = M.det := by
    rw [Matrix.det_mul, Matrix.det_mul, h₁, h₂, one_mul, mul_one]
  rw [← h]
  exact trop_cell (E₁ * M * E₂) W hW u v hd hB

section Pivot

variable {R : Type*} [CommRing R] [LinearOrder ι]

/-- The row pivot gauge: row `x` becomes `row x - l x · row a` when `π x = some a`. -/
def pivotRowGauge (π : ι → Option ι) (l : ι → R) : Matrix ι ι R :=
  1 - Matrix.of fun x y => if π x = some y then l x else 0

/-- The column pivot gauge: column `y` becomes `col y - l y · col a` when `π y = some a`. -/
def pivotColGauge (π : ι → Option ι) (l : ι → R) : Matrix ι ι R :=
  1 - Matrix.of fun a y => if π y = some a then l y else 0

/-- The row gauge has determinant `1` when every pivot lies below the pivoted node. -/
theorem det_pivotRowGauge (π : ι → Option ι) (l : ι → R) (hπ : ∀ x y, π x = some y → y < x) :
    (pivotRowGauge π l).det = 1 := by
  have hlow : (pivotRowGauge π l).IsLowerTriangular := by
    intro i j hij
    have hij' : i < j := hij
    have h1 : (1 : Matrix ι ι R) i j = 0 := Matrix.one_apply_ne hij'.ne
    have h2 : π i ≠ some j := fun h => absurd (hπ i j h) (not_lt.2 hij'.le)
    simp [pivotRowGauge, h1, h2]
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  refine Finset.prod_eq_one fun i _ => ?_
  have h2 : π i ≠ some i := fun h => absurd (hπ i i h) (lt_irrefl _)
  simp [pivotRowGauge, h2]

/-- The column gauge has determinant `1` when every pivot lies below the pivoted node. -/
theorem det_pivotColGauge (π : ι → Option ι) (l : ι → R) (hπ : ∀ x y, π x = some y → y < x) :
    (pivotColGauge π l).det = 1 := by
  have hup : (pivotColGauge π l).IsUpperTriangular := by
    intro i j hij
    have hij' : j < i := hij
    have h1 : (1 : Matrix ι ι R) i j = 0 := Matrix.one_apply_ne hij'.ne'
    have h2 : π j ≠ some i := fun h => absurd (hπ j i h) (not_lt.2 hij'.le)
    simp [pivotColGauge, h1, h2]
  rw [Matrix.det_of_isUpperTriangular hup]
  refine Finset.prod_eq_one fun i _ => ?_
  have h2 : π i ≠ some i := fun h => absurd (hπ i i h) (lt_irrefl _)
  simp [pivotColGauge, h2]

/-- Entry of the row-gauged matrix. -/
theorem pivotRowGauge_mul_apply (π : ι → Option ι) (l : ι → R) (hπ : ∀ x y, π x = some y → y < x)
    (M : Matrix ι ι R) (x b : ι) :
    (pivotRowGauge π l * M) x b = M x b - (match π x with | some a => l x * M a b | none => 0) := by
  unfold pivotRowGauge
  rw [Matrix.sub_mul, Matrix.sub_apply, Matrix.one_mul]
  congr 1
  rw [Matrix.mul_apply]
  rcases h : π x with _ | a
  · simp [h]
  · rw [Finset.sum_eq_single a]
    · simp [h]
    · intro y _ hy
      have : (some a : Option ι) ≠ some y := fun e => hy (Option.some.inj e).symm
      simp [h, this]
    · intro hn; exact absurd (Finset.mem_univ a) hn

/-- Entry of the column-gauged matrix. -/
theorem mul_pivotColGauge_apply (π : ι → Option ι) (l : ι → R) (M : Matrix ι ι R) (a y : ι) :
    (M * pivotColGauge π l) a y = M a y - (match π y with | some b => l y * M a b | none => 0) := by
  unfold pivotColGauge
  rw [Matrix.mul_sub, Matrix.sub_apply, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_apply]
  rcases h : π y with _ | b
  · simp [h]
  · rw [Finset.sum_eq_single b]
    · simp [h, mul_comm]
    · intro z _ hz
      have : (some b : Option ι) ≠ some y ∨ True := Or.inr trivial
      by_cases hzy : π y = some z
      · exact absurd (by rw [h] at hzy; exact (Option.some.inj hzy).symm) hz
      · simp [hzy]
    · intro hn; exact absurd (Finset.mem_univ b) hn

end Pivot

end CatalanCore.Uniform.Content.BankShared.KTerm

#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.trop_cell
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.trop_cell_sub
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.trop_cell_gauge
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.det_pivotRowGauge
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.det_pivotColGauge
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.pivotRowGauge_mul_apply
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.mul_pivotColGauge_apply
