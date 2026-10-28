module

public import CatalanCore.Uniform.Content.UFWedge.Cert

@[expose] public section

/-!
# UF families: determinants by LU certificate (lane H10)

`detN` (Laplace) costs `O(m!)` kernel steps (27 s at `7 × 7`).  A determinant value `d` of an integer
`n × n` matrix `B` is instead *certified* by integer matrices `Lz` (lower triangular), `Uz` (upper
triangular) with `Lz · B = Uz`: then `det B · ∏ Lz_ii = ∏ Uz_ii`.  The check is `O(n³)` integer
multiplications (`luOK`, a `Bool`), the data `Lz`, `Uz` are produced by exact Gaussian elimination
(fraction free after row scaling).
-/

open Matrix Finset

namespace CatalanCore.Uniform.Content.UFFamily

open CatalanCore.Uniform.Content.UFWedge

/-- Product of `f 0, …, f (n-1)` (structural). -/
def prodN : ℕ → (ℕ → ℤ) → ℤ
  | 0, _ => 1
  | n + 1, f => f n * prodN n f

theorem prodN_eq (n : ℕ) (f : ℕ → ℤ) : prodN n f = ∏ i : Fin n, f i := by
  induction n with
  | zero => simp [prodN]
  | succ n ih => rw [prodN, Fin.prod_univ_castSucc, ih]; simp [mul_comm]

/-- The certificate check: `Lz · B = Uz`, `Lz` lower, `Uz` upper triangular (all on `ℕ`-indexed entries). -/
def luOK (n : ℕ) (B Lz Uz : ℕ → ℕ → ℤ) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    (sumN n fun k => Lz i k * B k j) == Uz i j &&
    (if i < j then Lz i j == 0 else true) && (if j < i then Uz i j == 0 else true)

theorem luOK_det (n : ℕ) (B Lz Uz : ℕ → ℕ → ℤ) (h : luOK n B Lz Uz = true) :
    (Matrix.of fun a b : Fin n => B a b).det * prodN n (fun i => Lz i i) = prodN n (fun i => Uz i i) := by
  have h' : ∀ i j : Fin n, (∑ k : Fin n, Lz i k * B k j) = Uz i j ∧ (i < j → Lz i j = 0) ∧
      (j < i → Uz i j = 0) := by
    intro i j
    have := h
    unfold luOK at this
    rw [List.all_eq_true] at this
    have h1 := this i (List.mem_range.2 i.2)
    rw [List.all_eq_true] at h1
    have h2 := h1 j (List.mem_range.2 j.2)
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    obtain ⟨⟨h3, h4⟩, h5⟩ := h2
    have e := sumN_eq n (fun k => Lz i k * B k j)
    refine ⟨by rw [← e]; exact h3, fun hij => ?_, fun hji => ?_⟩
    · have : (i : ℕ) < j := hij
      simpa [this] using h4
    · have : (j : ℕ) < i := hji
      simpa [this] using h5
  set L : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => Lz a b
  set U : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => Uz a b
  set Bm : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun a b => B a b
  have hLB : L * Bm = U := by
    ext i j
    simp only [Matrix.mul_apply, L, Bm, U, Matrix.of_apply]
    exact (h' i j).1
  have hL : L.IsLowerTriangular := fun i j hij => (h' i j).2.1 hij
  have hU : U.IsUpperTriangular := fun i j hij => (h' i j).2.2 hij
  have h1 : L.det = ∏ i, L i i := Matrix.det_of_isLowerTriangular L hL
  have h2 : U.det = ∏ i, U i i := Matrix.det_of_isUpperTriangular hU
  have := congrArg Matrix.det hLB
  rw [Matrix.det_mul, h1, h2] at this
  rw [prodN_eq, prodN_eq]
  simpa [L, U, mul_comm] using this.symm.symm

end CatalanCore.Uniform.Content.UFFamily
