module

public import CatalanCore.Arith.Hybrid.DefGKCore

@[expose] public section
open Polynomial Finset Matrix
namespace CatalanCore.Arith.Hybrid.LemmaE

section Algebra
variable {R : Type*} [CommRing R] {ι κ : Type*}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Clear a common scalar denominator in arbitrary row and column partners. -/
theorem T_decomp_cleared (A N : Matrix ι ι R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (D : Matrix κ κ R) (g h : R) (hAN : A*N=g • 1) (hNA : N*A=g • 1)
    (Sr : Matrix κ ι R) (Sc : Matrix ι κ R) :
    h^2 • (g • D-C*N*B) =
      g • (h^2 • D-h • (Sr*B)-h • (C*Sc)+Sr*A*Sc) -
        (h • C-Sr*A)*N*(h • B-A*Sc) := by
  have key := T_decomp_gen A N (h • B) (h • C) (h^2 • D) g hAN hNA Sr Sc
  simpa only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul,
    mul_assoc, mul_comm, mul_left_comm, pow_two] using key

/-- Antisymmetry cancels the quadratic first-order contribution in every characteristic. -/
theorem weighted_difference_sum (f L : ι → R) :
    (∑ i, ∑ j, f i*f j*(L i-L j))=0 := by
  have he : (∑ i, ∑ j, f i*f j*L i) = ∑ i, ∑ j, f i*f j*L j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [he, sub_self]

/-- The two linear contributions and the quadratic difference contribution cancel. -/
theorem first_order_sum_cancel (f L : ι → R) (l c : R) :
    (∑ i, c*f i*(L i-l)) + (∑ i, c*f i*(l-L i)) -
      c*(∑ i, ∑ j, f i*f j*(L i-L j)) = 0 := by
  rw [weighted_difference_sum, mul_zero, sub_zero, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  ring
end Algebra

section Gauss
variable {p : ℕ} [Fact p.Prime] {ι κ : Type}
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Primitive polynomial denominators in partner matrices cost no Gauss valuation.
The second difference may carry arbitrary nonnegative entry weights. -/
theorem tcore_vec_T_cleared
    (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) Full.toBlocks₁₁ i j))
    (hprim : gn p (Atil p (fun _ : ι => 1) Full.toBlocks₁₁).det=1)
    (h : ℚ[X]) (hh : gn p h=1) (Sr : Matrix κ ι ℚ[X]) (Sc : Matrix ι κ ℚ[X])
    (w : κ → κ → ℕ)
    (hL : ∀ z c, gn p ((h • Full.toBlocks₂₁-Sr*Full.toBlocks₁₁) z c) ≤ p)
    (hR : ∀ c y, gn p ((h • Full.toBlocks₁₂-Full.toBlocks₁₁*Sc) c y) ≤ p)
    (hΔ : ∀ z y, GLE p (w z y) ((h^2 • Full.toBlocks₂₂-h • (Sr*Full.toBlocks₁₂)-
      h • (Full.toBlocks₂₁*Sc)+Sr*Full.toBlocks₁₁*Sc) z y)) (z y : κ) :
    GLE p (w z y) (Tscaled (Atil p (fun _ : ι => 1) Full.toBlocks₁₁).det Full.toBlocks₁₁
      Full.toBlocks₁₂ Full.toBlocks₂₁ Full.toBlocks₂₂
      (Nmat p (fun _ : ι => 1) Full.toBlocks₁₁) z y) := by
  classical
  let A := Full.toBlocks₁₁
  let d : ι → ℕ := fun _ => 1
  let g := (Atil p d A).det
  have key := T_decomp_cleared A (Nmat p d A) Full.toBlocks₁₂ Full.toBlocks₂₁
    Full.toBlocks₂₂ g h (AN_eq p d A) (NA_eq p d A) Sr Sc
  have hh2 : gn p (h^2)=1 := by rw [gn_pow, hh, one_pow]
  rw [gle_iff_gn]
  have hn (f : ℚ[X]) : gn p (h^2*f)=gn p f := by rw [gn_mul, hh2, one_mul]
  rw [← hn]
  apply (gle_iff_gn p (w z y) _).mp
  change GLE p (w z y) ((h^2 • (g • Full.toBlocks₂₂-
    Full.toBlocks₂₁*Nmat p d A*Full.toBlocks₁₂)) z y)
  rw [key, Matrix.sub_apply]
  have h1 : GLE p (w z y) ((g • (h^2 • Full.toBlocks₂₂-h • (Sr*Full.toBlocks₁₂)-
      h • (Full.toBlocks₂₁*Sc)+Sr*A*Sc)) z y) := by
    rw [Matrix.smul_apply, smul_eq_mul]
    rw [gle_iff_gn, gn_mul, hprim, one_mul]
    exact (gle_iff_gn p (w z y) _).mp (hΔ z y)
  have h2 : GLE p (w z y) (((h • Full.toBlocks₂₁-Sr*A)*Nmat p d A*
      (h • Full.toBlocks₁₂-A*Sc)) z y) := by
    apply GLE.mono (B := 0) (Nat.zero_le _)
    rw [gle_iff_gn]
    simp only [pow_zero]
    have hadj : ∀ i j, Int1 p ((Atil p d A).adjugate i j) := adj_int1 hI
    have he : (h • Full.toBlocks₂₁-Sr*A)*Nmat p d A*(h • Full.toBlocks₁₂-A*Sc) =
        ((h • Full.toBlocks₂₁-Sr*A)*scl p d)*(Atil p d A).adjugate*
          (scl p d*(h • Full.toBlocks₁₂-A*Sc)) := by
      simp only [Nmat, Matrix.mul_assoc]
    rw [he]
    have hl : ∀ i j, Int1 p (((h • Full.toBlocks₂₁-Sr*A)*scl p d) i j) := by
      intro i j
      simp only [scl, Matrix.mul_diagonal]
      exact int1_mul_Cp p (hL i j)
    have hr : ∀ i j, Int1 p ((scl p d*(h • Full.toBlocks₁₂-A*Sc)) i j) := by
      intro i j
      simp only [scl, Matrix.diagonal_mul]
      exact int1_Cp_mul p (hR i j)
    exact matmul_int1 p (fun i j => matmul_int1 p hl hadj i j) hr z y
  rw [gle_iff_gn]
  exact (gn_sub_le (p := p) _ _).trans (max_le ((gle_iff_gn p _ _).mp h1)
    ((gle_iff_gn p _ _).mp h2))
end Gauss

#print axioms tcore_vec_T_cleared
#print axioms first_order_sum_cancel
end CatalanCore.Arith.Hybrid.LemmaE
