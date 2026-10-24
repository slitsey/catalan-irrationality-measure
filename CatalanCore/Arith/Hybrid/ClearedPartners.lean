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

/-- **Second-order Neumann partners.** If `Q0 * adjQ = adjQ * Q0 = h` and `A = Q0 + O`, the left
partner `Sr = C adjQ (h - O adjQ)` satisfies `h² C - Sr A = C adjQ O adjQ O`: the residual is
quadratic in the off-block part `O`. -/
theorem neumann_residual_left (Q0 O adjQ : Matrix ι ι R) (C : Matrix κ ι R) (h : R)
    (hQ' : adjQ * Q0 = h • 1) :
    h^2 • C - (C * adjQ * (h • (1 : Matrix ι ι R) - O * adjQ)) * (Q0 + O) =
      C * adjQ * O * adjQ * O := by
  have e1 : (h • (1 : Matrix ι ι R) - O * adjQ) * (Q0 + O) =
      h • Q0 - O * adjQ * O := by
    have : O * adjQ * Q0 = h • O := by
      rw [Matrix.mul_assoc, hQ', Matrix.mul_smul, Matrix.mul_one]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.one_mul, this]
    abel
  have e2 : C * adjQ * (h • Q0) = h^2 • C := by
    rw [Matrix.mul_smul, Matrix.mul_assoc, hQ', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      pow_two]
  rw [Matrix.mul_assoc, e1, Matrix.mul_sub, e2]
  simp only [Matrix.mul_assoc, sub_sub_cancel]

/-- The right-hand analogue: `Sc = (h - adjQ O) adjQ B` gives `h² B - A Sc = O adjQ O adjQ B`. -/
theorem neumann_residual_right (Q0 O adjQ : Matrix ι ι R) (B : Matrix ι κ R) (h : R)
    (hQ : Q0 * adjQ = h • 1) :
    h^2 • B - (Q0 + O) * ((h • (1 : Matrix ι ι R) - adjQ * O) * adjQ * B) =
      O * adjQ * O * adjQ * B := by
  have e1 : (Q0 + O) * (h • (1 : Matrix ι ι R) - adjQ * O) =
      h • Q0 - O * adjQ * O := by
    have : Q0 * adjQ * O = h • O := by
      rw [hQ, Matrix.smul_mul, Matrix.one_mul]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc,
      this, smul_add]
    abel
  have e3 : (Q0 + O) * ((h • (1 : Matrix ι ι R) - adjQ * O) * adjQ * B) =
      h^2 • B - O * adjQ * O * adjQ * B := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1]
    simp only [Matrix.sub_mul, Matrix.smul_mul, hQ, Matrix.one_mul, smul_smul, pow_two]
  rw [e3]
  abel

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

lemma gn_sum_le_const {J : Type*} (s : Finset J) (f : J → ℚ[X]) (b : ℝ)
    (hb : 0 ≤ b) (hf : ∀ j∈s, gn p (f j) ≤ b) : gn p (∑ j∈s,f j) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [gn_zero] using hb
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (gn_add_le _ _).trans (max_le (hf j (by simp))
      (ih (fun k hk => hf k (by simp [hk]))))

/-- Gauss-norm bound for a matrix product entry. -/
lemma gn_matmul_le {a b c : Type*} [Fintype b] (M : Matrix a b ℚ[X]) (N : Matrix b c ℚ[X])
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hM : ∀ i j, gn p (M i j) ≤ α) (hN : ∀ i j, gn p (N i j) ≤ β) (i : a) (k : c) :
    gn p ((M * N) i k) ≤ α * β := by
  rw [Matrix.mul_apply]
  apply gn_sum_le_const _ _ _ (mul_nonneg hα hβ)
  intro j _
  rw [gn_mul]
  exact mul_le_mul (hM i j) (hN j k) (gn_nonneg p _) hα

/-- **The residual of the cleared Schur identity, at a general bound `q`.**  If the partner
defects `h C - Sr A` and `h B - A Sc` have Gauss norm `≤ q`, the residual
`(h C - Sr A) N (h B - A Sc)` has Gauss norm `≤ (q/p)²`.  With `q = p` this is the integrality used
by `tcore_vec_T_cleared`; with `q = 1` (second-order Neumann partners) it is `≡ 0 mod p²`. -/
theorem cleared_residual_gn
    (Full : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) Full.toBlocks₁₁ i j))
    (h : ℚ[X]) (Sr : Matrix κ ι ℚ[X]) (Sc : Matrix ι κ ℚ[X]) (q : ℝ) (hq : 0 ≤ q)
    (hL : ∀ z c, gn p ((h • Full.toBlocks₂₁-Sr*Full.toBlocks₁₁) z c) ≤ q)
    (hR : ∀ c y, gn p ((h • Full.toBlocks₁₂-Full.toBlocks₁₁*Sc) c y) ≤ q) (z y : κ) :
    gn p (((h • Full.toBlocks₂₁-Sr*Full.toBlocks₁₁)*Nmat p (fun _ : ι => 1) Full.toBlocks₁₁*
      (h • Full.toBlocks₁₂-Full.toBlocks₁₁*Sc)) z y) ≤ (q * (p : ℝ)⁻¹ * 1) * (q * (p : ℝ)⁻¹) := by
  classical
  let A := Full.toBlocks₁₁
  let d : ι → ℕ := fun _ => 1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hCp : gn p (C ((p : ℚ) ^ 1)) = (p : ℝ)⁻¹ := by
    rw [gn_C, pow_one, padicNorm.padicNorm_p_of_prime]; push_cast; simp
  have hadj : ∀ i j, Int1 p ((Atil p d A).adjugate i j) := adj_int1 hI
  have he : (h • Full.toBlocks₂₁-Sr*A)*Nmat p d A*(h • Full.toBlocks₁₂-A*Sc) =
      ((h • Full.toBlocks₂₁-Sr*A)*scl p d)*(Atil p d A).adjugate*
        (scl p d*(h • Full.toBlocks₁₂-A*Sc)) := by
    simp only [Nmat, Matrix.mul_assoc]
  rw [he]
  have hpq : 0 ≤ q * (p : ℝ)⁻¹ := by positivity
  have hl : ∀ i j, gn p (((h • Full.toBlocks₂₁-Sr*A)*scl p d) i j) ≤ q * (p : ℝ)⁻¹ := by
    intro i j
    simp only [scl, Matrix.mul_diagonal]
    rw [gn_mul, hCp]
    exact mul_le_mul_of_nonneg_right (hL i j) (by positivity)
  have hr : ∀ i j, gn p ((scl p d*(h • Full.toBlocks₁₂-A*Sc)) i j) ≤ q * (p : ℝ)⁻¹ := by
    intro i j
    simp only [scl, Matrix.diagonal_mul]
    rw [gn_mul, hCp, mul_comm]
    exact mul_le_mul_of_nonneg_right (hR i j) (by positivity)
  exact gn_matmul_le _ _ _ _ (mul_nonneg hpq zero_le_one) hpq
    (fun i j => gn_matmul_le _ _ _ _ hpq zero_le_one hl (fun a b => hadj a b) i j) hr z y

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
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    refine (cleared_residual_gn Full hI h Sr Sc p (Nat.cast_nonneg _) hL hR z y).trans ?_
    rw [mul_inv_cancel₀ hp0]; norm_num
  rw [gle_iff_gn]
  exact (gn_sub_le (p := p) _ _).trans (max_le ((gle_iff_gn p _ _).mp h1)
    ((gle_iff_gn p _ _).mp h2))
end Gauss

#print axioms tcore_vec_T_cleared
#print axioms first_order_sum_cancel
#print axioms neumann_residual_left
#print axioms neumann_residual_right
#print axioms cleared_residual_gn
end CatalanCore.Arith.Hybrid.LemmaE
