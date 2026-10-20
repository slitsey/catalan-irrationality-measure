module
public import CatalanCore.Arith.Hybrid.ClearedPartners
public import CatalanCore.Arith.Hybrid.LemmaE.ModelPartners
public import CatalanCore.Arith.Hybrid.LemmaE.WeightedCore
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime] {I Z : Type} [Fintype I] [DecidableEq I]
  [Fintype Z] [DecidableEq Z]
lemma gn_sum_le_const {J : Type*} (s : Finset J) (f : J → ℚ[X]) (b : ℝ)
    (hb : 0 ≤ b) (hf : ∀ j∈s, gn p (f j) ≤ b) : gn p (∑ j∈s,f j) ≤ b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [gn_zero] using hb
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (gn_add_le _ _).trans (max_le (hf j (by simp))
      (ih (fun k hk => hf k (by simp [hk]))))
lemma row_residual_bound (A A0 : Matrix I I ℚ[X]) (C C0 Sr : Matrix Z I ℚ[X])
    (h : ℚ[X]) (hh : Int1 p h) (hs : ∀ z i,Int1 p (Sr z i))
    (he : Sr*A0=h • C0) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ i j,gn p ((A0-A) i j)≤b) (hC : ∀ z i,gn p ((C-C0) z i)≤b) :
    ∀ z i,gn p ((h • C-Sr*A) z i)≤b := by
  have hid : h • C-Sr*A=h • (C-C0)+Sr*(A0-A) := by
    rw [Matrix.mul_sub, he, smul_sub]
    abel
  intro z i
  rw [hid, Matrix.add_apply]
  apply (gn_add_le _ _).trans
  apply max_le
  · rw [Matrix.smul_apply, smul_eq_mul, gn_mul]
    exact (mul_le_of_le_one_left (gn_nonneg p _) hh).trans (hC z i)
  · rw [Matrix.mul_apply]
    apply gn_sum_le_const _ _ b hb
    intro j _
    rw [gn_mul]
    exact (mul_le_of_le_one_left (gn_nonneg p _) (hs z j)).trans (hA j i)
lemma col_residual_bound (A A0 : Matrix I I ℚ[X]) (B B0 Sc : Matrix I Z ℚ[X])
    (h : ℚ[X]) (hh : Int1 p h) (hs : ∀ i z,Int1 p (Sc i z))
    (he : A0*Sc=h • B0) (b : ℝ) (hb : 0 ≤ b)
    (hA : ∀ i j,gn p ((A0-A) i j)≤b) (hB : ∀ i z,gn p ((B-B0) i z)≤b) :
    ∀ i z,gn p ((h • B-A*Sc) i z)≤b := by
  have hid : h • B-A*Sc=h • (B-B0)+(A0-A)*Sc := by
    rw [Matrix.sub_mul, he, smul_sub]
    abel
  intro i z
  rw [hid, Matrix.add_apply]
  apply (gn_add_le _ _).trans
  apply max_le
  · rw [Matrix.smul_apply, smul_eq_mul, gn_mul]
    exact (mul_le_of_le_one_left (gn_nonneg p _) hh).trans (hB i z)
  · rw [Matrix.mul_apply]
    apply gn_sum_le_const _ _ b hb
    intro j _
    rw [gn_mul]
    exact (mul_le_of_le_one_right (gn_nonneg p _) (hs j z)).trans (hA i j)
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.row_residual_bound
