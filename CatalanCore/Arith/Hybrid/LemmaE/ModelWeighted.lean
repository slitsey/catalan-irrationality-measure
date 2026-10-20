module
public import CatalanCore.Arith.Hybrid.LemmaE.ModelBounds
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
lemma int1_mul_gle {b : ℕ} {f g : ℚ[X]} (hf : Int1 p f) (hg : GLE p b g) :
    GLE p b (f*g) := by
  rw [gle_iff_gn, gn_mul]
  exact (mul_le_of_le_one_left (gn_nonneg p _) hf).trans ((gle_iff_gn p b g).mp hg)
lemma gle_mul_int1 {b : ℕ} {f g : ℚ[X]} (hf : GLE p b f) (hg : Int1 p g) :
    GLE p b (f*g) := by rw [mul_comm]; exact int1_mul_gle hg hf
lemma gle_sub {b : ℕ} {f g : ℚ[X]} (hf : GLE p b f) (hg : GLE p b g) :
    GLE p b (f-g) := by simpa [sub_eq_add_neg] using hf.add (hg.zsmul (-1))
variable {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
/-- Sparse cleared partners transfer arbitrary entry bounds to their second difference. -/
lemma cleared_delta_gle_at (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X]) (Sr : Matrix Z I ℚ[X])
    (Sc : Matrix I Z ℚ[X]) (h : ℚ[X]) (hh : Int1 p h)
    (hr : ∀ z i, Int1 p (Sr z i)) (hc : ∀ i y, Int1 p (Sc i y))
    (z y : Z) (w : ℕ)
    (hD : GLE p w (D z y))
    (hB : ∀ i,Sr z i ≠ 0 → GLE p w (B i y))
    (hC : ∀ i,Sc i y ≠ 0 → GLE p w (C z i))
    (hA : ∀ i j,Sr z i ≠ 0 → Sc j y ≠ 0 → GLE p w (A i j)) :
    GLE p w ((h^2 • D-h • (Sr*B)-h • (C*Sc)+Sr*A*Sc) z y) := by
  have hsb : GLE p w ((Sr*B) z y) := by
    rw [Matrix.mul_apply]
    apply GLE.sum
    intro i _
    by_cases hi : Sr z i=0
    · simp [hi, GLE.zero]
    · exact int1_mul_gle (hr z i) (hB i hi)
  have hcs : GLE p w ((C*Sc) z y) := by
    rw [Matrix.mul_apply]
    apply GLE.sum
    intro i _
    by_cases hi : Sc i y=0
    · simp [hi, GLE.zero]
    · exact gle_mul_int1 (hC i hi) (hc i y)
  have has : GLE p w ((Sr*A*Sc) z y) := by
    rw [Matrix.mul_apply]
    apply GLE.sum
    intro j _
    rw [Matrix.mul_apply, Finset.sum_mul]
    apply GLE.sum
    intro i _
    by_cases hi : Sr z i=0
    · simp [hi, GLE.zero]
    by_cases hj : Sc j y=0
    · simp [hj, GLE.zero]
    exact gle_mul_int1 (int1_mul_gle (hr z i) (hA i j hi hj)) (hc j y)
  simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using
    ((gle_sub (gle_sub (int1_mul_gle (by simpa [pow_two] using hh.mul hh) hD)
      (int1_mul_gle hh hsb)) (int1_mul_gle hh hcs)).add has)
/-- The complete weighted determinant conclusion from cleared-partner entry estimates. -/
theorem tcore_cleared_weighted (Full : Matrix (I ⊕ Z) (I ⊕ Z) ℚ[X])
    (hI : ∀ i j,Int1 p (Atil p (fun _ : I=>1) Full.toBlocks₁₁ i j))
    (hp : gn p (Atil p (fun _ : I=>1) Full.toBlocks₁₁).det=1)
    (h : ℚ[X]) (hh : gn p h=1) (Sr : Matrix Z I ℚ[X]) (Sc : Matrix I Z ℚ[X])
    (w : Z → Z → ℕ)
    (hL : ∀ z i,gn p ((h • Full.toBlocks₂₁-Sr*Full.toBlocks₁₁) z i)≤p)
    (hR : ∀ i y,gn p ((h • Full.toBlocks₁₂-Full.toBlocks₁₁*Sc) i y)≤p)
    (hd : ∀ z y,GLE p (w z y) ((h^2 • Full.toBlocks₂₂-h • (Sr*Full.toBlocks₁₂)-
      h • (Full.toBlocks₂₁*Sc)+Sr*Full.toBlocks₁₁*Sc) z y)) :
    GLE p (tropVal w+2*Fintype.card I) Full.det := by
  simpa using tcore_scaled_weighted p Full (fun _ : I=>1) hp w
    (tcore_vec_T_cleared Full hI hp h hh Sr Sc w hL hR hd)
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.cleared_delta_gle_at
#print axioms CatalanCore.Arith.Hybrid.LemmaE.tcore_cleared_weighted
