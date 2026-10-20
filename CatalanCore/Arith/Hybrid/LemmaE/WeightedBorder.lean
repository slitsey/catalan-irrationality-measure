module
public import CatalanCore.Arith.Hybrid.LemmaE.WeightedCore
public import CatalanCore.Arith.Hybrid.LemmaE.SchurBorder
public import CatalanCore.Arith.Hybrid.DefGKBorderCore
@[expose] public section
open Matrix Polynomial Finset
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
variable {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
theorem tcore_border_weighted_incidence (F : Matrix (I⊕Option Z) (I⊕Option Z) ℚ[X])
    (F0 : Matrix (I⊕Z) (I⊕Z) ℚ[X])
    (hold : ∀a b,F (Sum.map id some a) (Sum.map id some b)=F0 a b)
    (hI : ∀i j,Int1 p (Atil p (fun _:I=>1) F0.toBlocks₁₁ i j))
    (hp : gn p (Atil p (fun _:I=>1) F0.toBlocks₁₁).det=1)
    (W : Z→Z→ℕ)
    (hT : ∀z y,GLE p (W z y) (Tscaled (Atil p (fun _:I=>1) F0.toBlocks₁₁).det
      F0.toBlocks₁₁ F0.toBlocks₁₂ F0.toBlocks₂₁ F0.toBlocks₂₂
      (Nmat p (fun _:I=>1) F0.toBlocks₁₁) z y)) (w : ℕ)
    (hC : ∀z i,Int1 p (C ((p:ℚ)^2)*F.toBlocks₂₁ (some z) i))
    (hB : ∀i y,Int1 p (C ((p:ℚ)^2)*F.toBlocks₁₂ i (some y)))
    (hCr : ∀i,GLE p w (F.toBlocks₂₁ none i))
    (hBc : ∀i,GLE p w (F.toBlocks₁₂ i none))
    (hDr : ∀y,GLE p w (F.toBlocks₂₂ none (some y)))
    (hDc : ∀z,GLE p w (F.toBlocks₂₂ (some z) none))
    (hD : GLE p (w+w) (F.toBlocks₂₂ none none)) :
    GLE p (tropVal W+(w+w)+2*Fintype.card I) F.det := by
  have hA : F.toBlocks₁₁=F0.toBlocks₁₁ := by
    apply Matrix.ext; intro i j; exact hold (Sum.inl i) (Sum.inl j)
  have hb (i : I) (y : Z) : F.toBlocks₁₂ i (some y)=F0.toBlocks₁₂ i y := hold (Sum.inl i) (Sum.inr y)
  have hc (z : Z) (i : I) : F.toBlocks₂₁ (some z) i=F0.toBlocks₂₁ z i := hold (Sum.inr z) (Sum.inl i)
  have hd (z y : Z) : F.toBlocks₂₂ (some z) (some y)=F0.toBlocks₂₂ z y := hold (Sum.inr z) (Sum.inr y)
  have hIF : ∀i j,Int1 p (Atil p (fun _:I=>1) F.toBlocks₁₁ i j) := by simpa only [hA] using hI
  have hPF : gn p (Atil p (fun _:I=>1) F.toBlocks₁₁).det=1 := by simpa only [hA] using hp
  apply tcore_weighted_border p F _ hp _
    (by rw [hA];exact AN_eq p (fun _:I=>1) _)
    (2*Fintype.card I)
    (by rw [hA];simpa using (det_Atil p (fun _:I=>1) F0.toBlocks₁₁).symm) W w
  · intro z y
    simp only [Tscaled_apply,hA,hb,hc,hd]
    simpa only [Tscaled_apply] using hT z y
  · intro z
    simpa only [hA] using Tscaled_gle_right_at w _ _ _ _ hIF hPF (some z) none (hC z) hBc (hDc z)
  · intro y
    simpa only [hA] using Tscaled_gle_left_at w _ _ _ _ hIF hPF none (some y) hCr (fun i=>hB i y) (hDr y)
  · simpa only [hA] using Tscaled_gle_product_at w w _ _ _ _ hIF hPF none none hCr hBc hD
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.tcore_border_weighted_incidence
