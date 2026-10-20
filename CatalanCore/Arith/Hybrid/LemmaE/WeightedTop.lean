module
public import CatalanCore.Arith.Hybrid.LemmaE.WeightedBorder
@[expose] public section
open Matrix Polynomial Finset
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
variable {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]
/-- A new Schur row and column preserve every old entry weight at cost four. -/
theorem tcore_border_weighted (F : Matrix (I⊕Option Z) (I⊕Option Z) ℚ[X])
    (F0 : Matrix (I⊕Z) (I⊕Z) ℚ[X])
    (hold : ∀a b,F (Sum.map id some a) (Sum.map id some b)=F0 a b)
    (hI : ∀i j,Int1 p (Atil p (fun _:I=>1) F0.toBlocks₁₁ i j))
    (hp : gn p (Atil p (fun _:I=>1) F0.toBlocks₁₁).det=1)
    (W : Z→Z→ℕ)
    (hT : ∀z y,GLE p (W z y) (Tscaled (Atil p (fun _:I=>1) F0.toBlocks₁₁).det
      F0.toBlocks₁₁ F0.toBlocks₁₂ F0.toBlocks₂₁ F0.toBlocks₂₂
      (Nmat p (fun _:I=>1) F0.toBlocks₁₁) z y))
    (hC : ∀z i,Int1 p (C ((p:ℚ)^2)*F.toBlocks₂₁ z i))
    (hB : ∀i y,GLE p 2 (F.toBlocks₁₂ i y))
    (hD : ∀z y,GLE p 2 (F.toBlocks₂₂ z y)) :
    GLE p (tropVal W+4+2*Fintype.card I) F.det := by
  simpa using tcore_border_weighted_incidence F F0 hold hI hp W hT 2
    (fun z i=>hC (some z) i)
    (fun i y=>(int1_Cpow_iff 2 _).mpr (hB i (some y)))
    (fun i=>(int1_Cpow_iff 2 _).mp (hC none i))
    (fun i=>hB i none) (fun y=>hD none (some y)) (fun z=>hD (some z) none)
    ((hD none none).mono (by omega))
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.tcore_border_weighted
