module

public import CatalanCore.Arith.Hybrid.NegFrame
public import CatalanCore.Rect.PairBridge

@[expose] public section

/-!
# Sign transfer for the geometries of the rectangular hybrid and `Mem2Content`
-/

open Polynomial Finset CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr₁ Fr₂ : Frame}

lemma fullPolyG_neg (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) (G : Geometry) :
    G.fullPolyG Fr₂ = C ((-1 : ℚ) ^ (Fintype.card (G.C ⊕ Fin G.k))) *
      (G.fullPolyG Fr₁).comp (-(Polynomial.X : ℚ[X])) := by
  unfold Geometry.fullPolyG Geometry.Full
  set M₁ := FullN Fr₁ (fun a : G.C => (a : ℕ)) G.xs G.ys (Polynomial.X : ℚ[X]) with hM₁
  set M₂ := FullN Fr₂ (fun a : G.C => (a : ℕ)) G.xs G.ys (Polynomial.X : ℚ[X]) with hM₂
  have h1 : M₂ = -(M₁.map (fun f => f.comp (-(Polynomial.X : ℚ[X])))) := by
    refine Matrix.ext fun a b => ?_
    rcases a with c | c <;> rcases b with c' | c' <;>
    simp [hM₁, hM₂, FullN, Blk, blkA, blkB, blkC, blkD, hM, Matrix.fromBlocks, Matrix.one_apply,
      Polynomial.add_comp] <;> split_ifs <;> simp
  have h2 : (M₁.map (fun f => f.comp (-(Polynomial.X : ℚ[X])))).det =
      M₁.det.comp (-(Polynomial.X : ℚ[X])) := by
    have := RingHom.map_det (Polynomial.compRingHom (-(Polynomial.X : ℚ[X]))) M₁
    simpa using this.symm
  rw [h1, Matrix.det_neg, h2]
  simp [C_pow]

theorem Mem2Content.of_neg (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) {Λ : ℝ}
    (h : Mem2Content Fr₁ Λ) : Mem2Content Fr₂ Λ := by
  obtain ⟨D2, hpos, hint, hlog⟩ := h
  refine ⟨D2, hpos, ?_, hlog⟩
  intro r h8 i
  obtain ⟨z, hz⟩ := hint r h8 i
  rw [fullPolyG_neg hM, coeff_C_mul, coeff_comp_neg_X']
  refine ⟨((-1 : ℤ) ^ (Fintype.card ((afterTop r (r / 8)).C ⊕ Fin (afterTop r (r / 8)).k)) *
    (-1) ^ i) * z, ?_⟩
  have : (D2 r : ℚ) * ((-1) ^ Fintype.card ((afterTop r (r / 8)).C ⊕ Fin (afterTop r (r / 8)).k) *
      ((-1) ^ i * ((afterTop r (r / 8)).fullPolyG Fr₁).coeff i)) =
      ((-1) ^ Fintype.card ((afterTop r (r / 8)).C ⊕ Fin (afterTop r (r / 8)).k) * (-1) ^ i) *
        ((D2 r : ℚ) * ((afterTop r (r / 8)).fullPolyG Fr₁).coeff i) := by ring
  rw [this, hz]
  push_cast
  ring

end CatalanFrames.HybCommon
