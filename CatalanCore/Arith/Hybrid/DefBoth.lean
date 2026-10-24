module
public import CatalanCore.Arith.Hybrid.BorderDef
public import CatalanCore.Arith.Hybrid.DefSum
@[expose] public section
open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect
namespace CatalanCore.Arith.Hybrid
variable {Fr : Frame}
/-- Member-1 and member-2 deficit hypotheses together. -/
def DefBoth (I : HybInst Fr) (r m : ℕ) (T δ : ℕ → ℕ) : Prop :=
  DefHypT I r m T δ ∧ DefHypTop I r m T δ

lemma DefBoth.mono_T {I : HybInst Fr} {r m : ℕ} {T T' δ : ℕ → ℕ} (h : DefBoth I r m T δ)
    (hle : ∀ p, p.Prime → p < Bnd I r m → T p ≤ T' p) : DefBoth I r m T' δ :=
  ⟨h.1.mono_T hle, h.2.mono_T hle⟩

lemma DefBoth.add {I : HybInst Fr} {r m : ℕ} {T δ₁ δ₂ : ℕ → ℕ} (h1 : DefBoth I r m T δ₁)
    (h2 : DefBoth I r m T δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd I r m → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefBoth I r m T (fun p => δ₁ p + δ₂ p) := by
  refine ⟨?_, h1.2.add h2.2 hdisj⟩
  intro p hp hb
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2.1 p hp hb
  · simp only [h, add_zero]; exact h1.1 p hp hb

/-- **A `DefBoth` family from rank witnesses.** -/
theorem defBoth_of_wit (I : HybInst Fr) (r m : ℕ) [I.DiagOK r m] (T δ : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p) (W : ℕ → Prop)
    (hδ : ∀ p, ¬ W p → δ p = 0)
    (hW : ∀ p : ℕ, p.Prime → W p → ∀ [Fact p.Prime], ∃ u v : Fin r ⊕ Fin m → ℕ,
      HasRankWit Fr p r m u v (δ p) ∧ ∑ a, u a + ∑ b, v b ≤ T p)
    (hδT : ∀ p, p.Prime → p < Bnd I r m → W p → δ p ≤ T p) : DefBoth I r m T δ := by
  refine ⟨?_, defHypTop_of_wit I r m T δ hT W hδ hW⟩
  refine defHypT_of_local I r m T δ hT W hδ ?_
  intro p hp hb hWp
  refine ⟨hδT p hp hb hWp, fun [Fact p.Prime] => ?_⟩
  obtain ⟨u, v, hw, hle⟩ := hW p hp hWp
  exact hw.gle.mono (by omega)

#print axioms defBoth_of_wit
end CatalanCore.Arith.Hybrid
