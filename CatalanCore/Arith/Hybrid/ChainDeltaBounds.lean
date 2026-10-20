module
public import CatalanCore.Arith.Hybrid.ChainResidualBounds
public import CatalanCore.Arith.Hybrid.LemmaE.ModelWeighted
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma full_D_apply (z y : Z) :
    (full Fr p r xs ys).toBlocks₂₂ z y=C (Fr.Mn (xs z) (ys y)) := by
  change rescaleHom p 2 (C (Fr.Mn (xs z) (ys y))) = _
  simp [rescaleHom]
noncomputable def delta (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
    h Fr p r xs ys ^ 2 • (full Fr p r xs ys).toBlocks₂₂-
    h Fr p r xs ys • (Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₂)-
    h Fr p r xs ys • ((full Fr p r xs ys).toBlocks₂₁*Sc Fr p r xs ys)+
    Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys
lemma delta_gle_one_at (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) {k : ℕ} (hk : (4:ZMod p)*k=(o:ZMod p))
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) (hxy : xs z%p≠ys y%p) :
    GLE p 1 (delta Fr p r xs ys z y) := by
  apply cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive hL hp hN hr))
    (Sr_int1 hL hp hN hr hx) (Sc_int1 hL hp hN hr hy) z y 1
  · rw [full_D_apply]
    exact Mn_cross_gle hL hp hN hk (hx z) (hy y) (hxy)
  · intro i hsi
    have hi : xs z%p=i.val%p := by
      by_contra hn
      exact hsi (Sr_support hL hp hN hr z i hn)
    rw [full_B_apply]
    exact Mn_cross_gle hL hp hN hk (i.isLt.trans_le hr) (hy y) (by simpa [← hi] using hxy)
  · intro i hsi
    have hi : i.val%p=ys y%p := by
      by_contra hn
      exact hsi (Sc_support hL hp hN hr i y hn)
    rw [full_C_apply]
    exact Mn_cross_gle hL hp hN hk (hx z) (i.isLt.trans_le hr) (by simpa [hi] using hxy)
  · intro i j hsi hsj
    have hi : xs z%p=i.val%p := by
      by_contra hn
      exact hsi (Sr_support hL hp hN hr z i hn)
    have hj : j.val%p=ys y%p := by
      by_contra hn
      exact hsj (Sc_support hL hp hN hr j y hn)
    have hij : i.val%p≠j.val%p := by simpa [← hi,hj] using hxy
    rw [full_A_apply_ne i j (by intro he; subst j; exact hij rfl)]
    exact Mn_cross_gle hL hp hN hk (i.isLt.trans_le hr) (j.isLt.trans_le hr) hij
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_gle_one_at
