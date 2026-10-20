module
public import CatalanCore.Arith.Hybrid.ChainDeltaBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
lemma gle_of_scaled_int1 (b : ℕ) (f : ℚ[X]) (hf : Int1 p (C ((p:ℚ)^b)*f)) :
    GLE p b f := by
  intro i
  have hi : (C ((p:ℚ)^b)*f).coeff i ∈ Basic.LocRing p := by
    apply (mem_locRing_iff_padicNorm (p:=p)).mpr
    exact_mod_cast (padic_coeff_le_gn p _ i).trans hf
  simpa only [coeff_C_mul] using hi
end CatalanCore.Arith.Hybrid.LemmaE
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma A_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i j,GLE p 2 ((full Fr p r xs ys).toBlocks₁₁ i j) := by
  intro i j
  apply gle_of_scaled_int1
  have H:=Q_int1 (xs:=xs) (ys:=ys) hL hp hN hr i j
  rwa [Q_eq_smul,Matrix.smul_apply,smul_eq_mul] at H
lemma B_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,GLE p 2 ((full Fr p r xs ys).toBlocks₁₂ i y) := by
  intro i y
  exact gle_of_scaled_int1 2 _ (B2_int1 hL hp hN hr hy i y)
lemma C_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,GLE p 2 ((full Fr p r xs ys).toBlocks₂₁ z i) := by
  intro z i
  exact gle_of_scaled_int1 2 _ (C2_int1 hL hp hN hr hx z i)
lemma D_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) : ∀ z y,GLE p 2 ((full Fr p r xs ys).toBlocks₂₂ z y) := by
  intro z y
  rw [full_D_apply]
  exact GLE.C_iff.mpr (Mn_square_mem hL hp hN (hx z) (hy y))
lemma delta_gle_two (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) (hy : ∀ y,ys y<N) (z y : Z) : GLE p 2 (delta Fr p r xs ys z y) :=
  cleared_delta_gle_at _ _ _ _ _ _ _ (le_of_eq (h_primitive hL hp hN hr))
    (Sr_int1 hL hp hN hr hx) (Sc_int1 hL hp hN hr hy) z y 2
    (D_gle_two hL hp hN hx hy z y)
    (fun i _=>B_gle_two hL hp hN hr hy i y)
    (fun i _=>C_gle_two hL hp hN hr hx z i)
    (fun i j _ _=>A_gle_two hL hp hN hr i j)
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_gle_two
