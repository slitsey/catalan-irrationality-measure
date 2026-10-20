module
public import CatalanCore.Arith.Hybrid.ChainModelBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z → ℕ}
lemma B2_apply (i : Fin r) (y : Z) :
    B2 Fr p r xs ys i y=C ((p:ℚ)^2 * Fr.Mn i.val (ys y)) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn i.val (ys y))) = _
  simp [rescaleHom]
lemma C2_apply (z : Z) (i : Fin r) :
    C2 Fr p r xs ys z i=C ((p:ℚ)^2 * Fr.Mn (xs z) i.val) := by
  change C ((p:ℚ)^2) * rescaleHom p 2 (C (Fr.Mn (xs z) i.val)) = _
  simp [rescaleHom]
lemma B2_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (B2 Fr p r xs ys i y) := by
  intro i y
  rw [B2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (Mn_square_mem hL hp hN (i.isLt.trans_le hr) (hy y))
lemma C2_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (C2 Fr p r xs ys z i) := by
  intro z i
  rw [C2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (Mn_square_mem hL hp hN (hx z) (i.isLt.trans_le hr))
lemma Sr_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (Sr Fr p r xs ys z i) :=
  modelRow_int1 _ _ _ _ (Q0_int1 hL hp hN hr) (C2_int1 hL hp hN hr hx)
lemma Sc_int1 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (Sc Fr p r xs ys i y) :=
  modelCol_int1 _ _ _ _ (Q0_int1 hL hp hN hr) (B2_int1 hL hp hN hr hy)
lemma Q0_support (i j : Fin r) (hij : i.val%p≠j.val%p) : Q0 Fr p r xs ys i j=0 :=
  by simp [Q0, blockProject, blockRect, hij]
lemma Q0_det_ne (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    (Q0 Fr p r xs ys).det≠0 := by
  intro he
  have H:=h_primitive (xs:=xs) (ys:=ys) hL hp hN hr
  unfold h at H
  rw [he, gn_zero] at H
  norm_num at H
lemma Sr_support (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ z i,xs z%p≠i.val%p→Sr Fr p r xs ys z i=0 :=
  modelRow_support _ _ _ _ (Q0_det_ne hL hp hN hr) Q0_support
lemma Sc_support (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) :
    ∀ i y,i.val%p≠ys y%p→Sc Fr p r xs ys i y=0 :=
  modelCol_support _ _ _ _ (Q0_det_ne hL hp hN hr) Q0_support
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.Sr_support
