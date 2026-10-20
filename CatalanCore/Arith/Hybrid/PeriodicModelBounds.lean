module
public import CatalanCore.Arith.Hybrid.PeriodicChain
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
lemma Q_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q Fr p r xs ys i j) := by
  rw [Q_eq_shift]
  intro i j
  apply Int1.add
  · change Int1 p (C ((p:ℚ)^2 * Fr.Mn i.val j.val))
    rw [Int1, gn_C]
    exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp (D.square_mem hN (i.isLt.trans_le hr) (j.isLt.trans_le hr))
  · by_cases hi : i=j
    · subst j; simpa using (show Int1 p (X:ℚ[X]) from by
        unfold Int1; exact (gle_iff_gn p 0 X).mp GLE.X)
    · simp [Matrix.smul_apply, Matrix.one_apply, hi, Int1.zero]

lemma Q0_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i j,Int1 p (Q0 Fr p r xs ys i j) :=
  blockRect_int1 _ _ _ (Q_int1 D hN hr)

lemma h_primitive (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    gn p (h Fr p r xs ys)=1 := by
  unfold h Q0
  rw [Q_eq_shift]
  apply prim_blockProject_shift
  intro i j
  exact D.square_mem hN (i.isLt.trans_le hr) (j.isLt.trans_le hr)

lemma B2_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (B2 Fr p r xs ys i y) := by
  intro i y
  rw [B2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (D.square_mem hN (i.isLt.trans_le hr) (hy y))

lemma C2_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (C2 Fr p r xs ys z i) := by
  intro z i
  rw [C2_apply, Int1, gn_C]
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp
    (D.square_mem hN (hx z) (i.isLt.trans_le hr))

lemma Sr_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hx : ∀ z,xs z<N) : ∀ z i,Int1 p (Sr Fr p r xs ys z i) :=
  modelRow_int1 _ _ _ _ (Q0_int1 D hN hr) (C2_int1 D hN hr hx)

lemma Sc_int1 (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N)
    (hy : ∀ y,ys y<N) : ∀ i y,Int1 p (Sc Fr p r xs ys i y) :=
  modelCol_int1 _ _ _ _ (Q0_int1 D hN hr) (B2_int1 D hN hr hy)

lemma Q0_det_ne (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    (Q0 Fr p r xs ys).det≠0 := by
  intro he
  have H:=h_primitive (xs:=xs) (ys:=ys) D hN hr
  unfold h at H
  rw [he, gn_zero] at H
  norm_num at H

lemma Sr_support (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ z i,xs z%p≠i.val%p→Sr Fr p r xs ys z i=0 :=
  modelRow_support _ _ _ _ (Q0_det_ne D hN hr) Q0_support

lemma Sc_support (D : PoleData Fr p N) (hN : N<p*p) (hr : r≤N) :
    ∀ i y,i.val%p≠ys y%p→Sc Fr p r xs ys i y=0 :=
  modelCol_support _ _ _ _ (Q0_det_ne D hN hr) Q0_support

lemma Mn_cross_gle (D : PoleData Fr p N) {A B : ℕ} (hA : A<N) (hB : B<N)
    (hd : A%p≠B%p) : GLE p 1 (C (Fr.Mn A B)) := by
  apply GLE.C_iff.mpr
  apply Basic.mem_locRing.mpr
  apply mem_S.mp
  simpa only [pow_one] using (D.good_cross hA hB (by
    intro H
    apply hd
    exact (ZMod.natCast_eq_natCast_iff' A B p).mp (sub_eq_zero.mp H).symm)).mem
end CatalanCore.Arith.Hybrid.Periodic.Model
