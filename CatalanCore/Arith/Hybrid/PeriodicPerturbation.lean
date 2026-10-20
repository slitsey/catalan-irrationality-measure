module
public import CatalanCore.Arith.Hybrid.PeriodicWeighted
public import CatalanCore.Arith.Hybrid.LemmaE.IntegralCorePerturbation
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

/-- The denominator budget survives every integral constant change to the core.
This is the stability input for recovering all principal minors by differences. -/
theorem perturbed_full_det_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (w : Z→Z→ℕ) (hw : ∀z y,w z y≤2)
    (hzero : ∀z y,w z y=0→NoCut (Cut p r D.singular)
      (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hone : ∀z y,w z y=1→xs z%p≠ys y%p)
    (E : Matrix (Fin r) (Fin r) ℚ) (he : ∀i j,E i j∈S p) :
    GLE p (tropVal w+2*r)
      (Matrix.fromBlocks ((full Fr p r xs ys).toBlocks₁₁+E.map C)
        (full Fr p r xs ys).toBlocks₁₂ (full Fr p r xs ys).toBlocks₂₁
        (full Fr p r xs ys).toBlocks₂₂).det := by
  let M : Matrix (Fin r) (Fin r) ℚ := fun i j=>(p:ℚ)^2*(Fr.Mn i.val j.val+E i j)
  have hm : ∀i j,M i j∈Basic.LocRing p := by
    intro i j
    apply Basic.mem_locRing.mpr
    apply mem_S.mp
    dsimp [M]
    rw [mul_add]
    exact (S p).add_mem (D.square_mem hN (i.isLt.trans_le hr) (j.isLt.trans_le hr))
      ((S p).mul_mem ((S p).pow_mem (Good.natCast (ℓ:=p) p).mem 2) (he i j))
  have hshift : Atil p (fun _:Fin r=>1)
      ((full Fr p r xs ys).toBlocks₁₁+E.map C)=M.map C+(X:ℚ[X]) • 1 := by
    apply Matrix.ext
    intro i j
    have hq:=Q_apply (Fr:=Fr) (p:=p) (xs:=xs) (ys:=ys) i j
    simp only [Atil_apply, pow_one, Matrix.add_apply, Matrix.map_apply]
    change C (p:ℚ)*(((full Fr p r xs ys).toBlocks₁₁ i j)+C (E i j))*C (p:ℚ)=_
    have hq' : C (p:ℚ)*(full Fr p r xs ys).toBlocks₁₁ i j*C (p:ℚ)=
        C ((p:ℚ)^2*Fr.Mn i.val j.val)+X*(if i=j then 1 else 0) := by simpa only [Q, Atil_apply, pow_one] using hq
    simp only [Matrix.add_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,M]
    rw [mul_add,add_mul,hq',mul_assoc,←map_mul,←map_mul]
    ring_nf
    rw [map_add]
    ring
  have hI : ∀i j,Int1 p (Atil p (fun _:Fin r=>1)
      ((full Fr p r xs ys).toBlocks₁₁+E.map C) i j) := by
    rw [hshift]
    intro i j
    apply Int1.add
    · change Int1 p (C (M i j))
      rw [Int1,gn_C]
      exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp (hm i j)
    · by_cases hij : i=j
      · subst j;simpa [Int1, Matrix.smul_apply] using (gle_iff_gn p 0 X).mp (GLE.X (p:=p))
      · simp [Matrix.smul_apply,Matrix.one_apply,hij,Int1.zero]
  simpa only [Fintype.card_fin] using integral_core_add_weighted
    (full Fr p r xs ys).toBlocks₁₁ (E.map C) (full Fr p r xs ys).toBlocks₁₂
    (full Fr p r xs ys).toBlocks₂₁ (full Fr p r xs ys).toBlocks₂₂
    (h Fr p r xs ys) (Sr Fr p r xs ys) (Sc Fr p r xs ys)
    (h_primitive D hN hr) (Sr_int1 D hN hr hx) (Sc_int1 D hN hr hy)
    (fun i j=>by
      change Int1 p (C (E i j));rw [Int1,gn_C]
      exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp (he i j)) w
    (Sr_residual_bound D hN hr hx) (Sc_residual_bound D hN hr hy)
    (delta_gle_weighted D hN hr hx hy hxlo hylo hne w hw hzero hone) hI
    (by rw [hshift];exact prim_det_shift M hm)
end CatalanCore.Arith.Hybrid.Periodic.Model
