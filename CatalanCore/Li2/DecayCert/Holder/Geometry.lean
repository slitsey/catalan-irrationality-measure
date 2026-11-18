module
public import CatalanCore.Li2.DecayCert.Holder.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

theorem slitDistSq_le_norm_sub (ζ : CQ) (x : ℝ) (hx : x ∈ Icc (-1:ℝ) 1) :
    (slitDistSq ζ:ℝ) ≤ ‖cqReal ζ-(x:ℂ)‖^2 := by
  have hn : ‖cqReal ζ-(x:ℂ)‖^2=((ζ.1:ℝ)-x)^2+(ζ.2:ℝ)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply,cqReal_mk]
    simp <;> ring
  rw [hn]
  by_cases hl : ζ.1 < -1
  · simp only [slitDistSq,if_pos hl,Rat.cast_add,Rat.cast_pow,Rat.cast_one]
    have hlR : (ζ.1:ℝ)< -1 := by exact_mod_cast hl
    nlinarith [mul_nonneg (by linarith [hx.1] : 0 ≤ x+1) (by linarith [hx.1] : 0 ≤ x-2*(ζ.1:ℝ)-1)]
  · by_cases hr : 1 < ζ.1
    · simp only [slitDistSq,if_neg hl,if_pos hr,Rat.cast_add,Rat.cast_sub,Rat.cast_pow,Rat.cast_one]
      have hrR : 1 < (ζ.1:ℝ) := by exact_mod_cast hr
      nlinarith [mul_nonneg (by linarith [hx.2] : 0 ≤ 1-x) (by linarith [hx.2] : 0 ≤ 2*(ζ.1:ℝ)-x-1)]
    · simp only [slitDistSq,if_neg hl,if_neg hr,Rat.cast_pow]
      nlinarith [sq_nonneg ((ζ.1:ℝ)-x)]

theorem cq_affine_off_of_slitSq (ζ γ : CQ) (R L : ℚ) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (hγ : ‖cqReal γ‖*(R:ℝ) ≤ (L:ℝ)) (hsq : L^2 < slitDistSq ζ) :
    ∀ t ∈ Icc 0 (R:ℝ),1 < jc (cqReal ζ+cqReal γ*(t:ℂ)) := by
  intro t ht
  apply one_lt_jc_of_not_mem_sourceSlit
  rintro ⟨x,hx,he⟩
  have hn : ‖cqReal ζ-(x:ℂ)‖ ≤ (L:ℝ) := by
    rw [he,show cqReal ζ-(cqReal ζ+cqReal γ*(t:ℂ))= -(cqReal γ*(t:ℂ)) by ring,norm_neg,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)).trans hγ
  have hg := slitDistSq_le_norm_sub ζ x hx
  have hs : (L:ℝ)^2 < (slitDistSq ζ:ℝ) := by exact_mod_cast hsq
  have hLr : 0 ≤ (L:ℝ) := by exact_mod_cast hL
  nlinarith [norm_nonneg (cqReal ζ-(x:ℂ))]

theorem cq_affine_branch_off (ζ γ : CQ) (hζ : ζ=(1,0) ∨ ζ=(-1,0))
    (hg : γ.2 ≠ 0 ∨ (ζ=(1,0) ∧ 0 < γ.1) ∨ (ζ=(-1,0) ∧ γ.1 < 0)) :
    ∀ t : ℝ,0 < t → 1 < jc (cqReal ζ+cqReal γ*(t:ℂ)) := by
  intro t ht
  apply one_lt_jc_of_not_mem_sourceSlit
  rintro ⟨x,hx,he⟩
  rcases hg with hi | ⟨rfl,hr⟩ | ⟨rfl,hr⟩
  · have him : (cqReal ζ+cqReal γ*(t:ℂ)).im=(γ.2:ℝ)*t := by
      rcases hζ with rfl | rfl <;> simp [cqReal]
    have hh := congrArg Complex.im he
    rw [him] at hh
    have hiR : (γ.2:ℝ) ≠ 0 := by exact_mod_cast hi
    exact (mul_ne_zero hiR ht.ne') (by simpa using hh.symm)
  · have hh := congrArg Complex.re he
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,cqReal_re] at hh
    norm_num at hh
    have hrR : 0 < (γ.1:ℝ) := by exact_mod_cast hr
    nlinarith [mul_pos hrR ht,hx.2]
  · have hh := congrArg Complex.re he
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,cqReal_re] at hh
    norm_num at hh
    have hrR : (γ.1:ℝ) < 0 := by exact_mod_cast hr
    nlinarith [mul_neg_of_neg_of_pos hrR ht,hx.1]

theorem pure_affine_own_geometry (d : QSegment) (hh : cqReal d.half ≠ 0) (p e : CQ) (R : ℚ)
    (hR : 0 ≤ R)
    (hx : (cqDiv (cqSub p d.mid) d.half).2=0) (he : (cqDiv e d.half).2=0)
    (hb : intervalInside (-1) 1 (cqDiv (cqSub p d.mid) d.half).1
      ((cqDiv (cqSub p d.mid) d.half).1+(cqDiv e d.half).1*R)=true) :
    EndCellGeometry (d.toSegment hh) (cqReal p) (cqReal e) R .own := by
  let x := cqDiv (cqSub p d.mid) d.half
  let γ := cqDiv e d.half
  have hxb : -1 ≤ x.1 ∧ x.1 ≤ 1 ∧ -1 ≤ x.1+γ.1*R ∧ x.1+γ.1*R ≤ 1 := of_decide_eq_true hb
  have hx' : x.2=0 := hx
  have he' : γ.2=0 := he
  have hxb0 : (-1:ℚ) ≤ x.1 ∧ x.1 ≤ 1 := ⟨hxb.1,hxb.2.1⟩
  have hxbR : (-1:ℚ) ≤ x.1+γ.1*R ∧ x.1+γ.1*R ≤ 1 := ⟨hxb.2.2.1,hxb.2.2.2⟩
  intro t ht
  refine ⟨(x.1:ℝ)+(γ.1:ℝ)*t,?_,?_⟩
  · apply affine_interval_unit (x.1:ℝ) (γ.1:ℝ) 0 R
    · simpa using (show (-1:ℝ) ≤ (x.1:ℝ) ∧ (x.1:ℝ) ≤ 1 by exact_mod_cast hxb0)
    · exact_mod_cast hxbR
    · exact ht
  · change cqReal p+cqReal e*(t:ℂ)=cqReal d.mid+cqReal d.half*(((x.1:ℝ)+(γ.1:ℝ)*t:ℝ):ℂ)
    have hxR : cqReal x=((x.1:ℝ):ℂ) := by simp [cqReal,hx']
    have hγR : cqReal γ=((γ.1:ℝ):ℂ) := by simp [cqReal,he']
    simp only [Complex.ofReal_add,Complex.ofReal_mul]
    rw [← hxR,← hγR]
    dsimp only [x,γ]
    rw [cqReal_div,cqReal_sub,cqReal_div]
    field_simp [hh] <;> ring
#print axioms slitDistSq_le_norm_sub
#print axioms cq_affine_off_of_slitSq
#print axioms cq_affine_branch_off
#print axioms pure_affine_own_geometry
end
end CatalanCore.Li2.DecayCert
