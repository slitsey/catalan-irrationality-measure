module
public import CatalanCore.Li2.DecayCert.Compile.DiscValue
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
noncomputable section

theorem segDiscCompile_model (d : QSegment) (p e : CQ) (rt : ℚ) (w : SegDiscWitness)
    (m : CompiledModel)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (hc : segDiscCompile d p e rt w=some m) :
    Models (CellExpr.segment d p e).value (m.coeff.map ScalarExpr.value) rt m.error.value := by
  have hg : segDiscOK d p e rt w=true := by
    by_contra hn
    simp [segDiscCompile,hn] at hc
  let ζ := cqScale (1/2) (cqAdd w.phi (cqInv w.phi))
  let γ := cqDiv e d.half
  let center := cqAdd d.mid (cqMul d.half ζ)
  let shift := cqDiv (cqSub p center) e
  let δ := cqL1 shift
  have hbcheck := of_decide_eq_true hg
  rcases hbcheck with ⟨hhalf,he,hφ,hd,hdsq,hg0,hgsq,hz0,hzsq,hR,hf0,hf1,hgR,hrt,hdr,hH1,hZH,hHsq⟩
  have hζ : cqReal ζ=jJ (cqReal w.phi) := by
    dsimp only [ζ]
    rw [cqReal_scale,cqReal_add,cqReal_inv]
    unfold jJ
    push_cast
    ring
  have hγ : cqReal γ=cqReal e/cqReal d.half := cqReal_div e d.half
  have hφr : 1 < ‖cqReal w.phi‖ := by
    have hs : (1:ℝ) < ‖cqReal w.phi‖^2 := by rw [← cqSq_eq_norm_sq]; exact_mod_cast hφ
    nlinarith [norm_nonneg (cqReal w.phi)]
  have hRr : 0 < (w.radius:ℝ) := by exact_mod_cast hR
  have hδ : 0 ≤ δ := by dsimp only [δ,cqL1]; positivity
  have hδr : 0 ≤ (δ:ℝ) := by exact_mod_cast hδ
  have hrtr : 0 ≤ (rt:ℝ) := by exact_mod_cast hrt
  have hdrR : (rt:ℝ)+(δ:ℝ)<(w.radius:ℝ) := by exact_mod_cast hdr
  rcases segDiscOK_hasPrimitive d p e rt w hg with ⟨hh,G,b,hG,hGa,hb,hM⟩
  change IsDiscSegmentPrimitive (d.toSegment hh) (cqReal ζ) (cqReal γ) w.radius G at hG
  have hG' : IsDiscSegmentPrimitive (d.toSegment hh) (jJ (cqReal w.phi))
      (cqReal e/cqReal d.half) w.radius G := by simpa only [hζ,hγ] using hG
  rcases inverse_jq_hasTaylor_exists (jJ (cqReal w.phi)) (cqReal e/cqReal d.half)
    (one_lt_jc_jJ hφr) with ⟨y,hy⟩
  have hcoeff (n : ℕ) : cqReal (segCoeff d w.phi e (n+1))=b (n+1) :=
    segCoeff_value d hh w.phi e hφr w.radius hRr G hG' y b hy hb n
  let C : ℝ := (d.c 0:ℝ)*Real.log ‖cqReal d.half‖
  have hseed : (segConstant w.terms d w.phi).value=C+(b 0).re := by
    rw [segConstant_value _ _ _ (by intro hz; rw [hz,norm_zero] at hφr; norm_num at hφr)]
    rw [hb.zero,discPrimitive_seed (d.toSegment hh) (cqReal ζ) (cqReal γ) _ hRr G hG,hζ]
    simp only [Gfun,QSegment.toSegment,jphi_jJ hφr]
    rfl
  have hshape : m.coeff=(List.range (w.order+1)).map (fun j =>
      if j=0 then segConstant w.terms d w.phi else seRat (segCoeff d w.phi e j).1) ∧
    m.error=seAdd (seScale (((rt+δ)/w.radius)^(w.order+1)/(1-(rt+δ)/w.radius))
      (segDiscMajorantExpr d w)) (seRat (δ*((List.range w.order).map (fun k : ℕ =>
        (k+1:ℚ)*cqL1 (segCoeff d w.phi e (k+1))*(rt+δ)^k)).sum)) := by
    simp only [segDiscCompile,hg,ite_true] at hc
    cases Option.some.inj hc
    exact ⟨rfl,rfl⟩
  have hmc : m.coeff.map ScalarExpr.value=(List.range (w.order+1)).map
      (fun j => if j=0 then C+(b j).re else (b j).re) := by
    rw [hshape.1,List.map_map]
    apply List.map_congr_left
    intro j hj
    dsimp only [Function.comp_apply]
    by_cases hz : j=0
    · subst j; simp only [ite_true,hseed]
    · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      simp only [Nat.succ_ne_zero,ite_false,seRat_value]
      rw [← cqReal_re,hcoeff]
  have hme : m.error.value=
      (segDiscMajorantExpr d w).value*(((rt:ℝ)+(δ:ℝ))/(w.radius:ℝ))^(w.order+1)/
        (1-((rt:ℝ)+(δ:ℝ))/(w.radius:ℝ))+
      (δ:ℝ)*(∑ k ∈ Finset.range w.order,(k+1:ℕ)*(cqL1 (segCoeff d w.phi e (k+1)):ℝ)*((rt:ℝ)+(δ:ℝ))^k) := by
    rw [hshape.2,seAdd_value,seScale_value,seRat_value,list_sum_map_range]
    push_cast
    ring
  have hmodel := disc_taylor_models G b C (cqReal shift) w.radius rt δ
    (segDiscMajorantExpr d w).value hRr hrtr hδr hdrR (norm_cqReal_le_cqL1 shift) hGa hb hM w.order
  have herr : (segDiscMajorantExpr d w).value*(((rt:ℝ)+(δ:ℝ))/(w.radius:ℝ))^(w.order+1)/
      (1-((rt:ℝ)+(δ:ℝ))/(w.radius:ℝ))+
      (δ:ℝ)*(∑ k ∈ Finset.range w.order,(k+1:ℕ)*‖b (k+1)‖*((rt:ℝ)+(δ:ℝ))^k) ≤ m.error.value := by
    rw [hme]
    apply add_le_add (le_refl _)
    apply mul_le_mul_of_nonneg_left _ hδr
    apply Finset.sum_le_sum
    intro k hk
    rw [← hcoeff]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_cqReal_le_cqL1 _) (by positivity))
      (pow_nonneg (add_nonneg hrtr hδr) _)
  have hpoint (t : ℝ) : cqReal d.mid+cqReal d.half*(cqReal ζ+cqReal γ*((t:ℂ)+cqReal shift))=
      cqReal p+cqReal e*(t:ℂ) := by
    have he0 := cqReal_ne_of_cqSq_ne e he
    dsimp only [shift,center]
    rw [hγ,cqReal_div,cqReal_sub,cqReal_add,cqReal_mul]
    field_simp [hh,he0] <;> ring
  rw [hmc]
  refine ⟨hrtr,hmodel.2.1.trans herr,?_⟩
  intro t ht
  have hu : (t:ℂ)+cqReal shift ∈ Metric.ball (0:ℂ) (w.radius:ℝ) := by
    rw [Metric.mem_ball,dist_zero_right]
    apply lt_of_le_of_lt (norm_add_le _ _) _
    have ht' : ‖(t:ℂ)‖ ≤ (rt:ℝ) := by simpa using ht
    exact (add_le_add ht' (norm_cqReal_le_cqL1 shift)).trans_lt hdrR
  have hp := discPrimitive_potential (d.toSegment hh) hpos (cqReal ζ) (cqReal γ) w.radius G hG _ hu
  change P d.measure (cqReal d.mid+cqReal d.half*(cqReal ζ+cqReal γ*((t:ℂ)+cqReal shift)))=C+(G ((t:ℂ)+cqReal shift)).re at hp
  rw [hpoint] at hp
  change |P d.measure (cqReal p+cqReal e*(t:ℂ))-_| ≤ _
  rw [hp]
  exact (hmodel.2.2 t ht).trans herr
#print axioms segDiscCompile_model
end
end CatalanCore.Li2.DecayCert
