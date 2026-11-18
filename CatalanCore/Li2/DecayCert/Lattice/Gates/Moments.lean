module
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes.Source
public import CatalanCore.Li2.DecayCert.Lattice.FarMacro
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Polynomial
open scoped BigOperators
open CatalanCore.Zeta5.Potential CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert.LatticeGate

/-- Exact ordinary source moment; no supplied moment table is assumed. -/
theorem segment_complex_moment (d : QSegment) (y0 : ℚ) (k : ℕ)
    (hlen : 0<d.coeff.length) (hmid : d.mid.2=0) (hhalf : d.half.2=0)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,
      0≤chebF (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x) :
    moment d.measure (y0:ℂ) k=
      (arcPolyMoment (d.density*(C (d.mid.1-y0)+C d.half.1*X)^k):ℂ) := by
  let p := d.density*(C (d.mid.1-y0)+C d.half.1*X)^k
  have hg : Measurable (fun s : ℂ => (s-(y0:ℂ))^k) := by fun_prop
  unfold moment
  change (∫ s,(s-(y0:ℂ))^k ∂(segMeasure (cqReal d.mid) (cqReal d.half)
    (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1)))=_
  rw [integral_segMeasure_C hpos hg]
  have he (θ : ℝ) :
      (chebF (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) (Real.cos θ):ℂ)*
        (cqReal d.mid+cqReal d.half*(Real.cos θ:ℂ)-(y0:ℂ))^k=
      (((p.map (Rat.castHom ℝ)).eval (Real.cos θ):ℝ):ℂ) := by
    rw [← density_real_eval d hlen]
    have hm : cqReal d.mid=((d.mid.1:ℝ):ℂ) := by simp [cqReal,hmid]
    have hh : cqReal d.half=((d.half.1:ℝ):ℂ) := by simp [cqReal,hhalf]
    rw [hm,hh]
    dsimp only [p]
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_C,
      Polynomial.map_X,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_C,Polynomial.eval_X,Rat.coe_castHom]
    push_cast
    ring
  simp_rw [he]
  rw [integral_complex_ofReal,arcPolyMoment_integral]
  norm_cast

theorem segment_real_moment (d : QSegment) (y0 : ℚ) (k : ℕ)
    (hlen : 0<d.coeff.length) (hmid : d.mid.2=0) (hhalf : d.half.2=0)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,
      0≤chebF (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x) :
    (moment d.measure (y0:ℂ) k).re=
      (arcPolyMoment (d.density*(C (d.mid.1-y0)+C d.half.1*X)^k):ℝ) := by
  rw [segment_complex_moment d y0 k hlen hmid hhalf hpos]
  simp

#print axioms segment_complex_moment
#print axioms segment_real_moment
theorem segment_real_support (d : QSegment) (L Y : ℚ)
    (hmid : d.mid.2=0) (hhalf : d.half.2=0)
    (hlo : L≤d.mid.1-d.half.1 ∧ L≤d.mid.1+d.half.1)
    (hhi : d.mid.1-d.half.1≤Y ∧ d.mid.1+d.half.1≤Y) :
    d.measure {s | s.im≠0 ∨ s.re<(L:ℝ) ∨ (Y:ℝ)<s.re}=0 := by
  rw [← sourceParameter_map d,Measure.map_apply (by fun_prop) (by measurability)]
  apply measure_mono_null _ (sourceParameter_supported d)
  intro x hx
  intro hxin
  change (cqReal d.mid+cqReal d.half*(x:ℂ)).im≠0 ∨
    (cqReal d.mid+cqReal d.half*(x:ℂ)).re<(L:ℝ) ∨
    (Y:ℝ)<(cqReal d.mid+cqReal d.half*(x:ℂ)).re at hx
  have him : (cqReal d.mid+cqReal d.half*(x:ℂ)).im=0 := by simp [cqReal,hmid,hhalf]
  rcases hx with hx | hx
  · exact hx him
  · have hre : (cqReal d.mid+cqReal d.half*(x:ℂ)).re=(d.mid.1:ℝ)+(d.half.1:ℝ)*x := by
      simp [cqReal,hmid,hhalf]
    rw [hre] at hx
    have hL : (L:ℝ)≤(d.mid.1:ℝ)-(d.half.1:ℝ) ∧ (L:ℝ)≤(d.mid.1:ℝ)+(d.half.1:ℝ) := by
      exact_mod_cast hlo
    have hY : (d.mid.1:ℝ)-(d.half.1:ℝ)≤(Y:ℝ) ∧ (d.mid.1:ℝ)+(d.half.1:ℝ)≤(Y:ℝ) := by
      exact_mod_cast hhi
    have hxl : -1≤x := hxin.1
    have hxu : x≤1 := hxin.2
    by_cases hh : (0:ℝ)≤(d.half.1:ℝ)
    · have h1 := mul_le_mul_of_nonneg_left hxl hh
      have h2 := mul_le_mul_of_nonneg_left hxu hh
      rcases hx with hx | hx
      · linarith
      · linarith
    · have h1 := mul_le_mul_of_nonpos_left hxl (le_of_not_ge hh)
      have h2 := mul_le_mul_of_nonpos_left hxu (le_of_not_ge hh)
      rcases hx with hx | hx
      · linarith
      · linarith

#print axioms segment_real_support

def realSupportCheck (d : QSegment) (L Y : ℚ) : Bool :=
  decide (d.mid.2=0 ∧ d.half.2=0 ∧
    (L≤d.mid.1-d.half.1 ∧ L≤d.mid.1+d.half.1) ∧
    (d.mid.1-d.half.1≤Y ∧ d.mid.1+d.half.1≤Y))

theorem realSupportCheck_sound (d : QSegment) (L Y : ℚ)
    (hc : realSupportCheck d L Y=true) :
    d.measure {s | s.im≠0 ∨ s.re<(L:ℝ) ∨ (Y:ℝ)<s.re}=0 := by
  have h : d.mid.2=0 ∧ d.half.2=0 ∧
      (L≤d.mid.1-d.half.1 ∧ L≤d.mid.1+d.half.1) ∧
      (d.mid.1-d.half.1≤Y ∧ d.mid.1+d.half.1≤Y) := of_decide_eq_true hc
  exact segment_real_support d L Y h.1 h.2.1 h.2.2.1 h.2.2.2

noncomputable def ordinaryMomentCheck (d : QSegment) (y0 : ℚ) (K : ℕ) (mu : List ℚ) : Bool :=
  decide (0<d.coeff.length ∧ d.mid.2=0 ∧ d.half.2=0 ∧ mu.length=K+1) &&
    (List.range (K+1)).all (fun k=>decide (coeffQ mu k=
      arcPolyMoment (d.density*(C (d.mid.1-y0)+C d.half.1*X)^k)))

theorem ordinaryMomentCheck_sound (d : QSegment) (y0 : ℚ) (K : ℕ) (mu : List ℚ)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,
      0≤chebF (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x)
    (hc : ordinaryMomentCheck d y0 K mu=true) :
    mu.length=K+1 ∧ ∀ k≤K,moment d.measure (y0:ℂ) k=(coeffQ mu k:ℂ) := by
  have h : (0<d.coeff.length ∧ d.mid.2=0 ∧ d.half.2=0 ∧ mu.length=K+1) ∧
      ∀ k∈List.range (K+1),coeffQ mu k=
        arcPolyMoment (d.density*(C (d.mid.1-y0)+C d.half.1*X)^k) := by
    simpa only [ordinaryMomentCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] using hc
  refine ⟨h.1.2.2.2,?_⟩
  intro k hk
  rw [h.2 k (List.mem_range.mpr (by omega))]
  exact segment_complex_moment d y0 k h.1.1 h.1.2.1 h.1.2.2.1 hpos

noncomputable def stieltjesMomentCheck (d : QSegment) (phi : ℚ) (K : ℕ) (sm : List ℚ) : Bool :=
  decide (1<phi ∧ 0<d.half.1 ∧ sm.length=K+1) &&
    (List.range (K+1)).all (fun k=>decide (coeffQ sm k=stieltjesQ d phi k))

theorem stieltjesMomentCheck_sound (d : QSegment) (phi : ℚ) (K : ℕ) (sm : List ℚ)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,
      0≤chebF (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x)
    (hc : stieltjesMomentCheck d phi K sm=true) :
    sm.length=K+1 ∧ ∀ k≤K,
      inverseMoment d.measure (((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ)) k=(coeffQ sm k:ℝ) := by
  have h : (1<phi ∧ 0<d.half.1 ∧ sm.length=K+1) ∧
      ∀ k∈List.range (K+1),coeffQ sm k=stieltjesQ d phi k := by
    simpa only [stieltjesMomentCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] using hc
  refine ⟨h.1.2.2,?_⟩
  intro k hk
  rw [h.2 k (List.mem_range.mpr (by omega))]
  exact inverseMoment_stieltjesQ d phi h.1.1 h.1.2.1 hpos k

#print axioms ordinaryMomentCheck_sound
#print axioms stieltjesMomentCheck_sound
#print axioms realSupportCheck_sound

end CatalanCore.Li2.DecayCert.LatticeGate
