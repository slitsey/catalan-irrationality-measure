module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Integral
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set MeasureTheory
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert.LatticeGate

theorem pos_integral_zero (f : ℝ→ℝ) (a b : ℝ)
    (hab : a≤b) (h : ∀x∈Icc a b,f x≤0) :
    (∫x in a..b,pos (f x))=0 := by
  calc
    _=∫x in a..b,(0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact max_eq_right (h x hx)
    _=0 := by simp

theorem pos_integral_constant (f : ℝ→ℝ) (a b hi : ℝ)
    (hab : a≤b) (hf : ContinuousOn f (Icc a b))
    (h : ∀x∈Icc a b,f x≤hi) :
    (∫x in a..b,pos (f x))≤(b-a)*max hi 0 := by
  have hp : ContinuousOn (fun x=>pos (f x)) (Icc a b) := fun x hx=>Filter.Tendsto.max (hf x hx) tendsto_const_nhds
  calc
    _≤∫x in a..b,max hi 0 := by
      apply intervalIntegral.integral_mono_on hab
        (hp.intervalIntegrable_of_Icc hab) (continuous_const.intervalIntegrable _ _)
      intro x hx
      exact max_le_max_right 0 (h x hx)
    _=_ := by simp [smul_eq_mul]

theorem positive_model_integral (f : ℝ→ℝ) (co : List ℚ) (hne : co≠[])
    (a b E : ℚ) (hab : a≤b) (ha : -1≤a) (hb : b≤1)
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hm : ModelsOn f (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (bs : List (ℚ×ℚ))
    (ht : BernsteinGrid.CellBoxRep (qListPoly co) a b (co.length-1) bs)
    (hfloor : ∀x∈Icc (a:ℝ) (b:ℝ),0≤f x) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x))≤
      ((b:ℝ)-a)*((upperMeanQ bs:ℝ)+(E:ℝ)) := by
  have hn := qListPoly_natDegree_lt co hne
  let p := (qListPoly co).map (Rat.castHom ℝ)
  have he (x : ℝ) : p.eval x=evalModel (co.map (fun q : ℚ => (q:ℝ))) x := by
    dsimp only [p]
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) hn]
    simp only [qListPoly_coeff,evalModel_map_rat]
    rfl
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  have hp : Continuous (fun x : ℝ=>p.eval x) := p.continuous
  have hpos : ContinuousOn (fun x=>pos (f x)) (Icc (a:ℝ) (b:ℝ)) := fun x hx=>Filter.Tendsto.max (hf x hx) tendsto_const_nhds
  have hpoly := cell_polynomial_integral_upper (qListPoly co) a b (co.length-1)
    (by omega) hab bs ht
  calc
    _≤∫x in (a:ℝ)..(b:ℝ),p.eval x+(E:ℝ) := by
      apply intervalIntegral.integral_mono_on habR (hpos.intervalIntegrable_of_Icc habR)
        ((hp.add continuous_const).intervalIntegrable _ _)
      intro x hx
      change max (f x) 0≤p.eval x+(E:ℝ)
      rw [max_eq_left (hfloor x hx),he]
      have hx' : x∈Icc (-1:ℝ) 1 := by
        have haR : (-1:ℝ)≤(a:ℝ) := by exact_mod_cast ha
        have hbR : (b:ℝ)≤1 := by exact_mod_cast hb
        exact ⟨haR.trans hx.1,hx.2.trans hbR⟩
      have hh := (abs_le.mp (hm.2.2 x hx')).2
      linarith
    _=(∫x in (a:ℝ)..(b:ℝ),p.eval x)+((b:ℝ)-a)*(E:ℝ) := by
      rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
      simp [smul_eq_mul]
    _≤((b:ℝ)-a)*(upperMeanQ bs:ℝ)+((b:ℝ)-a)*(E:ℝ) := by
      dsimp only [p]
      linarith only [hpoly]
    _=_ := by ring

#print axioms pos_integral_zero
#print axioms pos_integral_constant
#print axioms positive_model_integral
end CatalanCore.Li2.DecayCert.LatticeGate
