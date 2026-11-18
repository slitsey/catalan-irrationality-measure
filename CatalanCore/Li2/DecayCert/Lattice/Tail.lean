module
public import CatalanCore.Li2.DecayCert.Lattice.Energy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

def latticeMajorant (z R x : ℝ) : ℝ :=
  3*Real.log (x+1)-4*Real.log x+Real.log |z| *x+4*Real.log (x+R)

theorem phi0_real_upper (x : ℝ) (hx : 1 ≤ x) :
    phi0 (x:ℂ) ≤ 3*Real.log (x+1)-4*Real.log x := by
  have hcont (B : ℝ) (hB : 0 ≤ B) : ContinuousOn (fun t : ℝ => Real.log (x+t)) (Icc 0 B) := by
    apply (continuous_const.add continuous_id).continuousOn.log
    intro t ht
    change x+t ≠ 0
    linarith [ht.1]
  have hi1 := (hcont 1 (by norm_num)).intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (0:ℝ) ≤ 1)
  have hi4 := (hcont 4 (by norm_num)).intervalIntegrable_of_Icc (μ:=volume) (by norm_num : (0:ℝ) ≤ 4)
  have hu : (∫ t in (0:ℝ)..1,Real.log (x+t)) ≤ Real.log (x+1) := by
    have h := intervalIntegral.integral_mono_on (f:=fun t : ℝ => Real.log (x+t))
      (g:=fun _ : ℝ => Real.log (x+1)) (by norm_num : (0:ℝ) ≤ 1) hi1
      (continuous_const.intervalIntegrable 0 1) (fun t ht => Real.log_le_log (by linarith [ht.1]) (by linarith [ht.2]))
    simpa only [intervalIntegral.integral_const,sub_zero,one_smul] using h
  have hl : 4*Real.log x ≤ ∫ t in (0:ℝ)..4,Real.log (x+t) := by
    have h := intervalIntegral.integral_mono_on (f:=fun _ : ℝ => Real.log x)
      (g:=fun t : ℝ => Real.log (x+t)) (by norm_num : (0:ℝ) ≤ 4)
      (continuous_const.intervalIntegrable 0 4) hi4 (fun t ht => Real.log_le_log (by linarith) (by linarith [ht.1]))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] using h
  change 3*(∫ t in (0:ℝ)..1,Real.log ‖(x:ℂ)+(t:ℂ)‖)-
    (∫ t in (0:ℝ)..4,Real.log ‖(x:ℂ)+(t:ℂ)‖) ≤ _
  simp_rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
  linarith

theorem latticeMajorant_field (z R x : ℝ) (d : DualDatum) (hR : 0 ≤ R)
    (hb : ∀ᵐ u : ℂ ∂d.σ,‖u‖ ≤ R) (hx : 1 ≤ x) :
    W z d.σ (x:ℂ) ≤ latticeMajorant z R x := by
  haveI := d.finite
  have hP : P d.σ (x:ℂ) ≤ 2*Real.log (x+R) := by
    have hi := integral_mono_ae (d.pointLogIntegrable (x:ℂ)) (integrable_const (Real.log (x+R)))
      (show ∀ᵐ u : ℂ ∂d.σ,Real.log ‖(x:ℂ)-u‖ ≤ Real.log (x+R) from by
        filter_upwards [hb] with u hu
        have hn : ‖(x:ℂ)-u‖ ≤ x+R := by
          exact (norm_sub_le _ _).trans (by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ x)] using add_le_add (le_refl x) hu)
        by_cases hzero : ‖(x:ℂ)-u‖=0
        · rw [hzero,Real.log_zero]
          exact Real.log_nonneg (by linarith)
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hn)
    simpa only [P,integral_const,smul_eq_mul,d.mass] using hi
  have hphi := phi0_real_upper x hx
  simp only [W,V,U,Complex.ofReal_re,Complex.ofReal_im,abs_zero,mul_zero,sub_zero,latticeMajorant]
  linarith

theorem latticeMajorant_hasDerivAt (z R x : ℝ) (hR : 0 ≤ R) (hx : 0 < x) :
    HasDerivAt (latticeMajorant z R)
      (3/(x+1)-4/x+Real.log |z|+4/(x+R)) x := by
  have hd := (((((hasDerivAt_id x).add_const 1).log (by change x+1 ≠ 0; linarith)).const_mul 3).sub
    (((hasDerivAt_id x).log hx.ne').const_mul 4)).add
    ((hasDerivAt_id x).const_mul (Real.log |z|)) |>.add
    ((((hasDerivAt_id x).add_const R).log (by change x+R ≠ 0; linarith)).const_mul 4)
  convert hd using 1 <;> (try rfl) <;> simp only [id_eq,mul_one] <;> ring

theorem latticeMajorant_antitone (z R C : ℝ) (hR : 0 ≤ R) (hC : 1 ≤ C)
    (hslope : 3/(C+1)+Real.log |z| ≤ 0) : AntitoneOn (latticeMajorant z R) (Ici C) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici C)
  · intro x hx
    exact (latticeMajorant_hasDerivAt z R x hR (by have hh : C ≤ x := hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    exact (latticeMajorant_hasDerivAt z R x hR (by have hh : C ≤ x := interior_subset hx; linarith)).hasDerivWithinAt
  · intro x hx
    have hCx : C ≤ x := interior_subset hx
    have hx0 : 0 < x := by linarith
    have h4 : 4/(x+R) ≤ (4:ℝ)/x := div_le_div_of_nonneg_left (by norm_num) hx0 (by linarith)
    have h3 : 3/(x+1) ≤ (3:ℝ)/(C+1) := div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith

theorem latticeTail_checked (z : ℚ) (d : LatticeInput) (c : LatticeSetup)
    (hd : datumCheck d.data c.density=true) (hC : 1 ≤ c.cutoff)
    (ht : scalarUpperCheck (latticeTailExpr z d c) c.theta=true)
    (hs : scalarUpperCheck (seAdd (seRat (3/(c.cutoff+1))) (.log c.terms |z|)) 0=true) :
    ∀ x : ℝ,(c.cutoff:ℝ) ≤ x → W (z:ℝ) d.data.dual.σ (x:ℂ) ≤ (c.theta:ℝ) := by
  have hR : (0:ℝ) ≤ (d.data.radius:ℝ) := by exact_mod_cast (sourceDataCheck_parts d.data.segments d.data.radius c.density hd).1.1
  have hCR : (1:ℝ) ≤ (c.cutoff:ℝ) := by exact_mod_cast hC
  have hslope := scalarUpperCheck_sound _ _ hs
  simp only [seAdd_value,seRat_value,ScalarExpr.value,Rat.cast_zero,Rat.cast_div,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,Rat.cast_abs] at hslope
  have htail := scalarUpperCheck_sound _ _ ht
  have he : (latticeTailExpr z d c).value=latticeMajorant (z:ℝ) (d.data.radius:ℝ) (c.cutoff:ℝ) := by
    simp only [latticeTailExpr,seSum,List.foldl_cons,List.foldl_nil,seAdd_value,seScale_value,seRat_value,ScalarExpr.value,latticeMajorant]
    push_cast
    ring
  rw [he] at htail
  intro x hx
  have hfield := latticeMajorant_field (z:ℝ) (d.data.radius:ℝ) x d.data.dual hR (datumCheck_positive d.data c.density hd).2 (hCR.trans hx)
  exact hfield.trans ((latticeMajorant_antitone _ _ _ hR hCR hslope le_rfl hx hx).trans htail)
#print axioms latticeMajorant_field
#print axioms latticeMajorant_antitone
#print axioms latticeTail_checked
end
end CatalanCore.Li2.DecayCert
