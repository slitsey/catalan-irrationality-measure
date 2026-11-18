module
public import CatalanCore.Li2.DecayCert.Assembly.Base
public import CatalanCore.Li2.DecayCert.Lattice
public import CatalanCore.Li2.Uniform.DecayBridge
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem latticeCert_window (z : ℚ) (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (hc : latticeSetupCheck z d c=true) (hp : latticeCheck z d c p=true)
    (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F) (hF : F.pure=true) :
    (p.lower:ℝ)≤CatalanCore.Li2.Uniform.dual F (CatalanCore.Li2.Uniform.signOf (z:ℝ))
      (Real.log (1/|(z:ℝ)|)) (p.rho:ℝ) d.data.dual (c.theta:ℝ) ∧
      CatalanCore.Li2.Uniform.WindowBound z (p.rho:ℝ) (p.lower:ℝ) := by
  have ha := (latticeSetupCheck_parts z d c hc).1
  have hz : ValidZ (z:ℝ) := by
    constructor
    · exact_mod_cast ha.1
    · exact_mod_cast ha.2.1
  have hfree : FreeBound (z:ℝ) F d.data.dual (c.theta:ℝ) := by
    intro u hu
    change u∈F.free (CatalanCore.Li2.Uniform.signOf (z:ℝ)) at hu
    rw [F.pure_free hF] at hu
    exact False.elim hu
  have hρ : (0:ℝ)<(p.rho:ℝ) := by exact_mod_cast (latticeCheck_parts z d c p hp).1
  have hbound : (p.lower:ℝ)≤dualValue (z:ℝ) (p.rho:ℝ) F d.data.dual.σ (c.theta:ℝ) := by
    have hb := latticeCert_D_ge z d c p hc hp
    simpa only [dualValue,latPenalty,lat,CatalanCore.Li2.Uniform.lat,F.pure_lattice hF] using hb
  refine ⟨?_,family_window_bound z hz _ _ ((li2_window_decay (z:ℝ) hz F g d.data.dual c.theta p.rho hρ hfree).mono hbound)⟩
  rwa [CatalanCore.Li2.Uniform.decay_dual_eq (z:ℝ) p.rho hz F d.data.dual c.theta] at hbound

theorem bentCheck_validZ (z : ℚ) (b : BentInput) (c : BentCert) (hc : bentSegmentCheck z b c=true) :
    ValidZ (z:ℝ) := by
  have hs := (bentSegmentCheck_parts z b c hc).1
  have hn : (z:ℝ)<0 := by exact_mod_cast hs.2.1
  have hl : (-1:ℝ)<(z:ℝ) := by exact_mod_cast hs.1
  exact ⟨abs_pos.mpr hn.ne,by rw [abs_of_neg hn]; linarith⟩

theorem bentSegCert_D_ge (z : ℚ) (b : BentInput) (c : BentCert)
    (hc : bentSegmentCheck z b c=true) (ρ lam D : ℚ) (hp : bentPairCheck c ρ lam D=true) :
    (D:ℝ)≤dualValue (z:ℝ) (ρ:ℝ) b.geom.frame b.data.dual.σ (lam:ℝ) ∧
      CatalanCore.Li2.Uniform.Admissible b.geom.frame (-1) (Real.log (1/|(z:ℝ)|)) b.data.dual (lam:ℝ) := by
  have hz := bentCheck_validZ z b c hc
  have hn : (z:ℝ)<0 := by exact_mod_cast (bentSegmentCheck_parts z b c hc).1.2.1
  have hz0 : z≠0 := by exact_mod_cast hn.ne
  have hparts := bentSegmentCheck_parts z b c hc
  have hpair := hp
  simp only [bentPairCheck,Bool.and_eq_true,decide_eq_true_eq] at hpair
  have hlam : (c.ell:ℝ)≤(lam:ℝ) := by exact_mod_cast hpair.1.2
  have hs := bentSegmentCheck_sound z b c hc
  have hfree : FreeBound (z:ℝ) b.geom.frame b.data.dual (lam:ℝ) := fun u hu => (hs.1 u hu).trans hlam
  have hA := atomPosSum_upper z hz0 b.data c.density hparts.2.1 c.atoms hparts.2.2.2.2.2.1 ρ lam
  have hscalar := scalarLowerCheck_sound _ _ hpair.2
  simp only [seSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    seScale_value,ScalarExpr.value,seRat_value,Rat.cast_neg,Rat.cast_ofNat] at hscalar
  push_cast at hscalar
  have hcut : CatalanCore.Li2.Uniform.frameCut b.geom.geometry=some 0 := by
    simp only [BentFrame.geometry,CatalanCore.Li2.Uniform.frameCut,b.geom.cut_zero]
  refine ⟨?_,?_⟩
  · unfold dualValue
    rw [frameCut_zero_latPenalty _ b.geom.geometry hcut]
    linarith [hs.2]
  · have hadm := (CatalanCore.Li2.Uniform.decay_freeBound_iff (z:ℝ) hz b.geom.frame b.data.dual lam).mp hfree
    have hsign : CatalanCore.Li2.Uniform.signOf (z:ℝ)= -1 := by simp [CatalanCore.Li2.Uniform.signOf,not_lt.mpr hn.le]
    rwa [hsign] at hadm

theorem bentSegCert_window (z : ℚ) (b : BentInput) (c : BentCert)
    (hc : bentSegmentCheck z b c=true) (ρ lam D : ℚ) (hp : bentPairCheck c ρ lam D=true) :
    CatalanCore.Li2.Uniform.WindowBound z (ρ:ℝ) (D:ℝ) := by
  have hz := bentCheck_validZ z b c hc
  have hpair := hp
  simp only [bentPairCheck,Bool.and_eq_true,decide_eq_true_eq] at hpair
  have hρ : (0:ℝ)<(ρ:ℝ) := by exact_mod_cast hpair.1.1
  have hlam : (c.ell:ℝ)≤(lam:ℝ) := by exact_mod_cast hpair.1.2
  have hs := bentSegmentCheck_sound z b c hc
  have hfree : FreeBound (z:ℝ) b.geom.frame b.data.dual (lam:ℝ) := fun u hu => (hs.1 u hu).trans hlam
  exact family_window_bound z hz D ρ ((li2_window_decay (z:ℝ) hz b.geom.frame b.geom.geometry b.data.dual lam ρ hρ hfree).mono
    (bentSegCert_D_ge z b c hc ρ lam D hp).1)
#print axioms latticeCert_window
#print axioms bentSegCert_D_ge
#print axioms bentSegCert_window
end
end CatalanCore.Li2.DecayCert
