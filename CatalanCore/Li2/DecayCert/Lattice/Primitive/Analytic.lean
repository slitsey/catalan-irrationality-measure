module
public import CatalanCore.Li2.DecayCert.Lattice.Primitive.Own
public import CatalanCore.Li2.DecayCert.Lattice.Primitive.Multipole
public import CatalanCore.Li2.DecayCert.Lattice.Cells
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem mp_real_continuousOn (σ : Measure ℂ) (y0 : ℝ) (hy : y0<0) (K : ℕ) :
    ContinuousOn (fun s : ℝ => mp σ (y0:ℂ) (s:ℂ) K) (Ici 0) := by
  have hsub : ContinuousOn (fun s : ℝ => s-y0) (Ici 0) := (continuous_id.sub continuous_const).continuousOn
  have hne (s : ℝ) (hs : s∈Ici (0:ℝ)) : s-y0≠0 := by have h : 0≤s := hs; linarith
  induction K with
  | zero =>
    have hc := (hsub.log hne).const_mul (-σ.real univ)
    apply hc.congr
    intro s hs
    have hp : 0<s-y0 := by have h : 0≤s := hs; linarith
    simp only [mp,Finset.range_zero,Finset.sum_empty,Complex.zero_re,add_zero,
      ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  | succ K ih =>
    have hden : ContinuousOn (fun s : ℝ => ((K+1:ℕ):ℝ)*(s-y0)^(K+1)) (Ici 0) := continuous_const.continuousOn.mul (hsub.pow _)
    have hc := ih.add ((continuous_const : Continuous (fun _ : ℝ => (moment σ (y0:ℂ) (K+1)).re)).continuousOn.div hden (fun s hs =>
      mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero K)) (pow_ne_zero _ (hne s hs))))
    apply hc.congr
    intro s hs
    exact mp_real_succ σ y0 s K

theorem latticeSecond_log_integrable {σ1 σ2 : Measure ℂ} [IsFiniteMeasure σ2] {Y : ℝ}
    (d : LatticeMomentData σ1 σ2 Y) (s : ℝ) (hs : 0≤s) :
    Integrable (fun u => Real.log ‖(s:ℂ)-u‖) σ2 := by
  have hsep : d.supportRadius<‖(s:ℂ)-(d.y0:ℂ)‖ := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith [d.y0_neg] : 0<s-d.y0)]
    linarith [d.separated]
  have hc : ContinuousOn (fun u : ℂ => Real.log ‖(s:ℂ)-u‖) (Metric.closedBall (d.y0:ℂ) d.supportRadius) := by
    apply (continuous_const.sub continuous_id).norm.continuousOn.log
    intro u hu
    apply norm_ne_zero_iff.mpr
    intro he
    have hsu : (s:ℂ)=u := sub_eq_zero.mp he
    rw [← hsu] at hu
    have hh : ‖(s:ℂ)-(d.y0:ℂ)‖≤d.supportRadius := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hu
    linarith
  apply (hc.integrableOn_compact (isCompact_closedBall _ _)).integrable_of_ae_notMem_eq_zero
  have hae := (measure_eq_zero_iff_ae_notMem).mp d.second_support
  filter_upwards [hae] with u hu
  intro hn
  exfalso
  apply hn
  simpa only [Metric.mem_closedBall,dist_eq_norm,mem_ofPred_eq,not_lt] using hu

theorem V_real_continuous (z : ℝ) : Continuous (fun s : ℝ => V z (s:ℂ)) := by
  have hphi : Continuous (fun s : ℝ => phi0 (s:ℂ)) := by
    convert continuous_phi0_neg.comp continuous_neg using 1
    funext s
    simp only [Function.comp_apply,Complex.ofReal_neg,neg_neg]
  convert hphi.add ((continuous_const : Continuous (fun _ : ℝ => Real.log |z|)).mul continuous_id) using 1
  funext s
  simp only [V_real_value,Pi.add_apply,Pi.mul_apply,id_eq]

def latticeApproxField {σ1 σ2 Y} (z θ : ℝ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) : ℝ :=
  V z (s:ℂ)-2*(d.c 0*Real.log (4/Y)+(ownUPoly d).eval s)-2*d.mpValue K s-θ

theorem latticeApproxField_continuousOn {σ1 σ2 Y} (z θ : ℝ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) :
    ContinuousOn (latticeApproxField z θ d K) (Ici 0) := by
  exact (((V_real_continuous z).continuousOn.sub (continuous_const.continuousOn.mul
    (continuous_const.continuousOn.add (ownUPoly d).continuous.continuousOn))).sub
    (continuous_const.continuousOn.mul (mp_real_continuousOn σ2 d.y0 d.y0_neg K))).sub continuous_const.continuousOn

theorem latticePrimitive_continuousOn {σ1 σ2 Y} (z θ : ℝ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) :
    ContinuousOn (latticePrimitive z θ d K) (Ici 0) := by
  have hmp : ContinuousOn (fun s => multipolePrimitive σ2 d.y0 s K) (Ici 0) :=
    fun s hs => (multipolePrimitive_hasDerivAt σ2 d.y0 d.y0_neg s hs K).continuousAt.continuousWithinAt
  exact ((latticeExternalPrimitive_continuous z θ (d.c 0) Y).continuousOn.sub
    (continuous_const.continuousOn.mul (ownUPoly d).integral.continuous.continuousOn)).sub (continuous_const.continuousOn.mul hmp)

theorem latticePrimitive_derivative {σ1 σ2 Y} (z θ : ℝ) (d : LatticeMomentData σ1 σ2 Y) (K : ℕ) (s : ℝ) (hs : 0<s) :
    HasDerivAt (latticePrimitive z θ d K) (latticeApproxField z θ d K s) s := by
  have he := latticeExternalPrimitive_hasDerivAt z θ (d.c 0) Y s hs
  have ho := (ownUPoly d).integral_eval_hasDerivAt s
  have hm := multipolePrimitive_hasDerivAt σ2 d.y0 d.y0_neg s hs.le K
  convert (he.sub (ho.const_mul 2)).sub (hm.const_mul 2) using 1
  · rfl
  · dsimp only [latticeApproxField,LatticeMomentData.mpValue]
    ring
#print axioms mp_real_continuousOn
#print axioms latticeSecond_log_integrable
#print axioms latticePrimitive_derivative
end
end CatalanCore.Li2.DecayCert
