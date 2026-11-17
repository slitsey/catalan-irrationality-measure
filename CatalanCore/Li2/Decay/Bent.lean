module
public import CatalanCore.Li2.Uniform.Geometry
public import CatalanCore.Tools.CappedDual
public import CatalanCore.Li2.Decay.Fields
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay
theorem bent_crossing (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (hc : CatalanCore.Li2.Uniform.frameCut g=some 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n, 0 ≤ u.re ∧ 1/2 ≤ ‖u‖) ∧
      ({u | u ∈ CatalanCore.Li2.Uniform.gammaN g n ∧ u.im=0} = {(1/2:ℂ)}) ∧
      CatalanCore.Li2.Uniform.replacementLength g n ≤ C ∧
      (∀ u ∈ CatalanCore.Li2.Uniform.replacement g n, ‖u/(n:ℂ)‖ ≤ C/(n:ℝ)) := by
  obtain ⟨C,hC,hrep⟩ := CatalanCore.Li2.Uniform.gammaN_bent_replacement F g hc
  refine ⟨C,hC,?_⟩
  filter_upwards [hrep,CatalanCore.Li2.Uniform.gammaN_kernel_domain F g,
    CatalanCore.Li2.Uniform.gammaN_crossing F g 0 hc] with n hn hdom hcross
  refine ⟨fun u hu => ⟨(hdom u hu).1,(hdom u hu).2.1⟩,?_,hn.1,hn.2⟩
  simpa only [zero_mul,Nat.floor_zero,Nat.cast_zero,zero_add,Complex.ofReal_div,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_zero,zero_add] using hcross

noncomputable def bentMajorant (x R y : ℝ) : ℝ :=
  let r := Real.sqrt (x^2+y^2)
  3*Real.log (r+1)-4*Real.log y+4*Real.log (r+R)-Real.pi*y
noncomputable def bentMajorantDeriv (x R y : ℝ) : ℝ :=
  let r := Real.sqrt (x^2+y^2)
  3*y/(r*(r+1))-4/y+4*y/(r*(r+R))-Real.pi
private theorem bent_derivative (x R y : ℝ) (hR : 0 ≤ R) (hy : 0 < y) :
    HasDerivAt (bentMajorant x R) (bentMajorantDeriv x R y) y ∧
      bentMajorantDeriv x R y ≤ 3/y-Real.pi := by
  let r := Real.sqrt (x^2+y^2)
  have hq : 0 < x^2+y^2 := by nlinarith [sq_nonneg x]
  have hr : 0 < r := Real.sqrt_pos.mpr hq
  have hsq : r^2=x^2+y^2 := Real.sq_sqrt hq.le
  have hry : y ≤ r := by nlinarith [sq_nonneg x]
  have hdq : HasDerivAt (fun t : ℝ => x^2+t^2) (2*y) y := by
    simpa only [id_eq,Pi.pow_apply,Nat.reduceSub,pow_one,mul_one,Nat.cast_ofNat] using ((hasDerivAt_id y).pow 2).const_add (x^2)
  have hdr : HasDerivAt (fun t : ℝ => Real.sqrt (x^2+t^2)) (y/r) y := by
    convert hdq.sqrt hq.ne' using 1 <;> dsimp [r] <;> field_simp <;> ring
  have hd := ((((hdr.const_add 1).log (by dsimp [r] at hr; positivity)).const_mul 3).sub
      (((hasDerivAt_id y).log hy.ne').const_mul 4)).add
      (((hdr.const_add R).log (by dsimp [r] at hr; positivity)).const_mul 4) |>.sub
      ((hasDerivAt_id y).const_mul Real.pi)
  constructor
  · convert hd using 1
    · funext t
      dsimp [bentMajorant]
      ring
    · dsimp [bentMajorantDeriv,r]
      field_simp
      <;> ring
  · have h1 : y/(r*(r+1)) ≤ 1/y := by
      apply (div_le_div_iff₀ (by positivity : 0 < r*(r+1)) hy).mpr
      nlinarith [sq_nonneg x]
    have h2 : y/(r*(r+R)) ≤ 1/y := by
      apply (div_le_div_iff₀ (by positivity : 0 < r*(r+R)) hy).mpr
      nlinarith [mul_nonneg hr.le hR,sq_nonneg x]
    change 3*y/(r*(r+1))-4/y+4*y/(r*(r+R))-Real.pi ≤ _
    calc
      _ = 3*(y/(r*(r+1)))-4/y+4*(y/(r*(r+R)))-Real.pi := by ring
      _ ≤ 3*(1/y)-4/y+4*(1/y)-Real.pi := by gcongr
      _ = _ := by ring
private theorem bent_field (z : ℝ) (hz : ValidZ z) (hneg : z < 0)
    (d : DualDatum) (x y : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) :
    W z d.σ ((x:ℂ)+(y:ℂ)*Complex.I) ≤ bentMajorant x d.radius y := by
  let u : ℂ := (x:ℂ)+(y:ℂ)*Complex.I
  have hy0 : 0 < y := by linarith
  have him : u.im=y := by simp [u]
  have hre : u.re=x := by simp [u]
  have hnorm : ‖u‖=Real.sqrt (x^2+y^2) := by
    rw [Complex.norm_def,Complex.normSq_apply]
    simp only [hre,him]
    congr 1
    ring
  have hlow (t : ℝ) : y ≤ ‖u+(t:ℂ)‖ := by
    have hh := Complex.abs_im_le_norm (u+(t:ℂ))
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero,him,abs_of_pos hy0] using hh
  have hu1 : 1 ≤ ‖u‖ := by simpa only [Complex.ofReal_zero,add_zero] using hy.trans (hlow 0)
  have hi (B : ℝ) : IntervalIntegrable (fun t : ℝ => Real.log ‖u+(t:ℂ)‖) volume 0 B := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    exact (hy0.trans_le (hlow t)).ne'
  have hu := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (by norm_num)
    (hi 1) (intervalIntegrable_const (c := Real.log (‖u‖+1))) (by
      intro t ht
      apply Real.log_le_log (hy0.trans_le (hlow t))
      have hh := norm_add_le u (t:ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] at hh
      linarith [ht.2])
  have hl := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 4) (by norm_num)
    (intervalIntegrable_const (c := Real.log y)) (hi 4) (fun t ht => Real.log_le_log hy0 (hlow t))
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,one_mul] at hu hl
  have hp := CatalanCore.Tools.CappedDual.logPotential_upper d.σ u d.radius d.radius_nonneg
    d.bounded (by linarith [d.radius_nonneg]) (d.pointLogIntegrable u)
  rw [d.mass] at hp
  have hL : Real.log |z| ≤ 0 := Real.log_nonpos hz.1.le hz.2.le
  have hLx : Real.log |z| *x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL hx
  have hzpos : ¬0 < z := by linarith
  change W z d.σ u ≤ _
  simp only [W,V,U,P,kappaRate,if_neg hzpos,him,hre,abs_of_pos hy0,bentMajorant,← hnorm]
  change 3*(∫ t in (0:ℝ)..1, Real.log ‖u+(t:ℂ)‖)-
    (∫ t in (0:ℝ)..4, Real.log ‖u+(t:ℂ)‖)+Real.log |z| *x-Real.pi*y-
    2*(-(∫ w, Real.log ‖u-w‖ ∂d.σ)) ≤ _
  linarith

theorem bent_tail (z : ℝ) (hz : ValidZ z) (hneg : z < 0)
    (d : DualDatum) (x : ℝ) (hx : 0 ≤ x) :
    (∀ y : ℝ, 1 ≤ y → W z d.σ (x+y*Complex.I) ≤ bentMajorant x d.radius y) ∧
    (∀ y : ℝ, 1 ≤ y → HasDerivAt (bentMajorant x d.radius)
      (bentMajorantDeriv x d.radius y) y ∧ bentMajorantDeriv x d.radius y ≤ 3/y-Real.pi) := by
  constructor
  · intro y hy
    exact bent_field z hz hneg d x y hx hy
  · intro y hy
    exact bent_derivative x d.radius y d.radius_nonneg (by linarith)
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.bent_crossing
#print axioms CatalanCore.Li2.Decay.bent_tail
