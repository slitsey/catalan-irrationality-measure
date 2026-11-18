module
public import CatalanCore.Li2.DecayCert.Lattice.PrimitiveDefs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem Gtilde_continuous : Continuous Gtilde := by
  have he : Gtilde=(fun x : ℝ => x*(x*Real.log x)/2-x^2/4) := by
    funext x
    unfold Gtilde
    ring
  rw [he]
  exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).sub ((continuous_id.pow 2).div_const 4)

theorem Gtilde_hasDerivAt (x : ℝ) (hx : 0 < x) : HasDerivAt Gtilde (x*Real.log x) x := by
  have hd := ((((hasDerivAt_id x).pow 2).mul (Real.hasDerivAt_log hx.ne')).div_const 2).sub
    (((hasDerivAt_id x).pow 2).div_const 4)
  convert hd using 1 <;> (try rfl) <;> simp only [id_eq,Pi.pow_apply] <;> field_simp [hx.ne'] <;> ring

theorem freValue_ofReal (x : ℝ) : freValue (x:ℂ)=x*Real.log x-x := by
  simp [freValue,Complex.mul_re,Complex.log_re,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]

theorem phi0_real_closed (x : ℝ) :
    phi0 (x:ℂ)=3*(x+1)*Real.log (x+1)-2*x*Real.log x-(x+4)*Real.log (x+4)+1 := by
  have h1 : (x:ℂ)+1=((x+1:ℝ):ℂ) := by push_cast; rfl
  have h4 : (x:ℂ)+4=((x+4:ℝ):ℂ) := by push_cast; rfl
  rw [phi0_primitive,h1,h4,freValue_ofReal,freValue_ofReal,freValue_ofReal]
  ring

theorem V_real_value (z x : ℝ) : V z (x:ℂ)=phi0 (x:ℂ)+Real.log |z| *x := by
  simp only [V,Complex.ofReal_re,Complex.ofReal_im,abs_zero,mul_zero,sub_zero]

def latticeExternalPrimitive (z θ c0 Y s : ℝ) : ℝ :=
  3*Gtilde (s+1)-Gtilde (s+4)-2*Gtilde s+
    (1-2*c0*Real.log (4/Y)-θ)*s+Real.log |z| *s^2/2

theorem latticeExternalPrimitive_continuous (z θ c0 Y : ℝ) :
    Continuous (latticeExternalPrimitive z θ c0 Y) := by
  unfold latticeExternalPrimitive
  exact ((((Gtilde_continuous.comp (continuous_id.add continuous_const)).const_mul 3).sub
    (Gtilde_continuous.comp (continuous_id.add continuous_const))).sub
    (Gtilde_continuous.const_mul 2) |>.add (continuous_const.mul continuous_id)) |>.add
    ((continuous_const.mul (continuous_id.pow 2)).div_const 2)

theorem latticeExternalPrimitive_hasDerivAt (z θ c0 Y s : ℝ) (hs : 0 < s) :
    HasDerivAt (latticeExternalPrimitive z θ c0 Y)
      (V z (s:ℂ)-2*c0*Real.log (4/Y)-θ) s := by
  have h1 := (Gtilde_hasDerivAt (s+1) (by linarith)).comp s ((hasDerivAt_id s).add_const 1)
  have h4 := (Gtilde_hasDerivAt (s+4) (by linarith)).comp s ((hasDerivAt_id s).add_const 4)
  have h0 := Gtilde_hasDerivAt s hs
  have hd := ((((h1.const_mul 3).sub h4).sub (h0.const_mul 2)).add
    ((hasDerivAt_id s).const_mul (1-2*c0*Real.log (4/Y)-θ))).add
    ((((hasDerivAt_id s).pow 2).const_mul (Real.log |z|)).div_const 2)
  convert hd using 1
  · rfl
  · rw [V_real_value,phi0_real_closed]
    simp only [id_eq,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    ring
#print axioms Gtilde_continuous
#print axioms Gtilde_hasDerivAt
#print axioms phi0_real_closed
#print axioms latticeExternalPrimitive_hasDerivAt
end
end CatalanCore.Li2.DecayCert
