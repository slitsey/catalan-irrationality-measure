module
public import CatalanCore.Li2.DecayCert.Compile
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem abs_sub_le_derivative_majorant (f g df dg : ℝ → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hf : ContinuousOn f (Icc 0 D)) (hg : ContinuousOn g (Icc 0 D)) (hg0 : g 0=0)
    (hdf : ∀ t ∈ Ioo 0 D,HasDerivAt f (df t) t)
    (hdg : ∀ t ∈ Ioo 0 D,HasDerivAt g (dg t) t)
    (hbound : ∀ t ∈ Ioo 0 D,|df t| ≤ dg t) :
    ∀ t ∈ Icc 0 D,|f t-f 0| ≤ g t := by
  have hmono1 : MonotoneOn (fun t => g t-f t) (Icc 0 D) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 D) (hg.sub hf)
    · intro t ht
      have ht' : t ∈ Ioo 0 D := by simpa only [interior_Icc] using ht
      exact ((hdg t ht').sub (hdf t ht')).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 D := by simpa only [interior_Icc] using ht
      exact sub_nonneg.mpr ((le_abs_self _).trans (hbound t ht'))
  have hmono2 : MonotoneOn (fun t => g t+f t) (Icc 0 D) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 D) (hg.add hf)
    · intro t ht
      have ht' : t ∈ Ioo 0 D := by simpa only [interior_Icc] using ht
      exact ((hdg t ht').add (hdf t ht')).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 D := by simpa only [interior_Icc] using ht
      have hh := (abs_le.mp (hbound t ht')).1
      linarith
  intro t ht
  have h1 := hmono1 (show (0:ℝ) ∈ Icc 0 D from ⟨le_rfl,hD⟩) ht ht.1
  have h2 := hmono2 (show (0:ℝ) ∈ Icc 0 D from ⟨le_rfl,hD⟩) ht ht.1
  dsimp only at h1 h2
  rw [hg0] at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem holder_sqrt_derivative_bound (f df : ℝ → ℝ) (D A B : ℝ)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ContinuousOn f (Icc 0 D))
    (hdf : ∀ t ∈ Ioo 0 D,HasDerivAt f (df t) t)
    (hb : ∀ t ∈ Ioo 0 D,|df t| ≤ A/Real.sqrt t+B) :
    ∀ t ∈ Icc 0 D,|f t-f 0| ≤ 2*A*Real.sqrt D+B*D := by
  let g : ℝ → ℝ := fun t => 2*A*Real.sqrt t+B*t
  have hdg (t : ℝ) (ht : t ∈ Ioo 0 D) : HasDerivAt g (A/Real.sqrt t+B) t := by
    have hs := Real.sqrt_pos.2 ht.1
    convert ((Real.hasDerivAt_sqrt ht.1.ne').const_mul (2*A)).add ((hasDerivAt_id' t).const_mul B) using 1 <;>
      field_simp [hs.ne'] <;> ring
  have hg : Continuous g := by dsimp only [g]; fun_prop
  have he := abs_sub_le_derivative_majorant f g df (fun t => A/Real.sqrt t+B) D hD hf hg.continuousOn
    (by simp [g]) hdf hdg hb
  intro t ht
  apply (he t ht).trans
  dsimp only [g]
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2) (by positivity))
    (mul_le_mul_of_nonneg_left ht.2 hB)

theorem holder_linear_derivative_bound (f df : ℝ → ℝ) (D B : ℝ)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hf : ContinuousOn f (Icc 0 D))
    (hdf : ∀ t ∈ Ioo 0 D,HasDerivAt f (df t) t)
    (hb : ∀ t ∈ Ioo 0 D,|df t| ≤ B) :
    ∀ t ∈ Icc 0 D,|f t-f 0| ≤ B*D := by
  have he := abs_sub_le_derivative_majorant f (fun t => B*t) df (fun _ => B) D hD hf (by fun_prop)
    (by simp) hdf (fun t ht => by simpa using (hasDerivAt_id' t).const_mul B) hb
  intro t ht
  exact (he t ht).trans (mul_le_mul_of_nonneg_left ht.2 hB)
#print axioms abs_sub_le_derivative_majorant
#print axioms holder_sqrt_derivative_bound
#print axioms holder_linear_derivative_bound
end
end CatalanCore.Li2.DecayCert
