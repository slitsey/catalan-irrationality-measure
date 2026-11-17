module

public import CatalanCore.Li2.Uniform.Spec

@[expose] public section
set_option Elab.async false
open MeasureTheory Set
open scoped BigOperators

namespace CatalanCore.Li2.Decay

noncomputable def P (σ : Measure ℂ) (s : ℂ) : ℝ := ∫ y, Real.log ‖s-y‖ ∂σ
noncomputable def U (σ : Measure ℂ) (s : ℂ) : ℝ := -P σ s
noncomputable def I (σ : Measure ℂ) : ℝ := ∫ s, U σ s ∂σ
noncomputable abbrev phi0 := CatalanCore.Li2.Uniform.phi0
noncomputable def kappaRate (z : ℝ) : ℝ := if 0 < z then 2*Real.pi else Real.pi
noncomputable def V (z : ℝ) (s : ℂ) : ℝ :=
  phi0 s + Real.log |z| * s.re - kappaRate z * |s.im|
noncomputable def omega (z x : ℝ) : ℝ := phi0 (-(x:ℂ))-x*Real.log |z|
noncomputable def W (z : ℝ) (σ : Measure ℂ) (s : ℂ) : ℝ := V z s-2*U σ s
noncomputable def A (z ρ : ℝ) (σ : Measure ℂ) (x : ℝ) : ℝ :=
  omega z x-ρ-2*U σ (-(x:ℂ))
def pos (x : ℝ) : ℝ := max x 0
def ValidZ (z : ℝ) : Prop := 0 < |z| ∧ |z| < 1

abbrev DualDatum := CatalanCore.Li2.Uniform.DualDatum
abbrev Frame := CatalanCore.Li2.Uniform.DualFrame
abbrev FrameGeometry := CatalanCore.Li2.Uniform.FrameGeometry
abbrev free := CatalanCore.Li2.Uniform.free
abbrev lat := CatalanCore.Li2.Uniform.lat

noncomputable def DualDatum.R (d : DualDatum) : ℝ := d.radius
noncomputable def DualDatum.α (d : DualDatum) : ℝ := d.holderExponent
noncomputable def DualDatum.C (d : DualDatum) : ℝ := (d.holderConstant:ℝ)

def FreeBound (z : ℝ) (F : Frame) (d : DualDatum) (θ : ℝ) : Prop :=
  ∀ s ∈ free F z, W z d.σ s ≤ θ
noncomputable def latPenalty (z : ℝ) (F : Frame) (σ : Measure ℂ) (θ : ℝ) : ℝ :=
  ∫ x in lat F, pos (W z σ (x:ℂ)-θ)
noncomputable def atomPenalty (z ρ : ℝ) (σ : Measure ℂ) (θ : ℝ) : ℝ :=
  ∫ x in (1:ℝ)..4, pos (A z ρ σ x-θ)
noncomputable def dualValue (z ρ : ℝ) (F : Frame) (σ : Measure ℂ) (θ : ℝ) : ℝ :=
  -(12*Real.log 2+4)-I σ-2*θ-2*latPenalty z F σ θ-atomPenalty z ρ σ θ

/-- The free field agrees with the explicit negative-axis atom field. -/
theorem atom_field_eq_extension (z x : ℝ) : V z (-(x:ℂ))=omega z x := by
  simp [V, omega, mul_comm, sub_eq_add_neg]

#print axioms atom_field_eq_extension

end CatalanCore.Li2.Decay