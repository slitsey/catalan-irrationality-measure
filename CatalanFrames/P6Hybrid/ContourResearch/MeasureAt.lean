module
public import CatalanFrames.P6Hybrid.QuarterSelect
public import CatalanFrames.P6Hybrid.QuarterPeriodicContent
public import CatalanFrames.P6.Const
public import CatalanCore.Measure.Pinned
public import CatalanCore.Measure.Scaling
public import CatalanCore.Decay.Rect.HybridHook
public import CatalanFrames.P6Hybrid.ContourResearch.AllowedSlopes
@[expose] public section
open CatalanCore CatalanCore.Rect CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.QuarterContour
noncomputable abbrev family : PolyFamily := commonMinorFam p6Frame Quarter.Adm 1

theorem measure_of_decay {D c E : ℚ} (hD : HasDecay family (D : ℝ) (c : ℝ))
    (hgap : (339258406689121/82516315939200 : ℚ) < D) (hc : 0 < c)
    (hsmall : D-(339258406689121/82516315939200 : ℚ) < 1)
    (hE : c/(D-(339258406689121/82516315939200 : ℚ)) ≤ E) :
    family.MeasureLB (E : ℝ) := by
  have hC : HasContent family (((339258406689121/82516315939200 : ℚ)) : ℝ) := by
    convert Quarter.Periodic.hasContent 1 using 1 <;> norm_num
  exact Measure.measure_of_family_pin_leC family
    (c := c) (Λ := 339258406689121/82516315939200) (D := D)
    (α := 1) (β := 2) (s := 1) (E' := E) hC hD hgap hc
    (by norm_num) (by norm_num) (by convert hsmall using 1 <;> norm_num)
    (by convert Quarter.hasNVPin using 1 <;> norm_num)
    (by convert p6_window_square using 1 <;> norm_num) hE

theorem chi3_measure_of_decay {D c E : ℚ} (hE0 : 0 ≤ E)
    (hD : HasDecay family (D : ℝ) (c : ℝ))
    (hgap : (339258406689121/82516315939200 : ℚ) < D) (hc : 0 < c)
    (hsmall : D-(339258406689121/82516315939200 : ℚ) < 1)
    (hE : c/(D-(339258406689121/82516315939200 : ℚ)) ≤ E) :
    Measure.MeasureLBAt chi3L2 (E : ℝ) := by
  have h' : Measure.MeasureLBAt p6Frame.const (E : ℝ) := by
    have h := (Measure.MeasureLB_iff family (E : ℝ)).mp (measure_of_decay hD hgap hc hsmall hE)
    convert h using 1 <;> norm_num [family, commonMinorFam]
  have he : chi3L2 = ((4 : ℚ) : ℝ)*p6Frame.const+((0 : ℚ) : ℝ) := by
    rw [p6Frame_const]
    push_cast
    ring
  rw [he]
  exact h'.affine (by exact_mod_cast hE0) 4 0 (by norm_num)

theorem adm_window {r m : ℕ} (ha : Quarter.Adm r m) :
    (((1/4 : ℚ)) : ℝ)*r ≤ m ∧ (m : ℝ) ≤ (((1/4 : ℚ)) : ℝ)*r+3/4 := by
  have h1 : (r : ℝ) ≤ 4*m := by exact_mod_cast ha.1
  have h2 : (4 : ℝ)*m ≤ r+3 := by exact_mod_cast ha.2
  push_cast
  constructor <;> linarith

theorem decay_of_certificate {sl : ℝ} {K : ℕ} {rho epsilon : ℝ}
    {c : Fin K → ℂ} {wt : Fin K → ℝ} {F : Cert.CertCoreGs sl K rho epsilon c wt}
    {Rc : ℝ} {Inu D : ℚ} (hsl : 1 ≤ sl)
    (hF : HybridDecayData F (1/4) Rc Inu D 3) :
    HasDecay family (D : ℝ) (F.ccert : ℝ) :=
  hF.commonMinorDecay (P6.ContourPreparation.p6_decayOK_atSlope hsl)
    rfl (a := 3/4) (by norm_num) 1 (fun _ _ h => adm_window h)
end CatalanFrames.P6Hybrid.QuarterContour
#print axioms CatalanFrames.P6Hybrid.QuarterContour.chi3_measure_of_decay
#print axioms CatalanFrames.P6Hybrid.QuarterContour.decay_of_certificate
