module

public import CatalanMeasure.GenD.Analytic.InverseImageKeyhole
public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.Signed.Davis.Trimmed130Branches

@[expose] public section

/-!
# Generic design weights from contour bounds

One generic adapter and its D58 instance. Numerical circle, segment and entropy bounds
are explicit hypotheses. No Design72Weights or S1RealSegments import is used.
-/

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 0

namespace CatalanMeasure.GenD.Signed.Davis

open Set Polynomial CatalanMeasure.GenD.Analytic OAI.InternalCatalan CatalanMeasure.Parametric
open CatalanMeasure.Refinement.Trimmed130

noncomputable section

/-- Circle affine rate for an arbitrary design; the denominator is controlled by hn0. -/
def contourOmega (P : Parameters) (radius circleCap κ : ℝ) : ℝ :=
  ((2 * (P.g0 : ℝ) - (P.n0 : ℝ) * κ) * Real.log radius + circleCap) / P.n0

theorem n0_mul_contourOmega (P : Parameters) (hn0 : 0 < P.n0)
    (radius circleCap κ : ℝ) :
    (P.n0 : ℝ) * contourOmega P radius circleCap κ =
      (2 * (P.g0 : ℝ) - (P.n0 : ℝ) * κ) * Real.log radius + circleCap := by
  have hn : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  unfold contourOmega
  field_simp

/-- Generic contour-to-weight adapter. tau and green are bound to the SAME p,m,certificate;
no independently named nodes or Green function are silently substituted. -/
theorem hweights_of_contour (P : Parameters)
    (hgn : P.g0 ≤ P.n0) (hdpos : 0 < P.n0 - P.g0)
    (hn0 : 0 < P.n0) (hPQ : 0 < P.h0 + P.q0)
    {p : ℝ[X]} {m : ℕ} {G : ℝ → Prop}
    (cert : InverseBranchCertificate p m G) (hdeg : p.natDegree = m) (hm : 0 < m)
    (τ : ∀ N : ℕ, Fin ((P.n0 - P.g0) * N) → ℝ)
    (hτ : τ = inverseQuadratureNodes P cert hm)
    (green : ℂ → ℝ) (hgreen : green = nodalGreen p m)
    (radius circleCap Ψ w : ℝ) (hr0 : 0 < radius) (hr1 : radius ≤ 1)
    (hcirc : ∀ z : ℂ, ‖z‖ = radius →
      ((P.h0 + P.q0 : ℕ) : ℝ) * Real.log ‖(1 : ℂ) - z‖ +
        ((P.n0 - P.g0 : ℕ) : ℝ) * green z ≤ circleCap)
    (hseg : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, radius ≤ |x| → |x| ≤ 1 →
      nodalPhi P green κ (x : ℂ) ≤
        (2 * (P.g0 : ℝ) - (P.n0 : ℝ) * κ) * Real.log radius + circleCap)
    (hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, contourOmega P radius circleCap κ + binomRate κ ≤ Ψ)
    (hw : (P.n0 : ℝ) * Ψ < w) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ a b : ℕ, a + b = P.n N →
      ∀ k : ℕ, k < P.n N → ∀ i : Fin ((P.n0 - P.g0) * N),
        |(rowCommonFactor P N).eval (τ N i)| *
          |restrictedWeight P N k (τ N) i| * (CatalanMeasure.binomBeta a b k : ℝ) ≤
            108000 * (N : ℝ) * Real.exp (w * N) := by
  subst green
  subst τ
  have hcircle : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, ‖z‖ = radius →
      nodalPhi P (nodalGreen p m) κ z ≤
        (P.n0 : ℝ) * contourOmega P radius circleCap κ := by
    intro κ hκ z hz
    rw [n0_mul_contourOmega P hn0]
    unfold nodalPhi
    rw [hz]
    linarith [hcirc z hz]
  have hsegment : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, radius ≤ |x| → |x| ≤ 1 →
      nodalPhi P (nodalGreen p m) κ (x : ℂ) ≤
        (P.n0 : ℝ) * contourOmega P radius circleCap κ := by
    intro κ hκ x hrl hxu
    rw [n0_mul_contourOmega P hn0]
    exact hseg κ hκ x hrl hxu
  exact inverseImage_binom_hweights_of_phi P hgn hdpos hn0 hPQ cert hdeg hm hr0 hr1
    (contourOmega P radius circleCap) hcircle hsegment hΨ hw

/-- The pinned Green function for the actual degree130 branch polynomial. -/
def green58 (z : ℂ) : ℝ := nodalGreen realP 130 z

/-- D58 specialization of the same generic affine circle rate. -/
def omega58 (circleCap κ : ℝ) : ℝ :=
  ((10 - 58 * κ) * Real.log (3 / 5) + circleCap) / 58

theorem contourOmega_dc58 (circleCap κ : ℝ) :
    contourOmega dc58.toParameters (3 / 5) circleCap κ = omega58 circleCap κ := by
  norm_num [contourOmega, omega58, dc58, DesignConst.toParameters]

/-- D58 instance, with exact canonical-node binding. RouteI.Nodes.tau58 supplies hτ by rfl;
this generic module need not import that unbuilt design adapter or any D72 weight chain. -/
theorem hweights58
    (τ : ∀ N : ℕ, Fin (53 * N) → ℝ)
    (hτ : τ = inverseQuadratureNodes dc58.toParameters branchCertificate (by norm_num))
    (circleCap Ψ : ℝ)
    (hcirc : ∀ z : ℂ, ‖z‖ = (3 / 5 : ℝ) →
      6 * Real.log ‖(1 : ℂ) - z‖ + 53 * green58 z ≤ circleCap)
    (hseg : ∀ κ ∈ Icc (0 : ℝ) 1, ∀ x : ℝ, (3 / 5 : ℝ) ≤ |x| → |x| ≤ 1 →
      nodalPhi dc58.toParameters green58 κ (x : ℂ) ≤
        (10 - 58 * κ) * Real.log (3 / 5) + circleCap)
    (hΨ : ∀ κ ∈ Icc (0 : ℝ) 1, omega58 circleCap κ + binomRate κ ≤ Ψ / 58)
    (hΨstrict : Ψ < (8723 / 100 : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ a b : ℕ, a + b = 58 * N →
      ∀ k : ℕ, k < 58 * N → ∀ i : Fin (53 * N),
        |(rowCommonFactor dc58.toParameters N).eval (τ N i)| *
          |restrictedWeight dc58.toParameters N k (τ N) i| *
          (CatalanMeasure.binomBeta a b k : ℝ) ≤
            108000 * (N : ℝ) * Real.exp ((8723 / 100 : ℝ) * N) := by
  have hw : (dc58.toParameters.n0 : ℝ) * (Ψ / 58) < (8723 / 100 : ℝ) := by
    change (58 : ℝ) * (Ψ / 58) < (8723 / 100 : ℝ)
    nlinarith
  apply hweights_of_contour dc58.toParameters (by norm_num [dc58, DesignConst.toParameters])
    (by norm_num [dc58, DesignConst.toParameters])
    (by norm_num [dc58, DesignConst.toParameters])
    (by norm_num [dc58, DesignConst.toParameters])
    branchCertificate realP_natDegree (by norm_num) τ hτ green58 rfl
    (3 / 5) circleCap (Ψ / 58) (8723 / 100) (by norm_num) (by norm_num) ?_ ?_ ?_ hw
  · intro z hz
    simpa [dc58, DesignConst.toParameters] using hcirc z hz
  · intro κ hκ x hrl hxu
    convert hseg κ hκ x hrl hxu using 1 <;> norm_num [dc58, DesignConst.toParameters]
  · intro κ hκ
    rw [contourOmega_dc58]
    exact hΨ κ hκ

end
end CatalanMeasure.GenD.Signed.Davis

#print axioms CatalanMeasure.GenD.Signed.Davis.hweights_of_contour
#print axioms CatalanMeasure.GenD.Signed.Davis.hweights58
