module

public import CatalanCore.Uniform.Decay.Spline.Bridge
public import CatalanCore.Uniform.Decay.Spline.PolyDensity
public import CatalanCore.Uniform.Decay.Spline.UnuReal

@[expose] public section

/-!
# The bridge for rational polynomial densities (lane D, package D2)

Pieces carry rational coefficient lists `l i` (density `ratPoly (l i)`).  The finite checks are

* exact mass `∑_i ∑_j a_{ij}/(j+1) = 1` (rational equality; `integral_ratPoly`);
* Bernstein `bernOkK (l i) (-M_i) M_i` for both `f` and `-f` (so `|f_i| ≤ M_i` on `[0,1]`, no root isolation),
  giving the presentation variation `V = ∑ M_i` and the arclength-density sum `B = ∑ M_i / L_i`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral CatalanLambda.Decay CatalanCore.Cert CatalanCore.Decay
  CatalanCore.Uniform.Decay.Tools

/-- Exact integral of a rational polynomial density. -/
theorem integral_ratPoly (l : List ℚ) :
    ∫ t in (0 : ℝ)..1, ratPoly l t
      = ((∑ j ∈ range (l.length - 1 + 1), coeffs l j / ((j : ℚ) + 1) : ℚ) : ℝ) := by
  unfold ratPoly
  rw [intervalIntegral.integral_finset_sum (fun i _ => by
    exact (continuous_const.mul (continuous_pow i)).intervalIntegrable _ _)]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

theorem exists_certCoreGs_poly {sl : ℝ} {α : ℚ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} {A B : Fin n → ℂ} {l : Fin n → List ℚ}
    (C : SplineCert sl α ε A B (fun i => ratPoly (l i)))
    (hAB : ∀ i, A i ≠ B i) (hne : ∀ i, l i ≠ []) {M : Fin n → ℚ}
    (hbern : ∀ i, bernOkK (l i) (-M i) (M i) = true) {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∑ i, ∑ j ∈ range ((l i).length - 1 + 1), coeffs (l i) j / ((j : ℚ) + 1) = 1)
    {Rc : ℝ} (hAR : ∀ i, ‖A i‖ ≤ Rc) (hBR : ∀ i, ‖B i‖ ≤ Rc)
    {τ : Fin n → Fin n} (hτ : Function.Involutive τ) (hAτ : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hBτ : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hlτ : ∀ i, l (τ i) = l i)
    {lossS : ℚ} (hlossS : Real.pi * ρ * Bs A B (fun i => (M i : ℝ)) ≤ lossS)
    {θ : ℚ} (hθ : 0 < θ) {ηS : ℚ} (hηS : 0 < ηS) :
    ∃ (K : ℕ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (F : CertCoreGs sl K ρ ε c wt),
      (∀ s, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|) ∧
      F.r0 = C.r0 ∧ F.W = C.W ∧ F.umax = C.umax ∧
      F.mprime = C.mprime - (1 + α) * (lossS + θ) ∧
      F.gmin = C.gmin - (1 + α) * (lossS + θ) ∧
      F.ccert = C.ccert ∧ F.Sbase = C.Scap - ηS ∧
      F.Ibound = C.Ibound + (∑ i, M i) * lossS + 2 * (∑ i, M i) * θ ∧
      (∑ k, |wt k| ≤ ∑ i, M i) ∧ (∀ k, ‖c k‖ ≤ Rc) := by
  have hf : ∀ i, Continuous ((fun i => ratPoly (l i)) i) := fun i => continuous_ratPoly (l i)
  have hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |(fun i => ratPoly (l i)) i t| ≤ (M i : ℝ) :=
    fun i t ht => ratPoly_abs_le (hne i) (hbern i) ht.1 ht.2
  have hmassR : ∑ i, ∫ t in (0 : ℝ)..1, (fun i => ratPoly (l i)) i t = 1 := by
    simp_rw [integral_ratPoly]
    rw [← Rat.cast_sum, hmass]
    norm_num
  have hV : Vp (fun i => ratPoly (l i)) ≤ ((∑ i, M i : ℚ) : ℝ) := by
    have := Vp_le_sum hf hM
    push_cast
    exact this
  have hτf : ∀ i, (fun i => ratPoly (l i)) (τ i) = (fun i => ratPoly (l i)) i := by
    intro i; simp [hlτ]
  have hαR : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα.le
  have hUc : ContinuousOn (fun x : ℝ => Unu α (x : ℂ)) (Set.Icc (-(C.r0 : ℝ)) 0) :=
    (continuousOn_Unu_real hαR).mono (fun x hx => hx.2)
  exact exists_certCoreGs hα hε0 hε1 C hAB hf hM hρ hmassR hV hAR hBR hτ hAτ hBτ hτf hUc
    hlossS hθ hηS

/-- The bridge for a general continuous (signed) density presentation, with the continuity of `Unu`
discharged. -/
theorem exists_certCoreGs_main {sl : ℝ} {α : ℚ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {n : ℕ} {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ} (C : SplineCert sl α ε A B f)
    (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∑ i, ∫ t in (0 : ℝ)..1, f i t = 1) {V : ℚ} (hV : Vp f ≤ V)
    {Rc : ℝ} (hAR : ∀ i, ‖A i‖ ≤ Rc) (hBR : ∀ i, ‖B i‖ ≤ Rc)
    {τ : Fin n → Fin n} (hτ : Function.Involutive τ) (hAτ : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hBτ : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hfτ : ∀ i, f (τ i) = f i)
    {lossS : ℚ} (hlossS : Real.pi * ρ * Bs A B M ≤ lossS) {θ : ℚ} (hθ : 0 < θ) {ηS : ℚ}
    (hηS : 0 < ηS) :
    ∃ (K : ℕ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (F : CertCoreGs sl K ρ ε c wt),
      (∀ s, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|) ∧
      F.r0 = C.r0 ∧ F.W = C.W ∧ F.umax = C.umax ∧
      F.mprime = C.mprime - (1 + α) * (lossS + θ) ∧
      F.gmin = C.gmin - (1 + α) * (lossS + θ) ∧
      F.ccert = C.ccert ∧ F.Sbase = C.Scap - ηS ∧
      F.Ibound = C.Ibound + V * lossS + 2 * V * θ ∧
      (∑ k, |wt k| ≤ V) ∧ (∀ k, ‖c k‖ ≤ Rc) := by
  have hαR : (0 : ℝ) ≤ (α : ℝ) := by exact_mod_cast hα.le
  have hUc : ContinuousOn (fun x : ℝ => Unu α (x : ℂ)) (Set.Icc (-(C.r0 : ℝ)) 0) :=
    (continuousOn_Unu_real hαR).mono (fun x hx => hx.2)
  exact exists_certCoreGs hα hε0 hε1 C hAB hf hM hρ hmass hV hAR hBR hτ hAτ hBτ hfτ hUc hlossS hθ hηS

end CatalanCore.Uniform.Decay.Spline
