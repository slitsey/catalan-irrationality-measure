module

public import CatalanCore.Uniform.Decay.Spline.PolyBridge
public import CatalanCore.Uniform.Decay.Spline.HybridHookS

@[expose] public section

/-!
# From a spline certificate to `HasDecay` (lane D, package D2)

`exists_hybridDecayDataS`: a `SplineCert` for a signed spline trial measure with exact mass one,
`|f_i| ≤ M_i`, conjugation symmetry, and a decay target
`D ≤ C.Dof - (losses)` produces atoms and a `CertCoreGs` `F` together with the signed hybrid decay
data `HybridDecayDataS F α Rc V Inu D dim` (`F.g` is the atomic hybrid function, `F.ccert = C.ccert`).
Then `HybridDecayDataS.hybridDecay` etc. give `HasDecay` for every frame `Fr` with
`Fr.DecayOKs' sl` and `Fr.d = dim`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset CatalanLambda.Decay CatalanCore.Cert CatalanCore.Decay CatalanCore.SignedChain

variable {n : ℕ}

/-- The decay exponent of the continuous certificate: same formula as `CertCoreGs.Dof`. -/
def SplineCert.Dof {sl : ℝ} {α : ℚ} {ε : ℝ} {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ}
    (C : SplineCert sl α ε A B f) (d : ℕ) (Inu : ℚ) : ℚ :=
  2 * ((1 + α) * C.mprime + d * C.Scap) - (1 + α) ^ 2 * C.Ibound + Inu

/-- The total exponent loss of the bridge: smoothing `lossS`, mesh `θ`, Darboux debit `ηS`. -/
def bridgeLoss (α : ℚ) (d : ℕ) (V lossS θ ηS : ℚ) : ℚ :=
  2 * (1 + α) ^ 2 * (lossS + θ) + 2 * d * ηS + (1 + α) ^ 2 * (V * lossS + 2 * V * θ)

theorem exists_hybridDecayDataS {sl : ℝ} {α : ℚ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ} (C : SplineCert sl α ε A B f)
    (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∑ i, ∫ t in (0 : ℝ)..1, f i t = 1) {V : ℚ} (hV : Vp f ≤ V)
    {Rc : ℝ} (hRc : 0 ≤ Rc) (hAR : ∀ i, ‖A i‖ ≤ Rc) (hBR : ∀ i, ‖B i‖ ≤ Rc)
    {τ : Fin n → Fin n} (hτ : Function.Involutive τ) (hAτ : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hBτ : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hfτ : ∀ i, f (τ i) = f i)
    {lossS : ℚ} (hlossS : Real.pi * ρ * Bs A B M ≤ lossS) {θ : ℚ} (hθ : 0 < θ) {ηS : ℚ}
    (hηS : 0 < ηS) {Inu : ℚ} (hInu : (Inu : ℝ) ≤ Jfun (α : ℝ)) (hcc : 0 ≤ (C.ccert : ℝ))
    (dim : ℕ) {D : ℚ} (hD : D ≤ C.Dof dim Inu - bridgeLoss α dim V lossS θ ηS) :
    ∃ (K : ℕ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (F : CertCoreGs sl K ρ ε c wt),
      HybridDecayDataS F α Rc V Inu D dim ∧ F.ccert = C.ccert := by
  obtain ⟨K, c, wt, F, hg, -, -, -, hm, hgm, hcc', hS, hI, hVb, hR⟩ :=
    exists_certCoreGs_main hα hε0 hε1 C hAB hf hM hρ hmass hV hAR hBR hτ hAτ hBτ hfτ hlossS hθ hηS
  have hDof : F.Dof dim α Inu = C.Dof dim Inu - bridgeLoss α dim V lossS θ ηS := by
    unfold CertCoreGs.Dof SplineCert.Dof bridgeLoss
    rw [hm, hS, hI]
    ring
  refine ⟨K, c, wt, F, ⟨hα, hg, hVb, hRc, hR, hInu, ?_, ?_⟩, hcc'⟩
  · rw [hDof]; exact hD
  · rw [hcc']; exact hcc

end CatalanCore.Uniform.Decay.Spline
