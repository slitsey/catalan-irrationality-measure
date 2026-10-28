module

public import CatalanCore.Uniform.Decay.SignedNodes.AllMinorMainSigned

@[expose] public section

/-!
# The positive case `V = 1` of the signed theorems (lane D, package D8)

For nonnegative weights `∑ |wt| = ∑ wt = 1`, so the signed theorems apply with `V = 1`: the
positive `energy_geom_small` and `hasAllMinorDecay_of_certG` are recovered with the same
statements.
-/

namespace CatalanCore.Uniform

theorem sum_abs_eq_one_of_nonneg {K : ℕ} {wt : Fin K → ℝ} (hw0 : ∀ k, 0 ≤ wt k)
    (hm : ∑ k, wt k = 1) : ∑ k, |wt k| ≤ 1 := by
  refine le_of_eq ?_
  rw [← hm]
  exact Finset.sum_congr rfl (fun k _ => abs_of_nonneg (hw0 k))

end CatalanCore.Uniform

namespace CatalanCore.Uniform.Decay.Cert

open CatalanCore.Uniform CatalanLambda.Decay

/-- The positive `hasAllMinorDecay_of_certG` is the case `V = 1` of the signed theorem. -/
theorem hasAllMinorDecay_of_certG_of_signed (G : BlockGeom) {sl : ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl)
    {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : Cert.CertCoreGs sl K ρ ε c wt) (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ Rc)
    (hg : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < ε) {ℓ cB : ℝ}
    (hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → ℓ ≤ F.g ((a : ℂ) / (r : ℂ)))
    (hcB : 2 * ((F.mprime : ℝ) - ℓ) ≤ cB) :
    NodeFamily.HasAllMinorDecay G.geometry Fr
      (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy) cB :=
  hasAllMinorDecay_of_certG_signed G hFr F (sum_abs_eq_one_of_nonneg hw0 F.hm) hc hg hBd0 hBc hBr
    hBq hm0 hm0xs hm0μ he0 heε hℓ hcB

end CatalanCore.Uniform.Decay.Cert
