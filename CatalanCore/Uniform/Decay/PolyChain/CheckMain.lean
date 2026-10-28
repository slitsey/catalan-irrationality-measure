module

public import CatalanCore.Uniform.Decay.PolyChain.Check
public import CatalanCore.Uniform.Decay.PolyChain.AllMinor
public import CatalanCore.Uniform.Decay.Cert.CheckMain

@[expose] public section

/-!
# `hasScaledDecay_of_check_poly`: from the polygon checker to the window contract (D7)

Polygon analogue of D5's `Cert.hasScaledDecay_of_check`, with the same proof:
`checkP R D P = true` gives `BasicFacts`, `P.OK` and `SplineCertNuP` (`checkP_sound`), then a
`CertCoreP` of atomic midpoint atoms (`exists_certCoreGsNuP`), then `HasAllMinorDecay`
(`hasAllMinorDecay_of_certG_poly`: D3's energy estimate with the distance hypothesis, the
polygon Lemma B, `theoremN_poly` over D5a's `polygonRep_scaled`), then `HasScaledDecay` of the
block family (`HasAllMinorDecay.mono`, `BlockGeom.hasScaledDecay_of_allMinor`).

Frame hypotheses: `ContourOK`, head range `hAR`, `norm ≥ 1`.  No slope hypothesis and no
`m0 ≤ xs` (polygon points are separated from the nodes by `node_dist`).
-/

namespace CatalanCore.Uniform.Decay.PolyChain

open Finset intervalIntegral MeasureTheory CatalanCore CatalanCore.Uniform
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Polygon

/-- **From the polygon checker to the window contract.** -/
theorem hasScaledDecay_of_check_poly (G : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (R : PolyCellRules G.nodePot) (D : SplineData) (P : RatPolygon)
    (hchk : D.checkP R P = true) (hMq : D.Mq = G.totalMass)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G.nodeEnergy)
    (hVc : ∀ s, G.nodePot ((starRingEnd ℂ) s) = G.nodePot s)
    (hUc : ContinuousOn (fun x : ℝ => G.nodePot (x : ℂ)) (Set.Icc (-(P.r0 : ℝ)) 0))
    (hsupp : ∀ r a : ℕ, a ∈ (G.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G.family Fr depth) G.scale (D.Dt : ℝ) (D.ccert : ℝ) := by
  classical
  obtain ⟨B, hP, _, C, hCW, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.checkP_sound hchk
  have hne := B.hne
  have hbd : ∀ i, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (0 : ℝ) ≤ D.f i t ∧ D.f i t ≤ (D.M i : ℝ) := by
    intro i t h0 h1
    have := ratPoly_bounds (hne i) (B.hbern i) h0 h1
    unfold SplineData.f
    simpa using this
  have hf : ∀ i, Continuous (D.f i) := fun i => continuous_ratPoly (D.l i)
  have hf0 : ∀ i t, 0 ≤ t → t ≤ 1 → 0 ≤ D.f i t := fun i t h0 h1 => (hbd i t h0 h1).1
  have hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |D.f i t| ≤ ((fun i => (D.M i : ℝ)) i) := by
    intro i t ht
    have := hbd i t ht.1 ht.2
    rw [abs_of_nonneg this.1]; exact this.2
  have hmass : ∑ i, ∫ t in (0 : ℝ)..1, D.f i t = 1 := by
    have := B.hmass
    simp_rw [SplineData.f, integral_ratPoly]
    rw [← Rat.cast_sum]
    have h2 : (∑ i : Fin D.n, ∑ j ∈ range ((D.l i).length - 1 + 1),
        coeffs (D.l i) j / ((j : ℚ) + 1)) = 1 := this
    rw [h2]; norm_num
  have hV : Vp D.f ≤ ((1 : ℚ) : ℝ) := by
    have h1 : Vp D.f = ∑ i, ∫ t in (0 : ℝ)..1, D.f i t := by
      unfold Vp
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le zero_le_one] using ht
      exact abs_of_nonneg (hf0 i t ht'.1 ht'.2)
    rw [h1, hmass]; norm_num
  have hτf : ∀ i, D.f (D.tauF i) = D.f i := by
    intro i; simp [SplineData.f, B.hlτ i]
  have hMq0 : 0 ≤ D.Mq := B.hM.le
  have hρ : (0 : ℝ) < D.rho := B.hρ
  obtain ⟨K, c, wt, F, hg, hFW, hFmp, hFgm, hFcc, hFS, hFI, hVb, hR, hw0⟩ :=
    exists_certCoreGsNuP hP.r0_pos hMq0 hVc B.hε0 B.hε1 C B.hAB hf hM hρ hmass hV
      B.hAR B.hBR B.hτ B.hAτ B.hBτ hτf hUc hf0 B.hloss B.hθ B.hηS
  -- bring to the form of `hasAllMinorDecay_of_certG`
  have hg' : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * CatalanLambda.Decay.Usig D.rho c wt s -
      G.nodePot s + (1 - (D.ε : ℝ)) * Real.pi * |s.im| := by
    intro s; rw [hg s, hMq]
  have hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → (F.gmin : ℝ) ≤ F.g ((a : ℂ) / (r : ℂ)) := by
    intro r a ha
    have hx0 : (0 : ℝ) ≤ (a : ℝ) / r := by positivity
    have hx1 : (a : ℝ) / r ≤ 1 := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp
      · rw [div_le_one (by exact_mod_cast h0)]; exact hsupp r a ha
    obtain ⟨p, hp, h1, h2⟩ := F.line_cover _ hx0 hx1
    have := F.line_ok p hp _ h1 h2
    have e : ((a : ℂ) / (r : ℂ)) = ⟨(a : ℝ) / r, 0⟩ := by
      have h3 : ((a : ℂ) / (r : ℂ)) = (((a : ℝ) / r : ℝ) : ℂ) := by push_cast; rfl
      rw [h3]; apply Complex.ext <;> simp
    rw [e]; exact this
  have hcB : 2 * ((F.mprime : ℝ) - F.gmin) ≤ (F.ccert : ℝ) := by
    have h1 := F.ccert_ge
    exact h1
  have hall := hasAllMinorDecay_of_certG_poly G hC hAR hnorm1 hP F hw0 hR hg' hBd0 hBc hBr hBq
    hm0 hm0μ he0 heε hℓ hcB
  have hccR : (F.ccert : ℝ) = D.ccert := by rw [hFcc, hCc]
  have hcc0 : (0 : ℝ) ≤ D.ccert := by exact_mod_cast B.hcc
  -- the decay exponent
  have hmpR : (F.mprime : ℝ) = D.mprime - D.Mq * (D.lossS + D.theta) := by
    rw [hFmp, hCm]; push_cast; ring
  have hSR : (F.Sbase : ℝ) = D.Scap - D.etaS := by rw [hFS, hCS]; push_cast; ring
  have hIR : (F.Ibound : ℝ) = D.Ibound + 1 * D.lossS + 2 * 1 * D.theta := by
    rw [hFI, hCI]; push_cast; ring
  have hDle : (D.Dt : ℝ) ≤ 2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
      - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy := by
    have hD := B.hD
    simp only [SplineData.V] at hD
    have hDR : (D.Dt : ℝ) ≤ 2 * ((D.Mq : ℝ) * D.mprime + D.dim * D.Scap) - (D.Mq : ℝ) ^ 2 * D.Ibound
        + D.Inu - (2 * (D.Mq : ℝ) ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
          + (D.Mq : ℝ) ^ 2 * (1 * D.lossS + 2 * 1 * D.theta)) := by exact_mod_cast hD
    have hMR : (D.Mq : ℝ) = G.totalMass := by rw [hMq]
    have hdR : (D.dim : ℝ) = Fr.d := by exact_mod_cast hd
    rw [hmpR, hSR, hIR, ← hMR, ← hdR]
    nlinarith [hDR, hInu]
  have hmono := NodeFamily.HasAllMinorDecay.mono (by rw [hccR]; exact hcc0) hDle
    (le_of_eq hccR) hall
  exact G.hasScaledDecay_of_allMinor Fr depth hcc0 hmono

end CatalanCore.Uniform.Decay.PolyChain
