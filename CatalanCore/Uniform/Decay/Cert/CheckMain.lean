module

public import CatalanCore.Uniform.Decay.Cert.Check
public import CatalanCore.Uniform.Decay.Cert.AllMinorMain

@[expose] public section

/-!
# `hasScaledDecay_of_check`: from the finite checker to the window contract (lane D, package D5)

`check R D = true` (cell rules `R` for the second potential `G.nodePot`) gives, for the block
geometry `G` with `D.Mq = G.totalMass`:

1. `SplineCertNu` (`check_sound`), 2. a `CertCoreGs` `F` of atomic midpoint atoms
(`exists_certCoreGsNu`), 3. `HasAllMinorDecay` (`hasAllMinorDecay_of_certG`, D3's
`energy_geom_small` through `Frame.theoremN_rect`), 4. `HasScaledDecay` of the block family
(`BlockGeom.hasScaledDecay_of_allMinor`, D3).

Frame and node-geometry hypotheses (`DecayOKs'`, `Inu ≤ J_node`, node support in `[0,1]`,
continuity/symmetry of `nodePot`, block bounds, `m0`, `e`) are explicit hypotheses for the banks.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset intervalIntegral MeasureTheory CatalanCore CatalanCore.Uniform
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

/-- Lower and upper Bernstein bounds of a rational polynomial density. -/
theorem ratPoly_bounds {l : List ℚ} (hne : l ≠ []) {lo hi : ℚ} (h : bernOkK l lo hi = true)
    {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : (lo : ℝ) ≤ ratPoly l t ∧ ratPoly l t ≤ (hi : ℝ) := by
  unfold bernOkK at h
  rw [List.all_eq_true] at h
  have hpos : 0 < l.length := List.length_pos_iff.mpr hne
  have hl : ∀ k ≤ l.length - 1, lo ≤ bern (coeffs l) (l.length - 1) k ∧
      bern (coeffs l) (l.length - 1) k ≤ hi := by
    intro k hk
    have := h k (List.mem_range.mpr (by omega))
    simp only [Bool.and_eq_true, decide_eq_true_eq, bernK_eq] at this
    exact this
  exact bernstein_range (K := ℝ) (fun i => ((coeffs l i : ℚ) : ℝ)) (l.length - 1)
    (lo := (lo : ℝ)) (hi := (hi : ℝ))
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).1)
    (fun k hk => by rw [bern_cast]; exact_mod_cast (hl k hk).2) h0 h1

/-- **From the checker to the window contract.** -/
theorem hasScaledDecay_of_check (G : BlockGeom) {sl : ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (R : CellRules G.nodePot) (D : SplineData)
    (hchk : D.check R = true) (hMq : D.Mq = G.totalMass) (hsl : (D.sl : ℝ) = sl)
    (hd : D.dim = Fr.d) (hInu : (D.Inu : ℝ) ≤ G.nodeEnergy)
    (hVc : ∀ s, G.nodePot ((starRingEnd ℂ) s) = G.nodePot s)
    (hUc : ContinuousOn (fun x : ℝ => G.nodePot (x : ℂ)) (Set.Icc (-(D.r0 : ℝ)) 0))
    (hsupp : ∀ r a : ℕ, a ∈ (G.geometry r).C → (a : ℝ) ≤ r)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < (D.ε : ℝ)) (depth : ℕ) :
    HasScaledDecay (G.family Fr depth) G.scale (D.Dt : ℝ) (D.ccert : ℝ) := by
  classical
  obtain ⟨B, C, hCr0, hCW, hCum, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.check_sound hchk
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
  obtain ⟨K, c, wt, F, hg, hFr0, hFW, hFum, hFmp, hFgm, hFcc, hFS, hFI, hVb, hR, hw0⟩ :=
    exists_certCoreGsNu (sl := (D.sl : ℝ)) hMq0 hVc B.hε0 B.hε1 C B.hAB hf hM hρ hmass hV
      B.hAR B.hBR B.hτ B.hAτ B.hBτ hτf (by rw [hCr0]; exact hUc) hf0 B.hloss B.hθ B.hηS
  -- bring to the form of `hasAllMinorDecay_of_certG`
  have hg' : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * CatalanLambda.Decay.Usig D.rho c wt s -
      G.nodePot s + (1 - (D.ε : ℝ)) * Real.pi * |s.im| := by
    intro s; rw [hg s, hMq]
  have hFsl : (D.sl : ℝ) = sl := hsl
  subst hFsl
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
  have hall := hasAllMinorDecay_of_certG G hFr F hw0 hR hg' hBd0 hBc hBr hBq hm0 hm0xs hm0μ
    he0 heε hℓ hcB
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

end CatalanCore.Uniform.Decay.Cert
