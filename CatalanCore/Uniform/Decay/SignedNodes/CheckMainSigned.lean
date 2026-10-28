module

public import CatalanCore.Uniform.Decay.SignedNodes.BasicSigned
public import CatalanCore.Uniform.Decay.SignedNodes.BridgeNuSigned
public import CatalanCore.Uniform.Decay.SignedNodes.AllMinorMainSigned

@[expose] public section

/-!
# `hasScaledDecay_of_check_signed`: the signed finite checker and its soundness (lane D, package D8)

`SplineDataS.check R D` is `SplineData.check R D` with `basicOkS` (signed elementary checks, total
variation `Vt`) in place of `basicOk`; the cell rules `R : CellRules Vnu` are reused unchanged
(they only concern the exact hybrid function `gNu`, which does not see the sign of the density).
`check_soundS` produces the `SplineCertNu` and `BasicFactsS`; `hasScaledDecay_of_check_signed`
runs the chain  `check_soundS` -> `exists_certCoreGsNu_signed` ->
`hasAllMinorDecay_of_certG_signed` (D3's `energy_geom_small_signed`) -> `mono` ->
`hasScaledDecay_of_allMinor`.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset intervalIntegral MeasureTheory CatalanCore CatalanCore.Uniform
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

namespace SplineDataS

/-- **The signed finite checker.** -/
def check {Vnu : ℂ → ℝ} (R : CellRules Vnu) (D : SplineDataS) : Bool :=
  D.basicOkS && D.rayBoxes.all (R.rayOk D.toSplineData) && D.lineCells.all (R.lineOk D.toSplineData) &&
    R.tailOk D.toSplineData && R.capOk D.toSplineData && R.energyOk D.toSplineData

/-- **Soundness of the signed checker**: `check = true` yields the bridge certificate. -/
theorem check_soundS {Vnu : ℂ → ℝ} {R : CellRules Vnu} {D : SplineDataS}
    (h : D.check R = true) :
    BasicFactsS D ∧ ∃ C : SplineCertNu (D.sl : ℝ) D.Mq Vnu (D.ε : ℝ) D.A D.B D.f,
      C.r0 = D.r0 ∧ C.W = D.W ∧ C.umax = D.umax ∧ C.mprime = D.mprime ∧ C.gmin = D.gmin ∧
      C.Scap = D.Scap ∧ C.Ibound = D.Ibound ∧ C.ccert = D.ccert := by
  simp only [check, Bool.and_assoc, Bool.and_eq_true] at h
  obtain ⟨hb, hray, hline, htail, hcap, hen⟩ := h
  have B := basicOkS_sound hb
  refine ⟨B, ?_⟩
  obtain ⟨hci, hcs⟩ := R.cap_sound D.toSplineData hcap
  refine ⟨SplineCertNu.mk D.r0 D.W D.umax D.mprime D.gmin D.Scap D.Ibound D.ccert B.r0_pos B.W_pos
    D.rayBoxes (fun p hp => R.ray_sound D.toSplineData p (List.all_eq_true.1 hray p hp)) B.hray
    (R.tail_sound D.toSplineData htail) D.lineCells
    (fun p hp => R.line_sound D.toSplineData p (List.all_eq_true.1 hline p hp)) B.hline hci hcs
    (R.energy_sound D.toSplineData hen) B.hccert, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end SplineDataS

/-- **From the signed finite checker to the window contract.**  Same statement as
`hasScaledDecay_of_check`; the trial density may be signed, the data carry a total-variation
bound `Vt` (`D.Vt = 1` with one-sided Bernstein certificates is the positive case), and the
decay exponent `D.Dt` is certified with the loss `Vt · (…)`. -/
theorem hasScaledDecay_of_check_signed (G : BlockGeom) {sl : ℝ} {Fr : Frame}
    (hFr : Fr.DecayOKs' sl) (R : CellRules G.nodePot) (D : SplineDataS)
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
  obtain ⟨B, C, hCr0, hCW, hCum, hCm, hCg, hCS, hCI, hCc⟩ := SplineDataS.check_soundS hchk
  have hne := B.hne
  have hf : ∀ i, Continuous (D.f i) := fun i => continuous_ratPoly (D.l i)
  have hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |D.f i t| ≤ ((fun i => (D.M i : ℝ)) i) := by
    intro i t ht
    have := ratPoly_bounds (hne i) (B.hbern i) ht.1 ht.2
    rw [abs_le]
    unfold SplineData.f
    constructor
    · have h1 := this.1; push_cast at h1; linarith
    · exact this.2
  have hmass : ∑ i, ∫ t in (0 : ℝ)..1, D.f i t = 1 := SplineDataS.mass_real_of_rat B.hmass
  have hV : Vp D.f ≤ ((D.Vt : ℚ) : ℝ) := B.hvar
  have hτf : ∀ i, D.f (D.tauF i) = D.f i := by
    intro i; simp [SplineData.f, B.hlτ i]
  have hMq0 : 0 ≤ D.Mq := B.hM.le
  have hρ : (0 : ℝ) < D.rho := B.hρ
  obtain ⟨K, c, wt, F, hg, hFr0, hFW, hFum, hFmp, hFgm, hFcc, hFS, hFI, hVb, hR⟩ :=
    exists_certCoreGsNu_signed (sl := (D.sl : ℝ)) hMq0 hVc B.hε0 B.hε1 C B.hAB hf hM hρ hmass hV
      B.hAR B.hBR B.hτ B.hAτ B.hBτ hτf (by rw [hCr0]; exact hUc) B.hloss B.hθ B.hηS
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
  have hall := hasAllMinorDecay_of_certG_signed G hFr F hVb hR hg' hBd0 hBc hBr hBq hm0 hm0xs hm0μ
    he0 heε hℓ hcB
  have hccR : (F.ccert : ℝ) = D.ccert := by rw [hFcc, hCc]
  have hcc0 : (0 : ℝ) ≤ D.ccert := by exact_mod_cast B.hcc
  -- the decay exponent
  have hmpR : (F.mprime : ℝ) = D.mprime - D.Mq * (D.lossS + D.theta) := by
    rw [hFmp, hCm]; push_cast; ring
  have hSR : (F.Sbase : ℝ) = D.Scap - D.etaS := by rw [hFS, hCS]; push_cast; ring
  have hIR : (F.Ibound : ℝ) = D.Ibound + D.Vt * D.lossS + 2 * D.Vt * D.theta := by
    rw [hFI, hCI]; push_cast; ring
  have hDle : (D.Dt : ℝ) ≤ 2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
      - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy := by
    have hD := B.hD
    have hDR : (D.Dt : ℝ) ≤ 2 * ((D.Mq : ℝ) * D.mprime + D.dim * D.Scap) - (D.Mq : ℝ) ^ 2 * D.Ibound
        + D.Inu - (2 * (D.Mq : ℝ) ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
          + (D.Mq : ℝ) ^ 2 * (D.Vt * D.lossS + 2 * D.Vt * D.theta)) := by exact_mod_cast hD
    have hMR : (D.Mq : ℝ) = G.totalMass := by rw [hMq]
    have hdR : (D.dim : ℝ) = Fr.d := by exact_mod_cast hd
    rw [hmpR, hSR, hIR, ← hMR, ← hdR]
    nlinarith [hDR, hInu]
  have hmono := NodeFamily.HasAllMinorDecay.mono (by rw [hccR]; exact hcc0) hDle
    (le_of_eq hccR) hall
  exact G.hasScaledDecay_of_allMinor Fr depth hcc0 hmono

end CatalanCore.Uniform.Decay.Cert
