module

public import CatalanCore.Uniform.Decay.Cert.BridgeNu
public import CatalanCore.Uniform.Decay.PolyChain.CertP

@[expose] public section

/-!
# The spline-to-atomic bridge over a polygon (lane D, package D7)

`SplineCertNuP P M Vnu ε A B f` is D5's `SplineCertNu` with the straight-ray fields
(`rayBoxes`, `ray_box_ok`, `ray_cover`, `ray_tail`, `umax`, slope) replaced by the tube field over
the normalised polygon `normSet P`, and the base `r0 := P.r0`.  `exists_certCoreGsNuP` is a copy
of `Cert.exists_certCoreGsNu` producing the polygon interface `CertCoreP`; only the tube field
is new (`g ≥ gNu - M(lossS + θ)` pointwise, as for the ray boxes).
-/

namespace CatalanCore.Uniform.Decay.PolyChain

open Finset intervalIntegral MeasureTheory CatalanLambda.Decay CatalanCore.Cert CatalanCore.Decay
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon

variable {n : ℕ}

/-- The finite-check certificate for the continuous spline trial measure over a polygon. -/
structure SplineCertNuP (P : RatPolygon) (M : ℚ) (Vnu : ℂ → ℝ) (ε : ℝ) (A B : Fin n → ℂ)
    (f : Fin n → ℝ → ℝ) where
  W : ℚ
  mprime : ℚ
  gmin : ℚ
  Scap : ℚ
  Ibound : ℚ
  ccert : ℚ
  W_pos : 0 < W
  tube_ok : ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ W → (mprime : ℝ) ≤ gNu M Vnu ε A B f (w + δ)
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ gNu M Vnu ε A B f ⟨x, 0⟩
  line_cover : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  cap_int : IntervalIntegrable (fun x : ℝ => min (gNu M Vnu ε A B f ⟨x, 0⟩ - mprime) 0) volume
    (-(P.r0 : ℝ)) 0
  cap_ok : (Scap : ℝ) ≤ ∫ x in (-(P.r0 : ℝ))..0, min (gNu M Vnu ε A B f ⟨x, 0⟩ - mprime) 0
  I_ok : I0 A B f ≤ Ibound
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

/-- **The spline-to-atomic bridge.** -/
theorem exists_certCoreGsNuP {P : RatPolygon} (hP0 : 0 < P.r0) {M : ℚ} (hM0 : 0 ≤ M) {Vnu : ℂ → ℝ}
    (hVc : ∀ s, Vnu ((starRingEnd ℂ) s) = Vnu s) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ} (C : SplineCertNuP P M Vnu ε A B f)
    (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {Mb : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ Mb i) {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∑ i, ∫ t in (0 : ℝ)..1, f i t = 1) {V : ℚ} (hV : Vp f ≤ V)
    {Rc : ℝ} (hAR : ∀ i, ‖A i‖ ≤ Rc) (hBR : ∀ i, ‖B i‖ ≤ Rc)
    {τ : Fin n → Fin n} (hτ : Function.Involutive τ) (hAτ : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hBτ : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hfτ : ∀ i, f (τ i) = f i)
    (hUc : ContinuousOn (fun x : ℝ => Vnu (x : ℂ)) (Set.Icc (-(P.r0 : ℝ)) 0))
    (hf0 : ∀ i t, 0 ≤ t → t ≤ 1 → 0 ≤ f i t)
    {lossS : ℚ} (hlossS : Real.pi * ρ * Bs A B Mb ≤ lossS) {θ : ℚ} (hθ : 0 < θ) {ηS : ℚ} (hηS : 0 < ηS) :
    ∃ (K : ℕ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (F : CertCoreP P K ρ ε c wt),
      (∀ s, F.g s = (M : ℝ) * Usig ρ c wt s - Vnu s + (1 - ε) * Real.pi * |s.im|) ∧
      F.W = C.W ∧
      F.mprime = C.mprime - M * (lossS + θ) ∧
      F.gmin = C.gmin - M * (lossS + θ) ∧
      F.ccert = C.ccert ∧ F.Sbase = C.Scap - ηS ∧
      F.Ibound = C.Ibound + V * lossS + 2 * V * θ ∧
      (∑ k, |wt k| ≤ V) ∧ (∀ k, ‖c k‖ ≤ Rc) ∧ (∀ k, 0 ≤ wt k) := by
  classical
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  obtain ⟨N, hN, hetaN⟩ := exists_N_etaN_le A B f hρ hθR
  have hM0R : (0 : ℝ) ≤ M := by exact_mod_cast hM0
  have hVp0 := Vp_nonneg f
  have hBs0 : 0 ≤ Real.pi * ρ * Bs A B Mb := by
    have hMn : ∀ i, 0 ≤ Mb i := fun i => (abs_nonneg _).trans (hM i 0 ⟨le_rfl, zero_le_one⟩)
    have : 0 ≤ Bs A B Mb := Finset.sum_nonneg (fun i _ => div_nonneg (hMn i) (norm_nonneg _))
    positivity
  -- loss in the potential
  set ℓ : ℝ := (lossS : ℝ) + θ with hℓ
  have hUerr : ∀ z, |Usig ρ (cK A B N) (wK f N) z - U0 A B f z| ≤ ℓ := by
    intro z
    have h1 := usig_atom_err (A := A) (B := B) hf hρ hN z
    have h2 := smooth_err hAB hf hM hρ z
    have := abs_sub_le (Usig ρ (cK A B N) (wK f N) z) (Urho A B f ρ z) (U0 A B f z)
    rw [abs_sub_comm (Urho A B f ρ z)] at this
    rw [hℓ]; linarith
  set c := cK A B N with hc
  set wt := wK f N with hwt
  have hg : ∀ s : ℂ, |(M : ℝ) * Usig ρ c wt s - Vnu s + (1 - ε) * Real.pi * |s.im|
      - gNu M Vnu ε A B f s| ≤ (M : ℝ) * ℓ := by
    intro s
    unfold gNu
    have e : (M : ℝ) * Usig ρ c wt s - Vnu s + (1 - ε) * Real.pi * |s.im|
        - ((M : ℝ) * U0 A B f s - Vnu s + (1 - ε) * Real.pi * |s.im|)
        = (M : ℝ) * (Usig ρ c wt s - U0 A B f s) := by ring
    rw [e, abs_mul, abs_of_nonneg hM0R]
    exact mul_le_mul_of_nonneg_left (hUerr s) hM0R
  have hgl : ∀ s : ℂ, gNu M Vnu ε A B f s - (M : ℝ) * ℓ
      ≤ (M : ℝ) * Usig ρ c wt s - Vnu s + (1 - ε) * Real.pi * |s.im| := by
    intro s; have := (abs_le.1 (hg s)).1; linarith
  -- mass, variation, radius
  have hm1 : ∑ k, wt k = 1 := by rw [hwt, sum_wK f hf hN, hmass]
  have hVb : ∑ k, |wt k| ≤ V := (abs_sum_wK_le f hf hN).trans hV
  have hR : ∀ k, ‖c k‖ ≤ Rc := fun k => norm_cK_le A B hAR hBR hN k
  have hw0 : ∀ k, 0 ≤ wt k := by
    intro k
    show 0 ≤ wAt f N (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    unfold wAt
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    set j := (finProdFinEquiv.symm k).2 with hj
    have hj1 : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
    have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
    refine intervalIntegral.integral_nonneg (by gcongr; linarith) (fun u hu => hf0 _ u ?_ ?_)
    · exact le_trans (by positivity) hu.1
    · exact hu.2.trans ((div_le_one hN').2 hj1)
  -- conjugation symmetry
  obtain ⟨σ, hσ, hσc, hσw⟩ := atoms_conj_symm A B f τ hτ hAτ hBτ hfτ N
  -- the atomic function on the real axis
  set G : ℝ → ℝ := fun x => (M : ℝ) * Usig ρ c wt (x : ℂ) - Vnu (x : ℂ) + (1 - ε) * Real.pi * |(x : ℂ).im| with hG
  have hGc : ContinuousOn G (Set.Icc (-(P.r0 : ℝ)) 0) := by
    have h1 : Continuous (fun x : ℝ => (M : ℝ) * Usig ρ c wt (x : ℂ)) :=
      continuous_const.mul ((continuous_Usig_left hρ c wt).comp Complex.continuous_ofReal)
    have h2 : (fun x : ℝ => (1 - ε) * Real.pi * |(x : ℂ).im|) = fun _ => 0 := by
      funext x; simp
    refine ((h1.continuousOn.sub hUc).add ?_)
    rw [h2]; exact continuousOn_const
  set mp : ℝ := (C.mprime : ℝ) - (M : ℝ) * ℓ with hmp
  have hGge : ∀ x : ℝ, gNu M Vnu ε A B f ⟨x, 0⟩ - (M : ℝ) * ℓ ≤ G x := by
    intro x; exact hgl (x : ℂ)
  have hS : (C.Scap : ℝ) ≤ ∫ x in (-(P.r0 : ℝ))..0, min (G x - mp) 0 := by
    refine C.cap_ok.trans ?_
    have hle : -(P.r0 : ℝ) ≤ 0 := by
      have : (0 : ℝ) < P.r0 := by exact_mod_cast hP0
      linarith
    refine intervalIntegral.integral_mono_on hle C.cap_int ?_ (fun x _ => ?_)
    · exact (continuous_min.comp_continuousOn ((hGc.sub continuousOn_const).prodMk
        continuousOn_const)).intervalIntegrable_of_Icc hle
    · apply min_le_min _ le_rfl
      have := hGge x
      rw [hmp]; linarith
  obtain ⟨nSeg, segA, segB, segG, hab, hok, hcov, hsum⟩ :=
    exists_seg_cover hP0 hGc mp (C.Scap : ℝ) hS (η := (ηS : ℝ)) (by exact_mod_cast hηS)
  -- assemble
  have hmpq : (((C.mprime - M * (lossS + θ) : ℚ)) : ℝ) = mp := by
    rw [hmp, hℓ]; push_cast; ring
  have hgminq : (((C.gmin - M * (lossS + θ) : ℚ)) : ℝ) = (C.gmin : ℝ) - (M : ℝ) * ℓ := by
    rw [hℓ]; push_cast; ring
  have hIq : (((C.Ibound + V * lossS + 2 * V * θ : ℚ)) : ℝ)
      = (C.Ibound : ℝ) + (V : ℝ) * lossS + 2 * (V : ℝ) * θ := by push_cast; ring
  have hVR : Vp f ≤ (V : ℝ) := hV
  have hlossR : Real.pi * ρ * Bs A B Mb ≤ (lossS : ℝ) := hlossS
  have hIbd : Irho ρ c wt ≤ (C.Ibound : ℝ) + (V : ℝ) * lossS + 2 * (V : ℝ) * θ := by
    have e1 := energy_atom_err (A := A) (B := B) hf hρ hN
    have e2 := energy_smooth_err hAB hf hM hρ
    have e3 := C.I_ok
    have e4 : Vp f * (Real.pi * ρ * Bs A B Mb) ≤ (V : ℝ) * lossS :=
      mul_le_mul hVR hlossR hBs0 ((hVp0.trans hVR))
    have e5 : 2 * Vp f * etaN A B f ρ N ≤ 2 * (V : ℝ) * θ :=
      mul_le_mul (by linarith) hetaN (etaN_nonneg A B f hρ N) (by have := hVp0.trans hVR; linarith)
    have e6 := (abs_le.1 e1).2
    have e7 := (abs_le.1 e2).1
    linarith
  let F : CertCoreP P (n * N) ρ ε c wt :=
    { g := fun s => (M : ℝ) * Usig ρ c wt s - Vnu s + (1 - ε) * Real.pi * |s.im|
      W := C.W
      mprime := C.mprime - M * (lossS + θ)
      gmin := C.gmin - M * (lossS + θ)
      Sbase := C.Scap - ηS
      Ibound := C.Ibound + V * lossS + 2 * V * θ
      ccert := C.ccert
      W_pos := C.W_pos
      hρ := hρ
      hε0 := hε0
      hε1 := hε1
      hm := hm1
      g_conj := by
        intro s
        have h1 := Usig_conj_of_involution ρ c wt σ hσ hσc hσw s
        simp only [h1, hVc, Complex.conj_im, abs_neg]
      tube_ok := by
        intro w hw δ hδ
        have := C.tube_ok w hw δ hδ
        have h5 := hgl (w + (δ : ℂ))
        rw [hmpq, hmp]
        show _ ≤ (M : ℝ) * Usig ρ c wt (w + (δ : ℂ)) - Vnu (w + (δ : ℂ))
          + (1 - ε) * Real.pi * |(w + (δ : ℂ)).im|
        linarith
      nSeg := nSeg
      segA := segA
      segB := segB
      segG := segG
      seg_ab := hab
      seg_ok := fun i x h1 h2 => hok i x h1 h2
      seg_cover := hcov
      Sbase_le := by
        rw [hmpq]
        push_cast
        have := hsum
        simpa [hmp] using this
      lineCells := C.lineCells
      line_ok := by
        intro p hp x h1 h2
        have := C.line_ok p hp x h1 h2
        have h5 := hgl ⟨x, 0⟩
        rw [hgminq]
        show _ ≤ (M : ℝ) * Usig ρ c wt ⟨x, 0⟩ - Vnu ⟨x, 0⟩ + (1 - ε) * Real.pi * |(⟨x, 0⟩ : ℂ).im|
        linarith
      line_cover := C.line_cover
      I_ok := by rw [hIq]; exact hIbd
      ccert_ge := by
        rw [hmpq, hgminq, hmp]
        have := C.ccert_ge
        linarith }
  exact ⟨n * N, c, wt, F, fun s => rfl, rfl, rfl, rfl, rfl, rfl, rfl, hVb, hR, hw0⟩

end CatalanCore.Uniform.Decay.PolyChain
