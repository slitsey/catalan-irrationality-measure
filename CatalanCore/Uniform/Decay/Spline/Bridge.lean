module

public import CatalanCore.Uniform.Decay.Spline.Errors
public import CatalanCore.Uniform.Decay.Spline.Darboux
public import CatalanCore.Decay.Rect.CertG
public import CatalanCore.Decay.Rect.Energy2

@[expose] public section

/-!
# The spline-to-atomic bridge: `SplineCert` ⟹ `CertCoreGs` (lane D, package D2)

`SplineCert` is the finite-check certificate for the *continuous* signed spline trial measure
`σ = (A_i, B_i, f_i)`: the same fields as `CertCoreGs`, stated for the exact hybrid function

  `gSpline = (1+α) U_σ - Unu α + (1-ε) π |Im|`,

with the cap integral bound `Scap ≤ ∫ min(g - m', 0)` and the exact energy bound `I(σ) ≤ Ibound`.

`exists_certCoreGs` produces, for every mesh tolerance `θ > 0` and Darboux debit `ηS > 0`, a finite
atomic measure `(c, wt)` (midpoint atoms, signed weights, exact mass one, conjugation symmetric) and a
`CertCoreGs` for it with the losses

* `m' = m'_σ - (1+α)(lossS + θ)`, `g_min = g_min,σ - (1+α)(lossS + θ)`  (`c`-certificate unchanged),
* `Sbase = Scap - ηS`,
* `Ibound = I_σ + V lossS + 2 V θ`,

where `lossS ≥ π ρ B` is the smoothing loss.  Then `energy_rectWS` applies to `F`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral MeasureTheory CatalanLambda.Decay CatalanCore.Cert CatalanCore.Decay

variable {n : ℕ}

/-- The exact hybrid function of the continuous spline trial measure. -/
noncomputable def gSpline (α : ℚ) (ε : ℝ) (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) (s : ℂ) : ℝ :=
  (1 + (α : ℝ)) * U0 A B f s - Unu α s + (1 - ε) * Real.pi * |s.im|

/-- The finite-check certificate for the continuous spline trial measure. -/
structure SplineCert (sl : ℝ) (α : ℚ) (ε : ℝ) (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) where
  r0 : ℚ
  W : ℚ
  umax : ℚ
  mprime : ℚ
  gmin : ℚ
  Scap : ℚ
  Ibound : ℚ
  ccert : ℚ
  r0_pos : 0 < r0
  W_pos : 0 < W
  rayBoxes : List (ℚ × ℚ)
  ray_box_ok : ∀ p ∈ rayBoxes, ∀ x y : ℝ, -(r0 : ℝ) - p.2 - W ≤ x → x ≤ -(r0 : ℝ) - p.1 + W →
    sl * (p.1 : ℝ) ≤ y → y ≤ sl * (p.2 : ℝ) → (mprime : ℝ) ≤ gSpline α ε A B f ⟨x, y⟩
  ray_cover : ∀ u : ℝ, 0 ≤ u → u ≤ umax → ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  ray_tail : ∀ u δ : ℝ, (umax : ℝ) ≤ u → |δ| ≤ W →
    (mprime : ℝ) ≤ gSpline α ε A B f ⟨-(r0 : ℝ) + δ - u, sl * u⟩
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ gSpline α ε A B f ⟨x, 0⟩
  line_cover : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  cap_int : IntervalIntegrable (fun x : ℝ => min (gSpline α ε A B f ⟨x, 0⟩ - mprime) 0) volume
    (-(r0 : ℝ)) 0
  cap_ok : (Scap : ℝ) ≤ ∫ x in (-(r0 : ℝ))..0, min (gSpline α ε A B f ⟨x, 0⟩ - mprime) 0
  I_ok : I0 A B f ≤ Ibound
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

/-! ### Conjugation symmetry of `Unu` -/

theorem Utau_conj' (s : ℂ) : Utau ((starRingEnd ℂ) s) = Utau s := by
  unfold Utau
  congr 1
  funext t
  have : (starRingEnd ℂ) s - (t : ℂ) = (starRingEnd ℂ) (s - (t : ℂ)) := by simp
  rw [this, Complex.norm_conj]

theorem Uex_conj' (L : ℝ) (s : ℂ) : Uex L ((starRingEnd ℂ) s) = Uex L s := by
  unfold Uex
  congr 1
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  unfold elog
  have : (starRingEnd ℂ) s - (u : ℂ) = (starRingEnd ℂ) (s - (u : ℂ)) := by simp
  simp only [this, Complex.norm_conj]

theorem Unu_conj' (α : ℝ) (s : ℂ) : Unu α ((starRingEnd ℂ) s) = Unu α s := by
  unfold Unu
  rw [Utau_conj', Uex_conj']

/-! ### Mesh choice -/

theorem exists_N_etaN_le (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) {θ : ℝ}
    (hθ : 0 < θ) : ∃ N : ℕ, 0 < N ∧ etaN A B f ρ N ≤ θ := by
  set E0 : ℝ := (1 / (2 * ρ)) * ∑ i, (‖B i - A i‖ / 2) * ∫ t in (0 : ℝ)..1, |f i t| with hE0
  have hE0n : 0 ≤ E0 := by
    rw [hE0]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg zero_le_one (fun t _ => abs_nonneg _))))
  obtain ⟨N, hN⟩ := exists_nat_gt (E0 / θ)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hNpos : 0 < N := by exact_mod_cast hN0
  refine ⟨N, hNpos, ?_⟩
  have e : etaN A B f ρ N = E0 / N := by
    unfold etaN
    have h1 : ∑ i, (‖B i - A i‖ / (2 * N)) * ∫ t in (0 : ℝ)..1, |f i t|
        = (∑ i, (‖B i - A i‖ / 2) * ∫ t in (0 : ℝ)..1, |f i t|) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun i _ => by field_simp)
    rw [h1, hE0]
    ring
  rw [e, div_le_iff₀ hN0]
  have := (div_lt_iff₀ hθ).1 hN
  linarith

theorem continuous_Usig_left {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (m : Fin K → ℝ) :
    Continuous (Usig ρ c m) := by
  unfold Usig
  refine continuous_finset_sum _ (fun k _ => continuous_const.mul ?_)
  have : (fun z => krho ρ z (c k)) = krho ρ (c k) := by funext z; exact krho_comm ρ z (c k)
  rw [this]
  exact continuous_krho hρ (c k)

/-- **The spline-to-atomic bridge.** -/
theorem exists_certCoreGs {sl : ℝ} {α : ℚ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    {A B : Fin n → ℂ} {f : Fin n → ℝ → ℝ} (C : SplineCert sl α ε A B f)
    (hAB : ∀ i, A i ≠ B i) (hf : ∀ i, Continuous (f i)) {M : Fin n → ℝ}
    (hM : ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) 1, |f i t| ≤ M i) {ρ : ℝ} (hρ : 0 < ρ)
    (hmass : ∑ i, ∫ t in (0 : ℝ)..1, f i t = 1) {V : ℚ} (hV : Vp f ≤ V)
    {Rc : ℝ} (hAR : ∀ i, ‖A i‖ ≤ Rc) (hBR : ∀ i, ‖B i‖ ≤ Rc)
    {τ : Fin n → Fin n} (hτ : Function.Involutive τ) (hAτ : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hBτ : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hfτ : ∀ i, f (τ i) = f i)
    (hUc : ContinuousOn (fun x : ℝ => Unu α (x : ℂ)) (Set.Icc (-(C.r0 : ℝ)) 0))
    {lossS : ℚ} (hlossS : Real.pi * ρ * Bs A B M ≤ lossS) {θ : ℚ} (hθ : 0 < θ) {ηS : ℚ} (hηS : 0 < ηS) :
    ∃ (K : ℕ) (c : Fin K → ℂ) (wt : Fin K → ℝ) (F : CertCoreGs sl K ρ ε c wt),
      (∀ s, F.g s = (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|) ∧
      F.r0 = C.r0 ∧ F.W = C.W ∧ F.umax = C.umax ∧
      F.mprime = C.mprime - (1 + α) * (lossS + θ) ∧
      F.gmin = C.gmin - (1 + α) * (lossS + θ) ∧
      F.ccert = C.ccert ∧ F.Sbase = C.Scap - ηS ∧
      F.Ibound = C.Ibound + V * lossS + 2 * V * θ ∧
      (∑ k, |wt k| ≤ V) ∧ (∀ k, ‖c k‖ ≤ Rc) := by
  classical
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  obtain ⟨N, hN, hetaN⟩ := exists_N_etaN_le A B f hρ hθR
  have hαR : (0 : ℝ) < α := by exact_mod_cast hα
  have hVp0 := Vp_nonneg f
  have hBs0 : 0 ≤ Real.pi * ρ * Bs A B M := by
    have hMn : ∀ i, 0 ≤ M i := fun i => (abs_nonneg _).trans (hM i 0 ⟨le_rfl, zero_le_one⟩)
    have : 0 ≤ Bs A B M := Finset.sum_nonneg (fun i _ => div_nonneg (hMn i) (norm_nonneg _))
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
  have hg : ∀ s : ℂ, |(1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|
      - gSpline α ε A B f s| ≤ (1 + (α : ℝ)) * ℓ := by
    intro s
    unfold gSpline
    have e : (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|
        - ((1 + (α : ℝ)) * U0 A B f s - Unu α s + (1 - ε) * Real.pi * |s.im|)
        = (1 + (α : ℝ)) * (Usig ρ c wt s - U0 A B f s) := by ring
    rw [e, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + (α : ℝ))]
    exact mul_le_mul_of_nonneg_left (hUerr s) (by linarith)
  have hgl : ∀ s : ℂ, gSpline α ε A B f s - (1 + (α : ℝ)) * ℓ
      ≤ (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im| := by
    intro s; have := (abs_le.1 (hg s)).1; linarith
  -- mass, variation, radius
  have hm1 : ∑ k, wt k = 1 := by rw [hwt, sum_wK f hf hN, hmass]
  have hVb : ∑ k, |wt k| ≤ V := (abs_sum_wK_le f hf hN).trans hV
  have hR : ∀ k, ‖c k‖ ≤ Rc := fun k => norm_cK_le A B hAR hBR hN k
  -- conjugation symmetry
  obtain ⟨σ, hσ, hσc, hσw⟩ := atoms_conj_symm A B f τ hτ hAτ hBτ hfτ N
  -- the atomic function on the real axis
  set G : ℝ → ℝ := fun x => (1 + (α : ℝ)) * Usig ρ c wt (x : ℂ) - Unu α (x : ℂ) + (1 - ε) * Real.pi * |(x : ℂ).im| with hG
  have hGc : ContinuousOn G (Set.Icc (-(C.r0 : ℝ)) 0) := by
    have h1 : Continuous (fun x : ℝ => (1 + (α : ℝ)) * Usig ρ c wt (x : ℂ)) :=
      continuous_const.mul ((continuous_Usig_left hρ c wt).comp Complex.continuous_ofReal)
    have h2 : (fun x : ℝ => (1 - ε) * Real.pi * |(x : ℂ).im|) = fun _ => 0 := by
      funext x; simp
    refine ((h1.continuousOn.sub hUc).add ?_)
    rw [h2]; exact continuousOn_const
  set mp : ℝ := (C.mprime : ℝ) - (1 + (α : ℝ)) * ℓ with hmp
  have hGge : ∀ x : ℝ, gSpline α ε A B f ⟨x, 0⟩ - (1 + (α : ℝ)) * ℓ ≤ G x := by
    intro x; exact hgl (x : ℂ)
  have hS : (C.Scap : ℝ) ≤ ∫ x in (-(C.r0 : ℝ))..0, min (G x - mp) 0 := by
    refine C.cap_ok.trans ?_
    have hle : -(C.r0 : ℝ) ≤ 0 := by
      have : (0 : ℝ) < C.r0 := by exact_mod_cast C.r0_pos
      linarith
    refine intervalIntegral.integral_mono_on hle C.cap_int ?_ (fun x _ => ?_)
    · exact (continuous_min.comp_continuousOn ((hGc.sub continuousOn_const).prodMk
        continuousOn_const)).intervalIntegrable_of_Icc hle
    · apply min_le_min _ le_rfl
      have := hGge x
      rw [hmp]; linarith
  obtain ⟨nSeg, segA, segB, segG, hab, hok, hcov, hsum⟩ :=
    exists_seg_cover C.r0_pos hGc mp (C.Scap : ℝ) hS (η := (ηS : ℝ)) (by exact_mod_cast hηS)
  -- assemble
  have hmpq : (((C.mprime - (1 + α) * (lossS + θ) : ℚ)) : ℝ) = mp := by
    rw [hmp, hℓ]; push_cast; ring
  have hgminq : (((C.gmin - (1 + α) * (lossS + θ) : ℚ)) : ℝ) = (C.gmin : ℝ) - (1 + (α : ℝ)) * ℓ := by
    rw [hℓ]; push_cast; ring
  have hIq : (((C.Ibound + V * lossS + 2 * V * θ : ℚ)) : ℝ)
      = (C.Ibound : ℝ) + (V : ℝ) * lossS + 2 * (V : ℝ) * θ := by push_cast; ring
  have hVR : Vp f ≤ (V : ℝ) := hV
  have hlossR : Real.pi * ρ * Bs A B M ≤ (lossS : ℝ) := hlossS
  have hIbd : Irho ρ c wt ≤ (C.Ibound : ℝ) + (V : ℝ) * lossS + 2 * (V : ℝ) * θ := by
    have e1 := energy_atom_err (A := A) (B := B) hf hρ hN
    have e2 := energy_smooth_err hAB hf hM hρ
    have e3 := C.I_ok
    have e4 : Vp f * (Real.pi * ρ * Bs A B M) ≤ (V : ℝ) * lossS :=
      mul_le_mul hVR hlossR hBs0 ((hVp0.trans hVR))
    have e5 : 2 * Vp f * etaN A B f ρ N ≤ 2 * (V : ℝ) * θ :=
      mul_le_mul (by linarith) hetaN (etaN_nonneg A B f hρ N) (by have := hVp0.trans hVR; linarith)
    have e6 := (abs_le.1 e1).2
    have e7 := (abs_le.1 e2).1
    linarith
  let F : CertCoreGs sl (n * N) ρ ε c wt :=
    { g := fun s => (1 + (α : ℝ)) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|
      r0 := C.r0
      W := C.W
      umax := C.umax
      mprime := C.mprime - (1 + α) * (lossS + θ)
      gmin := C.gmin - (1 + α) * (lossS + θ)
      Sbase := C.Scap - ηS
      Ibound := C.Ibound + V * lossS + 2 * V * θ
      ccert := C.ccert
      r0_pos := C.r0_pos
      W_pos := C.W_pos
      hρ := hρ
      hε0 := hε0
      hε1 := hε1
      hm := hm1
      g_conj := by
        intro s
        have h1 := Usig_conj_of_involution ρ c wt σ hσ hσc hσw s
        simp only [h1, Unu_conj', Complex.conj_im, abs_neg]
      rayBoxes := C.rayBoxes
      ray_box_ok := by
        intro p hp x y h1 h2 h3 h4
        have := C.ray_box_ok p hp x y h1 h2 h3 h4
        have h5 := hgl ⟨x, y⟩
        rw [hmpq, hmp]
        show _ ≤ (1 + (α : ℝ)) * Usig ρ c wt ⟨x, y⟩ - Unu α ⟨x, y⟩ + (1 - ε) * Real.pi * |(⟨x, y⟩ : ℂ).im|
        linarith
      ray_cover := C.ray_cover
      ray_tail := by
        intro u δ h1 h2
        have := C.ray_tail u δ h1 h2
        have h5 := hgl ⟨-(C.r0 : ℝ) + δ - u, sl * u⟩
        rw [hmpq, hmp]
        show _ ≤ (1 + (α : ℝ)) * Usig ρ c wt ⟨-(C.r0 : ℝ) + δ - u, sl * u⟩
          - Unu α ⟨-(C.r0 : ℝ) + δ - u, sl * u⟩ + (1 - ε) * Real.pi * |(⟨-(C.r0 : ℝ) + δ - u, sl * u⟩ : ℂ).im|
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
        show _ ≤ (1 + (α : ℝ)) * Usig ρ c wt ⟨x, 0⟩ - Unu α ⟨x, 0⟩ + (1 - ε) * Real.pi * |(⟨x, 0⟩ : ℂ).im|
        linarith
      line_cover := C.line_cover
      I_ok := by rw [hIq]; exact hIbd
      ccert_ge := by
        rw [hmpq, hgminq, hmp]
        have := C.ccert_ge
        linarith }
  exact ⟨n * N, c, wt, F, fun s => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hVb, hR⟩

end CatalanCore.Uniform.Decay.Spline
