module

public import CatalanCore.Uniform.Decay.Cells.Rules

@[expose] public section

/-!
# The cap rule (lane D, package D6)

`cap_ok : S_cap ≤ ∫_{-r0}^0 min (g - m') 0`, certified by the Darboux-type inequality
`∫ min (h, 0) = ∫ h - ∫ max (h, 0) ≥ ∫ h - Σ len · max (ub - m', 0)`
where the cap `[-r0, 0]` is chained into cells `(a, b, ub)` (`capChain`), each with an upper bound
`ub` of `g` (oracle `ubOk`), and `G ≤ ∫ g` is a lower bound of the exact integral (oracle `Gok`).
Everything else (continuity of `g` on the cap, integrability, the integral comparison) is proved.
-/

namespace CatalanCore.Uniform.Decay.Cells

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline

/-- A cap cell `(a, b, ub)`: `g ≤ ub` on `[a, b]`. -/
abbrev CapCell := ℚ × ℚ × ℚ

/-- The cells tile `[a, b]` consecutively. -/
def capChain : ℚ → List CapCell → ℚ → Bool
  | a, [], b => decide (a = b)
  | a, c :: cs, b => decide (c.1 = a) && decide (c.1 ≤ c.2.1) && capChain c.2.1 cs b

/-- `Σ len · max (ub - m, 0)`. -/
def capSum (m : ℚ) : List CapCell → ℚ
  | [] => 0
  | c :: cs => (c.2.1 - c.1) * max (c.2.2 - m) 0 + capSum m cs

theorem capChain_le : ∀ (cs : List CapCell) (a b : ℚ), capChain a cs b = true → a ≤ b := by
  intro cs
  induction cs with
  | nil => intro a b h; simp only [capChain, decide_eq_true_eq] at h; exact h.le
  | cons c cs ih =>
    intro a b h
    simp only [capChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := ih _ _ h3
    rw [← h1]; exact h2.trans this

/-- The integral of `max (h - m, 0)` over a chained cap is bounded by `capSum`. -/
theorem int_max_le {h : ℝ → ℝ} (m : ℚ) {lo hi : ℝ} (hc : ContinuousOn h (Icc lo hi)) (b : ℚ)
    (hb : (b : ℝ) = hi) :
    ∀ (cs : List CapCell) (a : ℚ), capChain a cs b = true → lo ≤ (a : ℝ) →
      (∀ c ∈ cs, ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 → h x ≤ c.2.2) →
      ∫ x in (a : ℝ)..hi, max (h x - m) 0 ≤ (capSum m cs : ℝ) := by
  intro cs
  induction cs with
  | nil =>
    intro a hch _ _
    simp only [capChain, decide_eq_true_eq] at hch
    subst hch
    rw [← hb]; simp [capSum]
  | cons c cs ih =>
    intro a hch hlo hub
    simp only [capChain, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨⟨h1, h2⟩, h3⟩ := hch
    have hF : ContinuousOn (fun x => max (h x - m) 0) (Icc lo hi) :=
      (Continuous.max continuous_id continuous_const).comp_continuousOn (ContinuousOn.sub hc continuousOn_const)
    have hle : (c.2.1 : ℝ) ≤ hi := by
      rw [← hb]; exact_mod_cast (capChain_le cs _ _ h3)
    have hac : (a : ℝ) ≤ (c.2.1 : ℝ) := by rw [← h1]; exact_mod_cast h2
    have hint1 : IntervalIntegrable (fun x => max (h x - m) 0) volume (a : ℝ) c.2.1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hac]
      exact hF.mono (Icc_subset_Icc hlo hle)
    have hint2 : IntervalIntegrable (fun x => max (h x - m) 0) volume (c.2.1 : ℝ) hi := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hle]
      exact hF.mono (Icc_subset_Icc (hlo.trans hac) le_rfl)
    rw [← integral_add_adjacent_intervals hint1 hint2]
    have hrest := ih c.2.1 h3 (hlo.trans hac) (fun c' hc' => hub c' (List.mem_cons_of_mem _ hc'))
    have hfirst : ∫ x in (a : ℝ)..c.2.1, max (h x - m) 0 ≤ ((c.2.1 - c.1 : ℚ) : ℝ) *
        ((max (c.2.2 - m) 0 : ℚ) : ℝ) := by
      have hconst : ∫ x in (a : ℝ)..c.2.1, ((max (c.2.2 - m) 0 : ℚ) : ℝ) =
          ((c.2.1 - c.1 : ℚ) : ℝ) * ((max (c.2.2 - m) 0 : ℚ) : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, ← h1]; push_cast; ring
      rw [← hconst]
      apply integral_mono_on hac hint1 intervalIntegrable_const
      intro x hx
      have hx1 : (c.1 : ℝ) ≤ x := by rw [← h1] at *; exact hx.1
      have := hub c List.mem_cons_self x hx1 hx.2
      push_cast
      exact max_le_max (by linarith) le_rfl
    simp only [capSum]
    push_cast at hfirst hrest ⊢
    linarith

/-- Oracles for the cap: upper bounds of `g` on cells, a lower bound of `∫ g`, continuity of the
second potential on the real axis. -/
structure CapOracle (Vnu : ℂ → ℝ) where
  ubOk : SplineData → CapCell → Bool
  Gok : SplineData → ℚ → Bool
  cont : ∀ D : SplineData, D.basicOk = true →
    ContinuousOn (fun x : ℝ => Vnu ⟨x, 0⟩) (Icc (-(D.r0 : ℝ)) 0)
  ub_sound : ∀ D : SplineData, D.basicOk = true → ∀ c, ubOk D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
    x ≤ c.2.1 → gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ c.2.2
  G_sound : ∀ D : SplineData, D.basicOk = true → ∀ G, Gok D G = true →
    (G : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0, gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩

/-- The cap checker. -/
def capOkOf {Vnu : ℂ → ℝ} (O : CapOracle Vnu) (cells : List CapCell) (G : ℚ) (D : SplineData) :
    Bool :=
  capChain (-D.r0) cells 0 && cells.all (O.ubOk D) && O.Gok D G &&
    decide (D.Scap + capSum D.mprime cells ≤ G - D.mprime * D.r0)

theorem capOkOf_sound {Vnu : ℂ → ℝ} (O : CapOracle Vnu) (cells : List CapCell) (G : ℚ)
    (D : SplineData) (hb : D.basicOk = true) (h : capOkOf O cells G D = true) :
    IntervalIntegrable
      (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0 := by
  simp only [capOkOf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hch, hall⟩, hG⟩, hsum⟩ := h
  have B := SplineData.basicOk_sound hb
  set g : ℝ → ℝ := fun x => gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ with hgdef
  have hr0 : (0 : ℝ) < D.r0 := by exact_mod_cast B.r0_pos
  have hge : ∀ x : ℝ, g x = (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) - Vnu ⟨x, 0⟩ := by
    intro x; simp [hgdef, gNu]
  have hgc : ContinuousOn g (Icc (-(D.r0 : ℝ)) 0) := by
    have h1 : Continuous (fun x : ℝ => (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ)) :=
      continuous_const.mul ((U0_continuous B).comp (Complex.continuous_ofReal : Continuous (fun x : ℝ => (⟨x, 0⟩ : ℂ))))
    have : g = fun x => (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) - Vnu ⟨x, 0⟩ := funext hge
    rw [this]
    exact h1.continuousOn.sub (O.cont D hb)
  have hF : ContinuousOn (fun x => min (g x - D.mprime) 0) (Icc (-(D.r0 : ℝ)) 0) :=
    (Continuous.min continuous_id continuous_const).comp_continuousOn (ContinuousOn.sub hgc continuousOn_const)
  have hsub : uIcc (-(D.r0 : ℝ)) 0 = Icc (-(D.r0 : ℝ)) 0 := uIcc_of_le (by linarith)
  have hgi : IntervalIntegrable g volume (-(D.r0 : ℝ)) 0 :=
    hgc.intervalIntegrable_of_Icc (by linarith)
  have hmaxc : ContinuousOn (fun x => max (g x - D.mprime) 0) (Icc (-(D.r0 : ℝ)) 0) :=
    (Continuous.max continuous_id continuous_const).comp_continuousOn (ContinuousOn.sub hgc continuousOn_const)
  have hmaxi : IntervalIntegrable (fun x => max (g x - D.mprime) 0) volume (-(D.r0 : ℝ)) 0 :=
    hmaxc.intervalIntegrable_of_Icc (by linarith)
  have hmini : IntervalIntegrable (fun x => min (g x - D.mprime) 0) volume (-(D.r0 : ℝ)) 0 :=
    hF.intervalIntegrable_of_Icc (by linarith)
  refine ⟨hmini, ?_⟩
  -- min = (g - m) - max
  have hmin : ∀ x, min (g x - D.mprime) 0 = (g x - D.mprime) - max (g x - D.mprime) 0 := by
    intro x
    rcases le_total (g x - D.mprime) 0 with hx | hx
    · rw [min_eq_left hx, max_eq_right hx]; ring
    · rw [min_eq_right hx, max_eq_left hx]; ring
  have hsplit : ∫ x in (-(D.r0 : ℝ))..0, min (g x - D.mprime) 0 =
      (∫ x in (-(D.r0 : ℝ))..0, g x) - (D.mprime : ℝ) * (D.r0 : ℝ) -
        ∫ x in (-(D.r0 : ℝ))..0, max (g x - D.mprime) 0 := by
    simp_rw [hmin]
    rw [integral_sub (hgi.sub intervalIntegrable_const) hmaxi, integral_sub hgi intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp; ring
  have hmax : ∫ x in (-(D.r0 : ℝ))..0, max (g x - D.mprime) 0 ≤ (capSum D.mprime cells : ℝ) := by
    have := int_max_le (h := g) D.mprime hgc 0 (by simp) cells (-D.r0) hch (by push_cast; exact le_rfl)
      (fun c hc x h1 h2 => O.ub_sound D hb c (List.all_eq_true.1 hall c hc) x h1 h2)
    push_cast at this
    exact this
  have hGi := O.G_sound D hb G hG
  have hsumR : (D.Scap : ℝ) + (capSum D.mprime cells : ℝ) ≤ (G : ℝ) - (D.mprime : ℝ) * (D.r0 : ℝ) := by
    exact_mod_cast hsum
  rw [hsplit]
  linarith

end CatalanCore.Uniform.Decay.Cells
