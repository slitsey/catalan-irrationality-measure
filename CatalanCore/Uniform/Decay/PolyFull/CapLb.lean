module

public import CatalanCore.Uniform.Decay.PolyFull.CapNodes

@[expose] public section
set_option Elab.async false

/-!
# A cap rule from lower bounds only (lane D, package D10)

D6's cap rule bounds `∫ min (g - m', 0)` by `∫ g` (pair energies) minus `∫ max (g - m', 0)` (upper
bounds of `g` on cells).  The alternative here uses *lower* bounds `lb ≤ g` on a chain of cells
`[a, b] ⊆ [-r0, 0]` (the same kind of near-cell oracle as for the line cells):

`Scap ≤ Σ len · min (lb - m', 0) ≤ ∫ min (g - m', 0)`.

No pair energies or upper bounds are needed; only continuity of the node potential on the cap.
-/

namespace CatalanCore.Uniform.Decay.PolyFull

open Finset Set intervalIntegral MeasureTheory CatalanCore.Uniform.Decay.Cert
  CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Cells

/-- `Σ len · min (lb - m, 0)`. -/
def capLbSum (m : ℚ) : List CapCell → ℚ
  | [] => 0
  | c :: cs => (c.2.1 - c.1) * min (c.2.2 - m) 0 + capLbSum m cs

theorem int_min_ge {h : ℝ → ℝ} (m : ℚ) {lo hi : ℝ} (hc : ContinuousOn h (Icc lo hi)) (b : ℚ)
    (hb : (b : ℝ) = hi) :
    ∀ (cs : List CapCell) (a : ℚ), capChain a cs b = true → lo ≤ (a : ℝ) →
      (∀ c ∈ cs, ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 → c.2.2 ≤ h x) →
      (capLbSum m cs : ℝ) ≤ ∫ x in (a : ℝ)..hi, min (h x - m) 0 := by
  intro cs
  induction cs with
  | nil =>
    intro a hch _ _
    simp only [capChain, decide_eq_true_eq] at hch
    subst hch
    rw [← hb]; simp [capLbSum]
  | cons c cs ih =>
    intro a hch hlo hub
    simp only [capChain, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨⟨h1, h2⟩, h3⟩ := hch
    have hF : ContinuousOn (fun x => min (h x - m) 0) (Icc lo hi) :=
      (Continuous.min continuous_id continuous_const).comp_continuousOn
        (ContinuousOn.sub hc continuousOn_const)
    have hle : (c.2.1 : ℝ) ≤ hi := by
      rw [← hb]; exact_mod_cast (capChain_le cs _ _ h3)
    have hac : (a : ℝ) ≤ (c.2.1 : ℝ) := by rw [← h1]; exact_mod_cast h2
    have hint1 : IntervalIntegrable (fun x => min (h x - m) 0) volume (a : ℝ) c.2.1 := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hac]
      exact hF.mono (Icc_subset_Icc hlo hle)
    have hint2 : IntervalIntegrable (fun x => min (h x - m) 0) volume (c.2.1 : ℝ) hi := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hle]
      exact hF.mono (Icc_subset_Icc (hlo.trans hac) le_rfl)
    rw [← integral_add_adjacent_intervals hint1 hint2]
    have hrest := ih c.2.1 h3 (hlo.trans hac) (fun c' hc' => hub c' (List.mem_cons_of_mem _ hc'))
    have hfirst : ((c.2.1 - c.1 : ℚ) : ℝ) * ((min (c.2.2 - m) 0 : ℚ) : ℝ) ≤
        ∫ x in (a : ℝ)..c.2.1, min (h x - m) 0 := by
      have hconst : ∫ x in (a : ℝ)..c.2.1, ((min (c.2.2 - m) 0 : ℚ) : ℝ) =
          ((c.2.1 - c.1 : ℚ) : ℝ) * ((min (c.2.2 - m) 0 : ℚ) : ℝ) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, ← h1]; push_cast; ring
      rw [← hconst]
      apply integral_mono_on hac intervalIntegrable_const hint1
      intro x hx
      have hx1 : (c.1 : ℝ) ≤ x := by rw [← h1] at *; exact hx.1
      have := hub c List.mem_cons_self x hx1 hx.2
      push_cast
      exact min_le_min (by linarith) le_rfl
    simp only [capLbSum]
    push_cast at hfirst hrest ⊢
    linarith

/-- Oracle for lower bounds of `g` on cap cells `(a, b, lb)`. -/
structure CapLb (Vnu : ℂ → ℝ) where
  lbOk : SplineData → CapCell → Bool
  lb_sound : ∀ D : SplineData, D.basicOk = true → ∀ c, lbOk D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
    x ≤ c.2.1 → (c.2.2 : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩

/-- The lower-bound cap checker. -/
def capLbOkOf {Vnu : ℂ → ℝ} (O : CapLb Vnu) (cells : List CapCell) (D : SplineData) : Bool :=
  capChain (-D.r0) cells 0 && cells.all (O.lbOk D) && decide (D.Scap ≤ capLbSum D.mprime cells)

theorem capLbOkOf_sound {Vnu : ℂ → ℝ} (O : CapLb Vnu) (cells : List CapCell) (D : SplineData)
    (hb : D.basicOk = true)
    (hcont : ContinuousOn (fun x : ℝ => Vnu ⟨x, 0⟩) (Icc (-(D.r0 : ℝ)) 0))
    (h : capLbOkOf O cells D = true) :
    IntervalIntegrable
      (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0 := by
  simp only [capLbOkOf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hch, hall⟩, hsum⟩ := h
  have B := SplineData.basicOk_sound hb
  set g : ℝ → ℝ := fun x => gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ with hgdef
  have hr0 : (0 : ℝ) < D.r0 := by exact_mod_cast B.r0_pos
  have hgc : ContinuousOn g (Icc (-(D.r0 : ℝ)) 0) := by
    have h1 : Continuous (fun x : ℝ => (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ)) :=
      continuous_const.mul ((U0_continuous B).comp
        (Complex.continuous_ofReal : Continuous (fun x : ℝ => (⟨x, 0⟩ : ℂ))))
    have : g = fun x => (D.Mq : ℝ) * U0 D.A D.B D.f (⟨x, 0⟩ : ℂ) - Vnu ⟨x, 0⟩ := by
      funext x; simp [hgdef, gNu]
    rw [this]
    exact h1.continuousOn.sub hcont
  have hF : ContinuousOn (fun x => min (g x - D.mprime) 0) (Icc (-(D.r0 : ℝ)) 0) :=
    (Continuous.min continuous_id continuous_const).comp_continuousOn
      (ContinuousOn.sub hgc continuousOn_const)
  have hmini : IntervalIntegrable (fun x => min (g x - D.mprime) 0) volume (-(D.r0 : ℝ)) 0 :=
    hF.intervalIntegrable_of_Icc (by linarith)
  refine ⟨hmini, ?_⟩
  have := int_min_ge (h := g) D.mprime hgc 0 (by simp) cells (-D.r0) hch
    (by push_cast; exact le_rfl)
    (fun c hc x h1 h2 => O.lb_sound D hb c (List.all_eq_true.1 hall c hc) x h1 h2)
  push_cast at this
  have hsumR : (D.Scap : ℝ) ≤ (capLbSum D.mprime cells : ℝ) := by exact_mod_cast hsum
  linarith

end CatalanCore.Uniform.Decay.PolyFull
