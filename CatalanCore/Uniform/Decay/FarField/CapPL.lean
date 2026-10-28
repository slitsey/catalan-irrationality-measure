import CatalanCore.Uniform.Decay.Cells.Cap
set_option Elab.async false

/-!
# Cap with a piecewise-linear majorant (lane D, package D15)

A PL cap cell `(a, b, ua, ub)` asserts `g ≤ ℓ` on `[a, b]`, where `ℓ` is the chord from `ua` (at `a`)
to `ub` (at `b`).  The overshoot budget uses the trapezoid rule
`∫_a^b max(g - m', 0) ≤ (b-a)(max(ua-m',0) + max(ub-m',0))/2`, which is exact when `ua - m'` and
`ub - m'` have the same sign (a cell whose chord crosses `m'` is split at the crossing).  A constant
upper bound `ub` is the case `ua = ub`.  `plCapOkOf_sound` has the conclusion of `Cells.capOkOf_sound`.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Set MeasureTheory intervalIntegral CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Spline

/-- A PL cap cell `(a, b, ua, ub)`. -/
abbrev PLCell := ℚ × ℚ × ℚ × ℚ

/-- The majorant (chord) of the cell. -/
noncomputable def plLine (c : PLCell) (x : ℝ) : ℝ :=
  (c.2.2.1 : ℝ) + ((c.2.2.2 : ℝ) - c.2.2.1) * (x - c.1) / ((c.2.1 : ℝ) - c.1)

/-- The cells tile `[a, b]` consecutively. -/
def plChain : ℚ → List PLCell → ℚ → Bool
  | a, [], b => decide (a = b)
  | a, c :: cs, b => decide (c.1 = a) && decide (c.1 ≤ c.2.1) && plChain c.2.1 cs b

/-- The trapezoid overshoot budget. -/
def plSum (m : ℚ) : List PLCell → ℚ
  | [] => 0
  | c :: cs => (c.2.1 - c.1) * (max (c.2.2.1 - m) 0 + max (c.2.2.2 - m) 0) / 2 + plSum m cs

theorem plChain_le : ∀ (cs : List PLCell) (a b : ℚ), plChain a cs b = true → a ≤ b := by
  intro cs
  induction cs with
  | nil => intro a b h; simp only [plChain, decide_eq_true_eq] at h; exact h.le
  | cons c cs ih =>
    intro a b h
    simp only [plChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have := ih _ _ h3
    rw [← h1]; exact h2.trans this

/-- One cell: `∫ max(g - m, 0)` is at most the trapezoid. -/
theorem cell_int_le {h : ℝ → ℝ} (m : ℚ) (c : PLCell) (hac : (c.1 : ℝ) ≤ c.2.1)
    (hint : IntervalIntegrable (fun x => max (h x - m) 0) volume (c.1 : ℝ) c.2.1)
    (hub : ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 → h x ≤ plLine c x) :
    ∫ x in (c.1 : ℝ)..c.2.1, max (h x - m) 0
      ≤ ((c.2.1 - c.1) * (max (c.2.2.1 - m) 0 + max (c.2.2.2 - m) 0) / 2 : ℚ) := by
  obtain ⟨a, b, ua, ub⟩ := c
  simp only at hac hint hub ⊢
  rcases hac.eq_or_lt with hab | hab
  · have hq : a = b := by exact_mod_cast hab
    subst hq; simp
  set len : ℝ := (b : ℝ) - a with hlen
  have hlen0 : 0 < len := by rw [hlen]; linarith
  set P : ℝ := max ((ua : ℝ) - m) 0 with hP
  set Q : ℝ := max ((ub : ℝ) - m) 0 with hQ
  have hmaj : ∀ x ∈ Icc (a : ℝ) b, max (h x - m) 0 ≤ P + (Q - P) * (x - a) / len := by
    intro x hx
    have hτ0 : 0 ≤ (x - a) / len := div_nonneg (by linarith [hx.1]) hlen0.le
    have hτ1 : (x - a) / len ≤ 1 := (div_le_one hlen0).2 (by rw [hlen]; linarith [hx.2])
    have hline := hub x hx.1 hx.2
    unfold plLine at hline
    simp only at hline
    set τ := (x - a) / len with hτ
    have hl : (ua : ℝ) + ((ub : ℝ) - ua) * (x - a) / ((b : ℝ) - a) = (1 - τ) * ua + τ * ub := by
      rw [hτ, hlen]; ring
    rw [hl] at hline
    have hp : (ua : ℝ) - m ≤ P := le_max_left _ _
    have hq : (ub : ℝ) - m ≤ Q := le_max_left _ _
    have hP0 : 0 ≤ P := le_max_right _ _
    have hQ0 : 0 ≤ Q := le_max_right _ _
    have e : P + (Q - P) * (x - a) / len = (1 - τ) * P + τ * Q := by rw [hτ]; ring
    rw [e]
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 1 - τ),
        mul_le_mul_of_nonneg_left hq hτ0]
    · nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - τ) hP0, mul_nonneg hτ0 hQ0]
  have hlin : IntervalIntegrable (fun x : ℝ => P + (Q - P) * (x - a) / len) volume (a : ℝ) b := by
    apply Continuous.intervalIntegrable; fun_prop
  have hint2 : ∫ x in (a : ℝ)..b, (P + (Q - P) * (x - a) / len) = len * (P + Q) / 2 := by
    have e : ∀ x : ℝ, P + (Q - P) * (x - a) / len = P + ((Q - P) / len) * (x - a) := by
      intro x; ring
    simp_rw [e]
    have i1 : IntervalIntegrable (fun _ : ℝ => P) volume (a : ℝ) b := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun x : ℝ => (Q - P) / len * (x - a)) volume (a : ℝ) b := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) (a : ℝ)]
    simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
    rw [hlen]
    field_simp
    ring
  calc ∫ x in (a : ℝ)..b, max (h x - m) 0
      ≤ ∫ x in (a : ℝ)..b, (P + (Q - P) * (x - a) / len) :=
        intervalIntegral.integral_mono_on hab.le hint hlin hmaj
    _ = len * (P + Q) / 2 := hint2
    _ = _ := by
        rw [hlen, hP, hQ]; push_cast; ring

/-- The integral of `max (g - m, 0)` over a chained PL cap is bounded by `plSum`. -/
theorem int_max_le_pl {h : ℝ → ℝ} (m : ℚ) {lo hi : ℝ} (hc : ContinuousOn h (Icc lo hi)) (b : ℚ)
    (hb : (b : ℝ) = hi) :
    ∀ (cs : List PLCell) (a : ℚ), plChain a cs b = true → lo ≤ (a : ℝ) →
      (∀ c ∈ cs, ∀ x : ℝ, (c.1 : ℝ) ≤ x → x ≤ c.2.1 → h x ≤ plLine c x) →
      ∫ x in (a : ℝ)..hi, max (h x - m) 0 ≤ (plSum m cs : ℝ) := by
  intro cs
  induction cs with
  | nil =>
    intro a hch _ _
    simp only [plChain, decide_eq_true_eq] at hch
    subst hch
    rw [← hb]; simp [plSum]
  | cons c cs ih =>
    intro a hch hlo hub
    simp only [plChain, Bool.and_eq_true, decide_eq_true_eq] at hch
    obtain ⟨⟨h1, h2⟩, h3⟩ := hch
    have hF : ContinuousOn (fun x => max (h x - m) 0) (Icc lo hi) :=
      (Continuous.max continuous_id continuous_const).comp_continuousOn (ContinuousOn.sub hc continuousOn_const)
    have hle : (c.2.1 : ℝ) ≤ hi := by
      rw [← hb]; exact_mod_cast (plChain_le cs _ _ h3)
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
    have hfirst : ∫ x in (a : ℝ)..c.2.1, max (h x - m) 0
        ≤ (((c.2.1 - c.1) * (max (c.2.2.1 - m) 0 + max (c.2.2.2 - m) 0) / 2 : ℚ) : ℝ) := by
      rw [← h1]
      exact cell_int_le m c (by rw [h1]; exact hac) (by rw [h1]; exact hint1)
        (hub c List.mem_cons_self)
    simp only [plSum]
    push_cast at hfirst hrest ⊢
    linarith

/-- The cap checker with PL cells; the `CapOracle` supplies `Gok`, `G_sound` and continuity only. -/
def plCapOkOf {Vnu : ℂ → ℝ} (O : CapOracle Vnu) (ubPL : SplineData → PLCell → Bool)
    (cells : List PLCell) (G : ℚ) (D : SplineData) : Bool :=
  plChain (-D.r0) cells 0 && cells.all (ubPL D) && O.Gok D G &&
    decide (D.Scap + plSum D.mprime cells ≤ G - D.mprime * D.r0)

theorem plCapOkOf_sound {Vnu : ℂ → ℝ} (O : CapOracle Vnu) (ubPL : SplineData → PLCell → Bool)
    (hub : ∀ D : SplineData, D.basicOk = true → ∀ c, ubPL D c = true → ∀ x : ℝ, (c.1 : ℝ) ≤ x →
      x ≤ c.2.1 → gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ ≤ plLine c x)
    (cells : List PLCell) (G : ℚ)
    (D : SplineData) (hb : D.basicOk = true) (h : plCapOkOf O ubPL cells G D = true) :
    IntervalIntegrable
      (fun x : ℝ => min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0)
      volume (-(D.r0 : ℝ)) 0 ∧
    (D.Scap : ℝ) ≤ ∫ x in (-(D.r0 : ℝ))..0,
      min (gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f ⟨x, 0⟩ - D.mprime) 0 := by
  simp only [plCapOkOf, Bool.and_eq_true, decide_eq_true_eq] at h
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
  have hgi : IntervalIntegrable g volume (-(D.r0 : ℝ)) 0 :=
    hgc.intervalIntegrable_of_Icc (by linarith)
  have hmaxc : ContinuousOn (fun x => max (g x - D.mprime) 0) (Icc (-(D.r0 : ℝ)) 0) :=
    (Continuous.max continuous_id continuous_const).comp_continuousOn (ContinuousOn.sub hgc continuousOn_const)
  have hmaxi : IntervalIntegrable (fun x => max (g x - D.mprime) 0) volume (-(D.r0 : ℝ)) 0 :=
    hmaxc.intervalIntegrable_of_Icc (by linarith)
  have hmini : IntervalIntegrable (fun x => min (g x - D.mprime) 0) volume (-(D.r0 : ℝ)) 0 :=
    hF.intervalIntegrable_of_Icc (by linarith)
  refine ⟨hmini, ?_⟩
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
  have hmax : ∫ x in (-(D.r0 : ℝ))..0, max (g x - D.mprime) 0 ≤ (plSum D.mprime cells : ℝ) := by
    have := int_max_le_pl (h := g) D.mprime hgc 0 (by simp) cells (-D.r0) hch (by push_cast; exact le_rfl)
      (fun c hc x h1 h2 => hub D hb c (List.all_eq_true.1 hall c hc) x h1 h2)
    push_cast at this
    exact this
  have hGi := O.G_sound D hb G hG
  have hsumR : (D.Scap : ℝ) + (plSum D.mprime cells : ℝ) ≤ (G : ℝ) - (D.mprime : ℝ) * (D.r0 : ℝ) := by
    exact_mod_cast hsum
  rw [hsplit]
  linarith

end CatalanCore.Uniform.Decay.FarField
