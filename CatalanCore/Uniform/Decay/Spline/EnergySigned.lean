module

public import CatalanCore.Decay.Rect.Energy3

@[expose] public section

/-!
# Signed trial measures: the signed `Usig_ge`, `pt_ineq` and `energy_rect` (lane D, package D2)

Replaces the positivity hypothesis `hw0 : ∀ k, 0 ≤ wt k` of `Energy1.Usig_ge` / `Energy3.energy_rectW`
by a presentation total-variation bound `∑ |wt k| ≤ V`.

* `Usig_ge_signed` : `Usig ρ c wt s ≥ -V (‖s‖ + Rc + ρ + Lp ρ)`, `Lp ρ = max 0 (-log ρ)` (`= log⁺ (1/ρ)`).
* `pt_ineqWS` : the pointwise comparison with the coefficient `2V/r` on the imaginary part.
* `energy_rectWS` : `energy_rectW` with `A_V = V (A₀ + Lp ρ)` replacing `A₀` and the threshold
  `2 w V ≤ π (ε - e) r`.  The positive case is `V = 1`.
-/

open Finset
open CatalanLambda.Decay

namespace CatalanCore.Decay

variable {sl : ℝ}

/-- `log⁺ (1/ρ)`. -/
noncomputable def Lp (ρ : ℝ) : ℝ := max 0 (-Real.log ρ)

theorem Lp_nonneg (ρ : ℝ) : 0 ≤ Lp ρ := le_max_left _ _

theorem neg_log_le_Lp (ρ : ℝ) : -Real.log ρ ≤ Lp ρ := le_max_right _ _

/-- `k_ρ ≤ log⁺ (1/ρ)`. -/
theorem krho_le_Lp {ρ : ℝ} (hρ : 0 < ρ) (x y : ℂ) : krho ρ x y ≤ Lp ρ := by
  unfold krho
  have h1 : Real.log (ρ ^ 2) ≤ Real.log (‖x - y‖ ^ 2 + ρ ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ‖x - y‖])
  rw [Real.log_pow] at h1
  push_cast at h1
  have := neg_log_le_Lp ρ
  linarith

/-- `k_ρ ≥ -(‖s‖ + R + ρ)` for `‖w‖ ≤ R`. -/
theorem neg_le_krho {ρ : ℝ} (hρ : 0 < ρ) {Rc : ℝ} (s w : ℂ) (hw : ‖w‖ ≤ Rc) :
    -(‖s‖ + Rc + ρ) ≤ krho ρ s w := by
  set X : ℝ := ‖s‖ + Rc + ρ with hX
  have hRc : 0 ≤ Rc := (norm_nonneg _).trans hw
  have hX0 : 0 < X := by have := norm_nonneg s; positivity
  unfold krho
  have h1 : ‖s - w‖ ≤ ‖s‖ + Rc := (norm_sub_le _ _).trans (by linarith)
  have h2 : ‖s - w‖ ^ 2 + ρ ^ 2 ≤ X ^ 2 := by
    have := norm_nonneg (s - w)
    nlinarith [norm_nonneg s]
  have h3 : Real.log (‖s - w‖ ^ 2 + ρ ^ 2) ≤ Real.log (X ^ 2) :=
    Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have h4 := Real.log_le_sub_one_of_pos hX0
  push_cast at h3
  linarith

/-- **Signed `Usig_ge`.** -/
theorem Usig_ge_signed {K : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (c : Fin K → ℂ) (wt : Fin K → ℝ)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc) (s : ℂ) :
    -(V * (‖s‖ + Rc + ρ + Lp ρ)) ≤ Usig ρ c wt s := by
  have hL := Lp_nonneg ρ
  set X : ℝ := ‖s‖ + Rc + ρ + Lp ρ with hX
  have hX0 : 0 ≤ X := by have := norm_nonneg s; positivity
  have key : ∀ k, |krho ρ s (c k)| ≤ X := by
    intro k
    have a := neg_le_krho hρ (Rc := Rc) s (c k) (hc k)
    have b := krho_le_Lp hρ s (c k)
    have hn := norm_nonneg s
    rw [abs_le]; constructor <;> nlinarith [hρ]
  have hV : ∀ k, |wt k * krho ρ s (c k)| ≤ |wt k| * X := fun k => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (key k) (abs_nonneg _)
  have h2 : |Usig ρ c wt s| ≤ V * X := by
    unfold Usig
    calc |∑ k, wt k * krho ρ s (c k)| ≤ ∑ k, |wt k * krho ρ s (c k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, |wt k| * X := Finset.sum_le_sum (fun k _ => hV k)
      _ = (∑ k, |wt k|) * X := by rw [Finset.sum_mul]
      _ ≤ V * X := mul_le_mul_of_nonneg_right hwV hX0
  have := (abs_le.1 h2).1
  linarith

theorem one_le_V {K : ℕ} {wt : Fin K → ℝ} (hm : ∑ k, wt k = 1) {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) :
    1 ≤ V := by
  have : |∑ k, wt k| ≤ ∑ k, |wt k| := Finset.abs_sum_le_sum_abs _ _
  rw [hm, abs_one] at this
  linarith

/-- Pointwise comparison with the signed coefficient `2V/r` on the imaginary part. -/
lemma pt_ineqWS {r m : ℕ} {α ε A0 Y U I g δ' w V : ℝ} (hr' : 0 < (r : ℝ)) (hδ0 : 0 ≤ δ')
    (hδ1 : δ' ≤ w) (hδdef : δ' = m - α * r) (hI : 0 ≤ I) (hA0 : 0 ≤ A0) (hV : 0 ≤ V)
    (hY : -(A0 + (2 * V / r) * I) ≤ Y) (hg : g = (1 + α) * Y - U + ((1 - ε) * Real.pi / r) * I) :
    2 * r * g - 2 * (1 - ε) * Real.pi * I - 2 * w * A0 - (4 * w * V / r) * I
      ≤ 2 * ((r : ℝ) + m) * Y - 2 * r * U := by
  have hX0 : 0 ≤ A0 + (2 * V / r) * I := by positivity
  have h1 : 0 ≤ δ' * (Y + (A0 + (2 * V / r) * I)) := mul_nonneg hδ0 (by linarith)
  have h2 : δ' * (A0 + (2 * V / r) * I) ≤ w * (A0 + (2 * V / r) * I) :=
    mul_le_mul_of_nonneg_right hδ1 hX0
  have hm : (m : ℝ) = δ' + α * r := by linarith
  have e : 2 * (r : ℝ) * g = 2 * r * (1 + α) * Y - 2 * r * U + 2 * (1 - ε) * Real.pi * I := by
    rw [hg]; field_simp
  have e2 : (4 * w * V / (r : ℝ)) * I = 2 * (w * ((2 * V / r) * I)) := by ring
  rw [e, hm, e2]
  nlinarith [h1, h2]

set_option maxHeartbeats 4000000 in
theorem energy_rectWS {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    {Fr : Frame} (hFr : Fr.DecayOKs sl) (F : Cert.CertCoreGs sl K ρ ε c wt)
    {α : ℝ} (hα : 0 < α) {w : ℝ} (hw : 1 ≤ w)
    (hg : ∀ s : ℂ, F.g s = (1 + α) * Usig ρ c wt s - Unu α s + (1 - ε) * Real.pi * |s.im|)
    {V : ℝ} (hwV : ∑ k, |wt k| ≤ V) {Rc : ℝ} (hRc : 0 ≤ Rc) (hc : ∀ k, ‖c k‖ ≤ Rc)
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (hαr : α * r ≤ m) (hαr' : (m : ℝ) ≤ α * r + w)
    {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * r⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * r)
    {m0 : ℝ} (hm0 : 0 < m0)
    {k : ℕ} (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hz : ∀ l, Fr.IsAtom N0 (z l) ∨ Fr.IsRay sl N0 (z l)) (hre : ∀ l, m0 ≤ -(z l).re)
    (s : Fin k → Fin (r + m)) (hs : Function.Injective s)
    (hkeep : ∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b)
    {e : ℝ} (he0 : 0 < e) (heε : e < ε) (hrbig : 2 * w * V ≤ Real.pi * (ε - e) * r)
    (q : Fin k → ℝ) {Cl : ℝ} (hCl : 0 ≤ Cl)
    (hq : ∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(z l).im|)) :
    ∑ l, Real.log (q l)
      + (1 / 2) * (Real.log (‖cexpr z (fun i => ((xnode r (s i) : ℕ) : ℂ))‖ ^ 2)
          + Real.log (‖cexpr z (fun i => ((ynode r (s i) : ℕ) : ℂ))‖ ^ 2))
      ≤ -(2 * r * ((r : ℝ) + m) * F.mprime + 2 * r ^ 2 * (Fr.d * F.Sbase)
            - ((r : ℝ) + m) ^ 2 * F.Ibound + Alow r m)
        + r * (((r : ℝ) + m) - k) * F.ccert
        + RerrRW w (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
            (V * ((F.r0 : ℝ) + Fr.xs + Rc + ρ + 1 + Lp ρ)) ρ m0 Cl α r m := by
  classical
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ := F.hρ
  have hε0 := F.hε0
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hFr.contour.xs_pos
  have hr0q : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hNpos : 0 < r + m := by omega
  have hNc : (((r + m : ℕ)) : ℝ) = (r : ℝ) + m := by push_cast; ring
  have hN' : (0 : ℝ) < (r : ℝ) + m := by positivity
  have hkN : k ≤ r + m := by simpa using Fintype.card_le_of_injective s hs
  have hkN' : (k : ℝ) ≤ (r : ℝ) + m := by exact_mod_cast hkN
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨δ', hδ'⟩ : ∃ δ', δ' = (m : ℝ) - α * r := ⟨_, rfl⟩
  have hδ0 : 0 ≤ δ' := by rw [hδ']; linarith
  have hδ1 : δ' ≤ w := by rw [hδ']; linarith
  have hL0 : 0 < 2 * α := by linarith
  have hL : 2 * α ≤ 2 * m / r := by rw [le_div_iff₀ hr']; nlinarith
  have hL2 : 2 * (m : ℝ) / r ≤ 2 * α + 2 * w / r := by
    rw [div_le_iff₀ hr']
    have e1 : (2 * α + 2 * w / (r : ℝ)) * r = 2 * α * r + 2 * w := by field_simp
    rw [e1]; linarith
  have hV1 : 1 ≤ V := one_le_V F.hm hwV
  have hV0 : 0 ≤ V := by linarith
  have hLp : 0 ≤ Lp ρ := Lp_nonneg ρ
  have hA0 : 0 ≤ V * ((F.r0 : ℝ) + Fr.xs + Rc + ρ + 1 + Lp ρ) := by positivity
  set A0 : ℝ := V * ((F.r0 : ℝ) + Fr.xs + Rc + ρ + 1 + Lp ρ) with hA0def
  -- positions
  set σ : Fin k → ℂ := fun l => z l / r with hσ
  set τX : Fin (r + m) → ℂ := fun b => nodeC r (xnode r b) with hτX
  set τY : Fin (r + m) → ℂ := fun b => nodeC r (ynode r b) with hτY
  have hσre : ∀ l, (σ l).re = (z l).re / r := fun l => by simp [hσ, Complex.div_natCast_re]
  have hσim : ∀ l, (σ l).im = (z l).im / r := fun l => by simp [hσ, Complex.div_natCast_im]
  have hσneg : ∀ l, m0 / r ≤ -(σ l).re := by
    intro l; rw [hσre, neg_div']; exact div_le_div_of_nonneg_right (hre l) hr'.le
  have hσneg' : ∀ l, (σ l).re < 0 := fun l => by
    have h1 := hσneg l
    have h2 : 0 < m0 / r := by positivity
    linarith
  have hσi : Function.Injective σ := by
    intro a b hab
    apply hzi
    have h1 : z a / r = z b / r := hab
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact (div_left_inj' hrC).1 h1
  have hτXre : ∀ b, 0 ≤ (τX b).re := fun b => by
    simp only [hτX]; rw [nodeC_re]; positivity
  have hτYre : ∀ b, 0 ≤ (τY b).re := fun b => by
    simp only [hτY]; rw [nodeC_re]; positivity
  have hτXi : Function.Injective τX := by
    intro a b hab
    have h1 : nodeC r (xnode r a) = nodeC r (xnode r b) := hab
    exact Fin.ext (xnode_inj r (nodeC_inj_nat hr h1))
  have hτYi : Function.Injective τY := by
    intro a b hab
    have h1 : nodeC r (ynode r a) = nodeC r (ynode r b) := hab
    exact Fin.ext (ynode_inj r (nodeC_inj_nat hr h1))
  have hστX : ∀ l b, σ l ≠ τX b := fun l b e' => by
    have h1 := congrArg Complex.re e'
    have h2 := hσneg' l
    have h3 := hτXre b
    linarith
  have hστY : ∀ l b, σ l ≠ τY b := fun l b e' => by
    have h1 := congrArg Complex.re e'
    have h2 := hσneg' l
    have h3 := hτYre b
    linarith
  have hpiX : Function.Injective (Sum.elim σ τX) := by
    intro x y hxy
    rcases x with l | b <;> rcases y with l' | b'
    · simp only [Sum.elim_inl] at hxy; rw [hσi hxy]
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy (hστX _ _)
    · simp only [Sum.elim_inl, Sum.elim_inr] at hxy; exact absurd hxy.symm (hστX _ _)
    · simp only [Sum.elim_inr] at hxy; rw [hτXi hxy]
  -- row / column Cauchy expressions
  set rowC : Fin k → ℂ := fun i => ((xnode r (s i) : ℕ) : ℂ) with hrowC
  set colC : Fin k → ℂ := fun i => ((ynode r (s i) : ℕ) : ℂ) with hcolC
  have hrowi : Function.Injective rowC := by
    intro a b hab
    have h1 : ((xnode r (s a) : ℕ) : ℂ) = ((xnode r (s b) : ℕ) : ℂ) := hab
    have h2 := Nat.cast_injective (R := ℂ) h1
    exact hs (Fin.ext (xnode_inj r h2))
  have hcoli : Function.Injective colC := by
    intro a b hab
    have h1 : ((ynode r (s a) : ℕ) : ℂ) = ((ynode r (s b) : ℕ) : ℂ) := hab
    have h2 := Nat.cast_injective (R := ℂ) h1
    exact hs (Fin.ext (ynode_inj r h2))
  have hzrow : ∀ l i, z l ≠ rowC i := by
    intro l i e'
    have h1 := congrArg Complex.re e'
    simp only [hrowC, Complex.natCast_re] at h1
    have h2 := hre l
    have h3 : (0 : ℝ) ≤ ((xnode r (s i) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hzcol : ∀ l i, z l ≠ colC i := by
    intro l i e'
    have h1 := congrArg Complex.re e'
    simp only [hcolC, Complex.natCast_re] at h1
    have h2 := hre l
    have h3 : (0 : ℝ) ≤ ((ynode r (s i) : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hrowτ : (fun i => rowC i / (r : ℂ)) = fun i => τX (s i) := by
    funext i; simp only [hrowC, hτX]; exact natC_div r _ hr
  have hcolτ : (fun i => colC i / (r : ℂ)) = fun i => τY (s i) := by
    funext i; simp only [hcolC, hτY]; exact natC_div r _ hr
  have hX := neg_log_cexpr_scaled hr z rowC hzi hrowi hzrow
  have hY := neg_log_cexpr_scaled hr z colC hzi hcoli hzcol
  rw [hrowτ] at hX
  rw [hcolτ] at hY
  have hX' : -Real.log (‖cexpr z rowC‖ ^ 2) = Esc σ (fun i => τX (s i)) + 2 * k * Real.log r := hX
  have hY' : -Real.log (‖cexpr z colC‖ ^ 2) = Esc σ (fun i => τY (s i)) + 2 * k * Real.log r := hY
  -- masks
  have hmsk01 : ∀ b, rmask s b = 0 ∨ rmask s b = 1 := rmask_cases s
  have hmskr : ∀ b : Fin (r + m), r ≤ (b : ℕ) → rmask s b = 0 := by
    intro b hb
    obtain ⟨i, hi⟩ := hkeep b hb
    unfold rmask
    rw [if_pos (Finset.mem_image.2 ⟨i, Finset.mem_univ _, hi⟩)]
  have hmsum : ∑ b, rmask s b = (((r + m : ℕ)) : ℝ) - k := by
    have h1 := sum_mask s hs (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_sub_distrib] at h1
    linarith
  have hmsum' : ∑ b, rmask s b = ((r : ℝ) + m) - k := by rw [hmsum, hNc]
  have hτeq : ∀ b : Fin (r + m), rmask s b ≠ 0 → τX b = τY b := by
    intro b hb
    have hb1 : (b : ℕ) < r := by
      by_contra h; exact hb (hmskr b (not_lt.1 h))
    simp only [hτX, hτY, xnode_lt r hb1, ynode_lt r hb1]
  have hDX := Esc_decomp' σ τX s hs
  have hDY := Esc_decomp' σ τY s hs
  have hBeq : Bexp σ τX (rmask s) = Bexp σ τY (rmask s) := Bexp_congr σ τX τY _ hτeq
  -- energy_B
  have hBX : 2 * (((r + m : ℕ)) : ℝ) * (∑ l, Usig ρ c wt (σ l) + ∑ b, rmask s b * Usig ρ c wt (τX b))
      - (((r + m : ℕ)) : ℝ) ^ 2 * Irho ρ c wt + (((r + m : ℕ)) : ℝ) * Real.log ρ
      ≤ Bexp σ τX (rmask s) :=
    energy_B hNpos hρ c wt F.hm σ τX (rmask s) hmsk01 hmsum hpiX
  rw [hNc] at hBX
  -- node-sum bounds, free points
  have hE1 : ∀ l, Real.log (1 + 1 / ‖σ l‖) ≤ Real.log (1 + r / m0) := by
    intro l
    have hn : m0 / r ≤ ‖σ l‖ := by
      calc m0 / r ≤ -(σ l).re := hσneg l
        _ ≤ |(σ l).re| := neg_le_abs _
        _ ≤ ‖σ l‖ := Complex.abs_re_le_norm _
    have hpos : 0 < m0 / r := by positivity
    apply Real.log_le_log (by positivity)
    have h1 : 1 / ‖σ l‖ ≤ r / m0 := by
      have h2 := one_div_le_one_div_of_le hpos hn
      rwa [one_div_div] at h2
    linarith
  have hPX : PS σ τX ≤ ∑ l, ((r : ℝ) * Unu α (σ l)
      + (Real.log (1 + r / m0) + Real.log (1 + 2 * m / r))) := by
    unfold PS
    refine Finset.sum_le_sum (fun l _ => ?_)
    have h1 := sumS_X_le (hσneg' l) hr hm hL0.le hL
    have h2 := hE1 l
    unfold Unu
    simp only [hτX]
    linarith
  have hPY : PS σ τY ≤ ∑ l, ((r : ℝ) * Unu α (σ l)
      + (Real.log (1 + r / m0) + Real.log (1 + 2 * m / r))) := by
    unfold PS
    refine Finset.sum_le_sum (fun l _ => ?_)
    have h1 := sumS_Y_le (hσneg' l) hr hm hL0.le hL
    have h2 := hE1 l
    unfold Unu
    simp only [hτY]
    linarith
  -- node-sum bounds, removed nodes
  have hRX1 : ∀ b : Fin (r + m), ∑ b', rmask s b * elog (τX b) (τX b')
      ≤ rmask s b * ((r : ℝ) * Unu α (τX b) + (Real.log (1 + 2 * m) + w * |Real.log (2 * α)|)) := by
    intro b
    rw [← Finset.mul_sum]
    by_cases hb : rmask s b = 0
    · simp [hb]
    · have hb1 : (b : ℕ) < r := by
        by_contra h; exact hb (hmskr b (not_lt.1 h))
      have hb2 : rmask s b = 1 := (hmsk01 b).resolve_left hb
      rw [hb2, one_mul, one_mul]
      have ee : τX b = nodeC r (b : ℕ) := by simp only [hτX, xnode_lt r hb1]
      have h1 := sumR_X_leW hb1 hr hm hL0 hL hL2
      rw [ee]
      exact h1
  have hRY1 : ∀ b : Fin (r + m), ∑ b', rmask s b * elog (τY b) (τY b')
      ≤ rmask s b * ((r : ℝ) * Unu α (τX b) + (Real.log (1 + 2 * m) + w * |Real.log (2 * α)|)) := by
    intro b
    rw [← Finset.mul_sum]
    by_cases hb : rmask s b = 0
    · simp [hb]
    · have hb1 : (b : ℕ) < r := by
        by_contra h; exact hb (hmskr b (not_lt.1 h))
      have hb2 : rmask s b = 1 := (hmsk01 b).resolve_left hb
      rw [hb2, one_mul, one_mul]
      have ee : τX b = nodeC r (b : ℕ) := by simp only [hτX, xnode_lt r hb1]
      have ee' : τY b = nodeC r (b : ℕ) := by simp only [hτY, ynode_lt r hb1]
      have h1 := sumR_Y_leW hb1 hr hm hL0 hL hL2
      rw [ee, ee']
      exact h1
  have hmulsum : ∀ (f : Fin (r + m) → ℝ) (C1 C2 : ℝ),
      ∑ b, rmask s b * (C1 * f b + C2) = C1 * ∑ b, rmask s b * f b + C2 * ∑ b, rmask s b := by
    intro f C1 C2
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  have hRX : RS (rmask s) τX
      ≤ r * ∑ b, rmask s b * Unu α (τX b)
        + (Real.log (1 + 2 * m) + w * |Real.log (2 * α)|) * (((r : ℝ) + m) - k) := by
    unfold RS
    refine (Finset.sum_le_sum (fun b _ => hRX1 b)).trans (le_of_eq ?_)
    rw [hmulsum (fun b => Unu α (τX b)) (r : ℝ) _, hmsum']
  have hRY : RS (rmask s) τY
      ≤ r * ∑ b, rmask s b * Unu α (τX b)
        + (Real.log (1 + 2 * m) + w * |Real.log (2 * α)|) * (((r : ℝ) + m) - k) := by
    unfold RS
    refine (Finset.sum_le_sum (fun b _ => hRY1 b)).trans (le_of_eq ?_)
    rw [hmulsum (fun b => Unu α (τX b)) (r : ℝ) _, hmsum']
  -- self-energies
  have hAX : Alow r m ≤ AS τX := by
    have h1 : AS τX = ∑ a ∈ range (r + m), ∑ b ∈ range (r + m),
        elog (nodeC r (xnode r a)) (nodeC r (xnode r b)) := AS_eq_range r m (xnode r)
    rw [h1]; exact AX_ge hr hm
  have hAY : Alow r m - 2 * m * Real.log (r + 2 * m) ≤ AS τY := by
    have h1 : AS τY = ∑ a ∈ range (r + m), ∑ b ∈ range (r + m),
        elog (nodeC r (ynode r a)) (nodeC r (ynode r b)) := AS_eq_range r m (ynode r)
    rw [h1]; exact AY_ge hr hm
  -- pointwise g-bounds
  have hT : (N0 : ℝ) + Fr.n0off ≤ (F.r0 : ℝ) * r := by
    have h1 := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * r by positivity)
    rw [← hN0] at h1; push_cast at h1; exact h1
  have hfree : ∀ l, 2 * r * F.g (σ l) - 2 * (1 - ε) * Real.pi * |(z l).im| - 2 * w * A0
        - (4 * w * V / r) * |(z l).im|
      ≤ 2 * ((r : ℝ) + m) * Usig ρ c wt (σ l) - 2 * r * Unu α (σ l) := by
    intro l
    have hnorm : ‖σ l‖ ≤ (F.r0 : ℝ) + Fr.xs + (2 / r) * |(z l).im| := by
      have h1 := free_norm_le hFr.slope.one_le hxs.le hFr.atomRange hT (hz l)
      have h2 : ‖σ l‖ = ‖z l‖ / r := by
        show ‖z l / (r : ℂ)‖ = _
        rw [norm_div, Complex.norm_natCast]
      rw [h2, div_le_iff₀ hr']
      have h3 : ((F.r0 : ℝ) + Fr.xs + 2 / r * |(z l).im|) * r
          = F.r0 * r + Fr.xs * r + 2 * |(z l).im| := by field_simp
      rw [h3]
      nlinarith [h1, mul_le_mul_of_nonneg_left hr1 hxs.le]
    have hYl : -(A0 + (2 * V / r) * |(z l).im|) ≤ Usig ρ c wt (σ l) := by
      have h1 := Usig_ge_signed hρ c wt hwV hRc hc (σ l)
      have h2 := mul_le_mul_of_nonneg_left
        (show ‖σ l‖ + Rc + ρ + Lp ρ ≤ ((F.r0 : ℝ) + Fr.xs + (2 / r) * |(z l).im|) + Rc + ρ + Lp ρ
          by linarith) hV0
      have h3 : V * (((F.r0 : ℝ) + Fr.xs + (2 / r) * |(z l).im|) + Rc + ρ + Lp ρ)
          = A0 - V + (2 * V / r) * |(z l).im| := by rw [hA0def]; ring
      linarith
    refine pt_ineqWS (α := α) (w := w) (ε := ε) (U := Unu α (σ l)) hr' hδ0 hδ1 hδ' (abs_nonneg _) hA0 hV0 hYl ?_
    rw [hg (σ l), hσim, abs_div, abs_of_pos hr']
    ring
  have hline : ∀ b : Fin (r + m), rmask s b * (2 * r * F.gmin - 2 * w * A0)
      ≤ rmask s b * (2 * ((r : ℝ) + m) * Usig ρ c wt (τX b) - 2 * r * Unu α (τX b)) := by
    intro b
    by_cases hb : rmask s b = 0
    · simp [hb]
    · have hb1 : (b : ℕ) < r := by
        by_contra h; exact hb (hmskr b (not_lt.1 h))
      have hb2 : rmask s b = 1 := (hmsk01 b).resolve_left hb
      rw [hb2, one_mul, one_mul]
      have ee : τX b = nodeC r (b : ℕ) := by simp only [hτX, xnode_lt r hb1]
      have hb0 : (0 : ℝ) ≤ (b : ℝ) / r := by positivity
      have hb1' : (b : ℝ) / r ≤ 1 := by rw [div_le_one hr']; exact_mod_cast hb1.le
      have hgm : (F.gmin : ℝ) ≤ F.g (τX b) := by
        have h1 := F.g_line_ge hb0 hb1'
        have h2 : τX b = (⟨(b : ℝ) / r, 0⟩ : ℂ) := by
          rw [ee]; apply Complex.ext <;> simp [nodeC]
        rw [h2]; exact h1
      have hnb : ‖τX b‖ ≤ 1 := by
        rw [ee]
        have : nodeC r (b : ℕ) = (((b : ℝ) / r : ℝ) : ℂ) := rfl
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]; exact hb1'
      have hYl : -(A0 + (2 * V / r) * |(0 : ℝ)|) ≤ Usig ρ c wt (τX b) := by
        have h1 := Usig_ge_signed hρ c wt hwV hRc hc (τX b)
        have h2 := mul_le_mul_of_nonneg_left
          (show ‖τX b‖ + Rc + ρ + Lp ρ ≤ 1 + Rc + ρ + Lp ρ by linarith) hV0
        have h3 : 0 ≤ V * ((F.r0 : ℝ) + Fr.xs) := by positivity
        have h4 : A0 = V * (1 + Rc + ρ + Lp ρ) + V * ((F.r0 : ℝ) + Fr.xs) := by
          rw [hA0def]; ring
        simp only [abs_zero, mul_zero, add_zero]
        linarith
      have hgτ : F.g (τX b) = (1 + α) * Usig ρ c wt (τX b) - Unu α (τX b)
          + ((1 - ε) * Real.pi / r) * |(0 : ℝ)| := by
        rw [hg (τX b)]
        have h0 : (τX b).im = 0 := by rw [ee, nodeC_im]
        rw [h0]; simp
      have hpt := pt_ineqWS (α := α) (w := w) (ε := ε) (U := Unu α (τX b)) hr' hδ0 hδ1 hδ' (abs_nonneg _) hA0 hV0
        hYl hgτ
      simp only [abs_zero, mul_zero, sub_zero] at hpt
      nlinarith [hpt, hgm, mul_le_mul_of_nonneg_left hgm (by positivity : (0 : ℝ) ≤ 2 * r)]
  -- sums
  have hfreeSum : 2 * r * (∑ l, F.g (σ l)) - 2 * (1 - ε) * Real.pi * (∑ l, |(z l).im|)
        - k * (2 * w * A0) - (4 * w * V / r) * (∑ l, |(z l).im|)
      ≤ 2 * ((r : ℝ) + m) * (∑ l, Usig ρ c wt (σ l)) - 2 * r * (∑ l, Unu α (σ l)) := by
    have h1 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hfree l)
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  have hlineSum : (((r : ℝ) + m) - k) * (2 * r * F.gmin - 2 * w * A0)
      ≤ 2 * ((r : ℝ) + m) * (∑ b, rmask s b * Usig ρ c wt (τX b))
        - 2 * r * (∑ b, rmask s b * Unu α (τX b)) := by
    have h1 := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin (r + m)))) => hline b)
    rw [← Finset.sum_mul, hmsum'] at h1
    have h2 : ∀ b : Fin (r + m), rmask s b * (2 * ((r : ℝ) + m) * Usig ρ c wt (τX b)
        - 2 * r * Unu α (τX b))
        = 2 * ((r : ℝ) + m) * (rmask s b * Usig ρ c wt (τX b))
          - 2 * r * (rmask s b * Unu α (τX b)) := fun b => by ring
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
    exact h1
  have hlogq : ∑ l, Real.log (q l) ≤ (1 - e) * k * Cl
      - 2 * (1 - e) * Real.pi * ∑ l, |(z l).im| := by
    have h1 := Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin k))) => hq l)
    have h2 : ∀ l : Fin k, (1 - e) * (Cl - 2 * Real.pi * |(z l).im|)
        = (1 - e) * Cl - (2 * (1 - e) * Real.pi) * |(z l).im| := fun l => by ring
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h1
    linarith
  have hSB := Frame.lemmaBG hFr F hr hN0 hW z hzi hz
  have hPXs : ∑ l, ((r : ℝ) * Unu α (σ l) + (Real.log (1 + r / m0) + Real.log (1 + 2 * m / r)))
      = r * (∑ l, Unu α (σ l)) + k * (Real.log (1 + r / m0) + Real.log (1 + 2 * m / r)) := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hPXs] at hPX hPY
  -- scalar facts
  have hSI : 0 ≤ ∑ l, |(z l).im| := Finset.sum_nonneg (fun l _ => abs_nonneg _)
  have h4r : (4 * w * V / (r : ℝ)) * (∑ l, |(z l).im|)
      ≤ 2 * Real.pi * (ε - e) * (∑ l, |(z l).im|) := by
    apply mul_le_mul_of_nonneg_right _ hSI
    rw [div_le_iff₀ hr']
    nlinarith [hrbig]
  have hcc : (2 * r * F.mprime - r * F.ccert : ℝ) ≤ 2 * r * F.gmin := by
    have := F.ccert_ge
    nlinarith
  have hcc' := mul_le_mul_of_nonneg_left hcc (by linarith : (0 : ℝ) ≤ ((r : ℝ) + m) - k)
  have hSG' : 2 * (r : ℝ) * ((k : ℝ) * F.mprime + r * (Fr.d * F.Sbase)
      - Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ≤ 2 * r * ∑ l, F.g (σ l) :=
    mul_le_mul_of_nonneg_left hSB (by positivity)
  have hIb : ((r : ℝ) + m) ^ 2 * Irho ρ c wt ≤ ((r : ℝ) + m) ^ 2 * F.Ibound :=
    mul_le_mul_of_nonneg_left F.I_ok (by positivity)
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hE1nn : 0 ≤ Real.log (1 + r / m0) + Real.log (1 + 2 * m / r) := by
    have a1 : 0 ≤ Real.log (1 + (r : ℝ) / m0) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ r / m0 := by positivity
      linarith)
    have a2 : 0 ≤ Real.log (1 + 2 * (m : ℝ) / r) := Real.log_nonneg (by
      have : (0 : ℝ) ≤ 2 * m / r := by positivity
      linarith)
    linarith
  have hE2nn : 0 ≤ Real.log (1 + 2 * (m : ℝ)) + w * |Real.log (2 * α)| := by
    have a1 : 0 ≤ Real.log (1 + 2 * (m : ℝ)) := Real.log_nonneg (by linarith)
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ w) (abs_nonneg (Real.log (2 * α)))
    linarith
  have hkE1 := mul_le_mul_of_nonneg_right hkN' hE1nn
  have hkE2 := mul_le_mul_of_nonneg_right (by linarith : (((r : ℝ) + m) - k) ≤ (r : ℝ) + m) hE2nn
  have hkCl : (1 - e) * k * Cl ≤ ((r : ℝ) + m) * Cl := by
    have : (1 - e) * (k : ℝ) ≤ (r : ℝ) + m := by nlinarith
    exact mul_le_mul_of_nonneg_right this hCl
  have hlogρ : -Real.log ρ ≤ |Real.log ρ| := neg_le_abs _
  have hNlog := mul_le_mul_of_nonneg_left hlogρ hN'.le
  have hklogr : 0 ≤ 2 * (k : ℝ) * Real.log r := by positivity
  have hLX : Real.log (‖cexpr z rowC‖ ^ 2) = -(Esc σ (fun i => τX (s i)) + 2 * k * Real.log r) := by
    linarith
  have hLY : Real.log (‖cexpr z colC‖ ^ 2) = -(Esc σ (fun i => τY (s i)) + 2 * k * Real.log r) := by
    linarith
  unfold RerrRW
  rw [hLX, hLY]
  rw [hDX, hDY, ← hBeq]
  linarith [hBX, hPX, hPY, hRX, hRY, hAX, hAY, hfreeSum, hlineSum, hlogq, hSG', hIb, hcc', hkE1,
    hkE2, hkCl, hNlog, hklogr, h4r, hSI]
/-- The positive case: nonnegative weights of total mass one have presentation variation `V = 1`. -/
theorem sum_abs_le_one_of_nonneg {K : ℕ} {wt : Fin K → ℝ} (hw0 : ∀ k, 0 ≤ wt k)
    (hw1 : ∑ k, wt k = 1) : ∑ k, |wt k| ≤ 1 := by
  have : ∑ k, |wt k| = ∑ k, wt k := Finset.sum_congr rfl (fun k _ => abs_of_nonneg (hw0 k))
  rw [this, hw1]

end CatalanCore.Decay
