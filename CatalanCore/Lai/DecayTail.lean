module

public import CatalanCore.Decay.WedgeBounds
public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

/-!
# Lai decay, the tail and the atoms: instance numbers (LD08, LD16, LD17)

Theorem side only (no cell data).  Generic parts are `Decay.WedgeBounds` (`tail_wField_le`,
`atom_sup_le`, `omega_majorant`); this module adds

* a rational enclosure `vEnc` of the weight field `V = vField` at a rational point of the open upper
  half plane, built from the certified `LogEval` tools (`logQ`, `reClogQ`, `π`), with its soundness
  theorem `vEnc_spec`, for every design `(e, r, B, K)` and `θ = t π`;
* **LD17 / LD08 (Lemma T, Lai instance)** `lai_tail_decay`: for every finite `σ` of mass `3` carried by
  the disc `|2.1 - u| ≤ 2.091`, and every `y ≥ 3.3`,
  `W_σ(2.1 + i y) ≤ -130471/10000 - y/40`;
* **LD16 (atoms, Lai instance)** `lai_omega_curv` (`ω'' ≤ -8/5` on `(0, 6)`) and `lai_atom_bound`:
  `sup_{[0,6]} (ω - 2 U^σ(-x)) ≤ a(x*) + A²/(2 · 49/100)` at `x* = 2211/500`.

Say μ, never B, for the irrationality measure; `B` here is the design parameter of `vField`.
-/

namespace CatalanCore.Lai.DecayTail

open Complex Set MeasureTheory CatalanMeasure.GenD.Signed.LogEval CatalanCore.Decay.ComplexTaylor
  CatalanCore.Decay.WedgeBounds

noncomputable section

/-! ### enclosure arithmetic on pairs -/

def eAdd (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 + q.1, p.2 + q.2)
def eSub (p q : ℚ × ℚ) : ℚ × ℚ := (p.1 - q.1, p.2 + q.2)
def eMul (w : ℚ) (p : ℚ × ℚ) : ℚ × ℚ := (w * p.1, CatalanMeasure.Cert.qabs w * p.2)
def eConst (c : ℚ) : ℚ × ℚ := (c, 0)

theorem enc_pi : Enc Real.pi (4 * PI4, 4 * PI4E) := by
  have h := pi4_spec
  unfold Enc
  push_cast
  have : Real.pi - 4 * (PI4 : ℝ) = 4 * (Real.pi / 4 - (PI4 : ℝ)) := by ring
  rw [this, abs_mul]
  have h4 : |(4 : ℝ)| = 4 := abs_of_pos (by norm_num)
  rw [h4]
  linarith

/-- the weight field at a point of the upper half plane in closed form -/
theorem vField_closed (e r B K θ : ℝ) {s : ℂ} (hs : 0 < s.im) :
    vField e r B K θ s =
      (r * (K * Real.log K - K) - e * (B * Real.log B - B))
        + e * ((s * Complex.log s).re - ((s - (B : ℂ)) * Complex.log (s - (B : ℂ))).re - B)
        - r * (((s + (K : ℂ)) * Complex.log (s + (K : ℂ))).re - (s * Complex.log s).re - K)
        - θ * s.im := by
  unfold vField
  rw [integral_log_norm_sub hs B, integral_log_norm_add hs K, abs_of_pos hs]
  simp only [sub_zero, add_zero, Complex.sub_re, Complex.neg_re, Complex.add_re, Complex.ofReal_re]
  ring

theorem vField_sub_theta (e r B K θ θ' : ℝ) (s : ℂ) :
    vField e r B K θ' s = vField e r B K θ s + (θ - θ') * |s.im| := by
  unfold vField; ring

theorem wField_sub_theta (e r B K θ θ' : ℝ) (σ : Measure ℂ) (s : ℂ) :
    wField e r B K θ' σ s = wField e r B K θ σ s + (θ - θ') * |s.im| := by
  unfold wField; rw [vField_sub_theta e r B K θ θ']; ring

/-- Enclosure of `vField e r B K (t π) (x + y i)` (`y > 0`), `nL`/`nA` the log / arctan series lengths. -/
def vEnc (nL nA : ℕ) (e r B K t x y : ℚ) : Option (ℚ × ℚ) :=
  match logQ nL K, logQ nL B, reClogQ nL nA (x - B) y (x - B) y, reClogQ nL nA x y x y,
      reClogQ nL nA (x + K) y (x + K) y with
  | some pK, some pB, some p1, some p0, some p2 =>
    some (eSub (eSub (eAdd (eSub (eMul r (eSub (eMul K pK) (eConst K)))
        (eMul e (eSub (eMul B pB) (eConst B))))
        (eMul e (eSub (eSub p0 p1) (eConst B))))
        (eMul r (eSub (eSub p2 p0) (eConst K))))
        (eMul (t * y) (4 * PI4, 4 * PI4E)))
  | _, _, _, _, _ => none

theorem vEnc_spec {nL nA : ℕ} {e r B K t x y : ℚ} {p : ℚ × ℚ} (hy : 0 < y)
    (h : vEnc nL nA e r B K t x y = some p) :
    Enc (vField (e : ℝ) (r : ℝ) (B : ℝ) (K : ℝ) ((t : ℝ) * Real.pi)
      (⟨(x : ℝ), (y : ℝ)⟩ : ℂ)) p := by
  unfold vEnc at h
  split at h
  · rename_i pK pB p1 p0 p2 hK hB h1 h0 h2
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨_, eK⟩ := logQ_spec hK
    obtain ⟨_, eB⟩ := logQ_spec hB
    obtain ⟨_, e1⟩ := reClogQ_spec h1
    obtain ⟨_, e0⟩ := reClogQ_spec h0
    obtain ⟨_, e2⟩ := reClogQ_spec h2
    set s : ℂ := ⟨(x : ℝ), (y : ℝ)⟩ with hs
    have hsim : 0 < s.im := by simp [hs]; exact_mod_cast hy
    have hw1 : s - ((B : ℝ) : ℂ) = ⟨(((x - B : ℚ)) : ℝ), (y : ℝ)⟩ :=
      Complex.ext (by simp [hs]) (by simp [hs])
    have hw2 : s + ((K : ℝ) : ℂ) = ⟨(((x + K : ℚ)) : ℝ), (y : ℝ)⟩ :=
      Complex.ext (by simp [hs]) (by simp [hs])
    have hw0 : s = ⟨(((x : ℚ)) : ℝ), (y : ℝ)⟩ := rfl
    rw [vField_closed _ _ _ _ _ hsim, hw1, hw2]
    have hs0 : (s * Complex.log s).re = (({ re := ((x : ℚ) : ℝ), im := ((y : ℚ) : ℝ) } : ℂ) *
        Complex.log { re := ((x : ℚ) : ℝ), im := ((y : ℚ) : ℝ) }).re := rfl
    have hsi : s.im = (y : ℝ) := rfl
    rw [hs0, hsi]
    have hθ : (t : ℝ) * Real.pi * (y : ℝ) = ((t * y : ℚ) : ℝ) * Real.pi := by push_cast; ring
    rw [hθ]
    have eKK := (Enc.mulQ r ((Enc.mulQ K eK).sub (Enc.const K)))
    have eBB := (Enc.mulQ e ((Enc.mulQ B eB).sub (Enc.const B)))
    have eI := Enc.mulQ e (((e0.sub e1).sub (Enc.const B)))
    have eJ := Enc.mulQ r (((e2.sub e0).sub (Enc.const K)))
    have eP := Enc.mulQ (t * y) enc_pi
    exact (((eKK.sub eBB).add eI).sub eJ).sub eP
  · simp at h

/-! ### LD17 / LD08: the tail on the ray `x₁ = 21/10`, `y ≥ y₁ = 33/10` -/

/-- Checker: `V(2.1 + 3.3 i) + 6 log 5.391 + 33/400 ≤ ℓ = -130471/10000`, with `V` at `θ = 2π`. -/
def laiTailOK : Bool :=
  match vEnc 4 4 3 2 2 6 2 (21 / 10) (33 / 10), logQ 4 (5391 / 1000) with
  | some (v, ev), some (l, el) =>
      decide (v + ev + 6 * (l + el) + (1 / 40) * (33 / 10) ≤ -130471 / 10000)
  | _, _ => false

-- kcost: 1.85 s measured (5 reClogQ/logQ at series length 4 + 1 logQ, one declaration)
theorem laiTailOK_true : laiTailOK = true := by decide +kernel

theorem laiTail_numeric :
    vField 3 2 2 6 (2 * Real.pi) (((21 / 10 : ℝ) : ℂ) + ((33 / 10 : ℝ) : ℂ) * I)
      + 6 * Real.log (5391 / 1000) + 33 / 400 ≤ -130471 / 10000 := by
  have h := laiTailOK_true
  unfold laiTailOK at h
  split at h
  · rename_i v ev l el hv hl
    have hs := vEnc_spec (nL := 4) (nA := 4) (by norm_num : (0 : ℚ) < 33 / 10) hv
    obtain ⟨_, hl'⟩ := logQ_spec hl
    have h1 := hs.le_upper
    have h2 := hl'.le_upper
    simp only [decide_eq_true_eq] at h
    push_cast at h1 h2
    rw [Complex.mk_eq_add_mul_I] at h1
    push_cast at h1
    have hh : ((v + ev + 6 * (l + el) + 1 / 40 * (33 / 10) : ℚ) : ℝ) ≤ ((-130471 / 10000 : ℚ) : ℝ) :=
      by exact_mod_cast h
    push_cast at hh
    norm_num at h1 h2 hh ⊢
    linarith
  · simp at h

theorem lai_tail_decay {σ : Measure ℂ} [IsFiniteMeasure σ] (hmass : σ.real univ = 3)
    (hsupp : ∀ᵐ u ∂σ, ‖(((21 / 10 : ℝ)) : ℂ) - u‖ ≤ 2091 / 1000)
    (hint : ∀ y : ℝ, 33 / 10 ≤ y →
      Integrable (fun u => Real.log ‖(((21 / 10 : ℝ)) : ℂ) + y * I - u‖) σ)
    {y : ℝ} (hy : 33 / 10 ≤ y) :
    wField 3 2 2 6 (2 * Real.pi) σ ((((21 / 10 : ℝ)) : ℂ) + y * I) ≤
      -130471 / 10000 - (1 / 40) * y := by
  have hpi := Real.pi_gt_d2
  have hneg : (3 + 2 : ℝ) * (21 / 10) / (33 / 10) - (2 * Real.pi - 1 / 40) +
      2 * σ.real univ / (33 / 10 + 2091 / 1000) ≤ 0 := by
    rw [hmass]; norm_num; linarith
  have key := tail_wField_le 3 2 2 6 (2 * Real.pi - 1 / 40) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (σ := σ) (x₁ := 21 / 10) (y₁ := 33 / 10) (R₀ := 2091 / 1000) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hsupp hint hneg hy
  rw [wField_sub_theta 3 2 2 6 (2 * Real.pi) (2 * Real.pi - 1 / 40) σ,
    vField_sub_theta 3 2 2 6 (2 * Real.pi) (2 * Real.pi - 1 / 40)] at key
  have hy0 : 0 ≤ y := by linarith
  have him : |((((21 / 10 : ℝ)) : ℂ) + y * I).im| = y := by
    simp [abs_of_nonneg hy0]
  have him1 : |((((21 / 10 : ℝ)) : ℂ) + ((33 / 10 : ℝ) : ℂ) * I).im| = 33 / 10 := by
    simp; norm_num
  rw [him, him1, hmass] at key
  have hnum := laiTail_numeric
  norm_num at key hnum ⊢
  linarith

/-! ### LD16: atoms by strong concavity at `x* = 2211/500` -/

theorem lai_omega_curv : ∀ x ∈ Ioo (0 : ℝ) 6, omegaD2 3 2 2 6 x ≤ -(8 / 5) := by
  intro x hx
  obtain ⟨h0, h6⟩ := hx
  unfold omegaD2
  have h6x : 0 < 6 - x := by linarith
  have h2x : 0 < 2 + x := by linarith
  have key : -2 / x - 2 / (6 - x) + 3 / (2 + x) - 3 / x + 8 / 5 ≤ 0 := by
    have e : -2 / x - 2 / (6 - x) + 3 / (2 + x) - 3 / x + 8 / 5 =
        (-8 * x ^ 3 + 32 * x ^ 2 + 66 * x - 300) / (5 * x * (6 - x) * (2 + x)) := by
      field_simp; ring
    rw [e]
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [sq_nonneg (x - 7 / 2), mul_pos h0 h6x, mul_pos (mul_pos h0 h6x) h2x,
        sq_nonneg (x - 3), mul_pos h0 h0]
    · positivity
  linarith

/-- **LD16 (Lai atoms).**  For a finite `σ` of mass `3` carried by `Re u ≥ 8/5`, with `a0` an upper bound of
`a(x*) = ω(x*) + 2 ∫ log |x* + u| dσ` and `A ≥ |a'(x*)|` at `x* = 2211/500`:
`ω(x) + 2 ∫ log |x + u| dσ ≤ a0 + A² / (2 · 49/100)` on `[0, 6]`. -/
theorem lai_atom_bound {σ : Measure ℂ} [IsFiniteMeasure σ] (hmass : σ.real univ = 3)
    (hsupp : ∀ᵐ u ∂σ, (8 / 5 : ℝ) ≤ u.re)
    (hint : ∀ x ∈ Icc (0 : ℝ) 6, Integrable (fun u => Real.log ‖(x : ℂ) + u‖) σ)
    (hint1 : Integrable (fun u => ln1 u (2211 / 500)) σ) {a0 A : ℝ}
    (ha0 : omegaF 3 2 2 6 (2211 / 500) + 2 * ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂σ ≤ a0)
    (hA : |omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂σ| ≤ A) :
    ∀ x ∈ Icc (0 : ℝ) 6,
      omegaF 3 2 2 6 x + 2 * ∫ u, Real.log ‖(x : ℂ) + u‖ ∂σ ≤ a0 + A ^ 2 / (2 * (49 / 100)) := by
  have hmaj := omega_majorant 3 2 2 6 (M₁ := 8 / 5) (xs := 2211 / 500) (by norm_num)
    (by constructor <;> norm_num) lai_omega_curv
  have hm : 0 < 8 / 5 - 2 * (1 / (8 * (8 / 5 : ℝ) ^ 2)) * σ.real univ := by
    rw [hmass]; norm_num
  have h := atom_sup_le (σ := σ) (vmin := 8 / 5) (K' := 6) (xs := 2211 / 500) (M₁ := 8 / 5)
    (by norm_num) (by norm_num) (by constructor <;> norm_num) hsupp hint hint1
    (ω := omegaF 3 2 2 6) (ω' := omegaD1 3 2 2 6 (2211 / 500)) hmaj hm
  intro x hx
  have h1 := h x hx
  have hmv : 2 * (8 / 5 - 2 * (1 / (8 * (8 / 5 : ℝ) ^ 2)) * σ.real univ) ≥ 2 * (49 / 100) := by
    rw [hmass]; norm_num
  have hsq : (omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂σ) ^ 2 ≤ A ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hA 2
  have h2 : (omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂σ) ^ 2 /
      (2 * (8 / 5 - 2 * (1 / (8 * (8 / 5 : ℝ) ^ 2)) * σ.real univ)) ≤ A ^ 2 / (2 * (49 / 100)) := by
    calc _ ≤ A ^ 2 / (2 * (8 / 5 - 2 * (1 / (8 * (8 / 5 : ℝ) ^ 2)) * σ.real univ)) :=
          div_le_div_of_nonneg_right hsq (by linarith)
      _ ≤ A ^ 2 / (2 * (49 / 100)) :=
          div_le_div_of_nonneg_left (sq_nonneg A) (by norm_num) hmv
  linarith

end

end CatalanCore.Lai.DecayTail
