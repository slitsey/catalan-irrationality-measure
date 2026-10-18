import CatalanLambda.Decay.ThmNLemmaB

/-!
# Theorem N_ρ: Lemma A_ρ (pointwise energy bound for a configuration)
-/

open Finset

namespace CatalanLambda.Decay

/-- The explicit error term `R(h)` of Lemma A_ρ (an `O(h log h)` quantity). -/
noncomputable def Rerr (h : ℕ) (Γ ρ Cl : ℝ) : ℝ :=
  4 * h * Γ + h * |Real.log ρ| + 2 * h * Real.log h + 3 * h + 1 / 2
    + 2 * h * Real.log (1 + 8 * h / 3) + h * Cl

theorem arith_core (h k Cl ε SIm G Rm Γ Ib D Sc mp gm cc I lr Lh L1 Sq LC : ℝ)
    (hh : 0 < h) (hk0 : 0 ≤ k) (hkh : k ≤ h) (hCl : 0 ≤ Cl) (hε1 : ε < 1) (hε0 : 0 < ε)
    (hL1 : 0 ≤ L1) (hLh : 0 ≤ Lh)
    (hE : 2 * h * (G + Rm) - 2 * ((1 - ε) * SIm) - h ^ 2 * I + h * lr + 3 / 2 * h ^ 2
        - 2 * h * Lh - 3 * h - 1 / 2 - 2 * k * L1 + 2 * k * Lh ≤ -LC)
    (hfield : Sq ≤ (1 - ε) * (k * Cl) - 2 * ((1 - ε) * SIm))
    (hB : k * mp + h * Sc - 2 * Γ ≤ G) (hrem : (h - k) * gm ≤ Rm) (hI : I ≤ Ib)
    (hD : D ≤ 2 * (mp + Sc) - Ib + 3 / 2) (hc : 2 * (mp - gm) ≤ cc) :
    Sq + LC ≤ -h ^ 2 * D + h * (h - k) * cc
      + (4 * h * Γ + h * |lr| + 2 * h * Lh + 3 * h + 1 / 2 + 2 * h * L1 + h * Cl) := by
  have p1 := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 2 * h by positivity)
  have p2 := mul_le_mul_of_nonneg_left hrem (show (0 : ℝ) ≤ 2 * h by positivity)
  have p3 := mul_le_mul_of_nonneg_left hI (show (0 : ℝ) ≤ h ^ 2 by positivity)
  have p4 : 0 ≤ h * (h - k) * (cc - 2 * (mp - gm)) :=
    mul_nonneg (mul_nonneg hh.le (by linarith)) (by linarith)
  have p5 := mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ h ^ 2 by positivity)
  have p6 : (1 - ε) * (k * Cl) ≤ h * Cl := by
    have : k * Cl ≤ h * Cl := mul_le_mul_of_nonneg_right hkh hCl
    have : (1 - ε) * (k * Cl) ≤ 1 * (k * Cl) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hk0 hCl)
    linarith
  have p7 : -h * lr ≤ h * |lr| := by
    have := neg_le_abs lr
    nlinarith
  have p8 : 2 * k * L1 ≤ 2 * h * L1 := by nlinarith [mul_le_mul_of_nonneg_right hkh hL1]
  have p9 : 0 ≤ 2 * k * Lh := by positivity
  nlinarith [hE, hfield, p1, p2, p3, p4, p5, p6, p7, p8, p9]

/-- **Lemma A_ρ.** For `h ≥ 5/(8W)`, any distinct free points `z_l` (atoms or ray points, with
`Re z_l ≤ -3/8`), any node family `s : Fin k → Fin h` injective, and weights `q` with
`log q_l ≤ (1-ε)(C - 2π |Im z_l|)`, `C ≥ 0`:

`∑ log q_l + log ‖C(z,s)‖² ≤ -h² D_cert + h (h-k) c_cert + R(h)`.  -/
theorem lemmaA {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertFacts K ρ ε c m)
    {h k : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h) (s : Fin k → Fin h)
    (hs : Function.Injective s) (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hz : ∀ l, IsAtom ⌊(F.r0 : ℝ) * h⌋₊ (z l) ∨ IsRay ⌊(F.r0 : ℝ) * h⌋₊ (z l))
    (hre : ∀ l, 3 / 8 ≤ -(z l).re) (q : Fin k → ℝ) (Cl : ℝ) (hCl : 0 ≤ Cl)
    (hq : ∀ l, Real.log (q l) ≤ (1 - ε) * (Cl - 2 * Real.pi * |(z l).im|)) :
    ∑ l, Real.log (q l) + Real.log (‖cexpr z (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2)
      ≤ -(h : ℝ) ^ 2 * F.Dcert + h * ((h : ℝ) - k) * F.ccert
        + Rerr h (∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ Cl := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hkh : k ≤ h := by simpa using Fintype.card_le_of_injective s hs
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (show (1 : ℝ) ≤ h by exact_mod_cast hh)
  have hlog1 : 0 ≤ Real.log (1 + 8 * (h : ℝ) / 3) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ 8 * h / 3 := by positivity
                        linarith)
  have hρ := F.hρ
  have hE := energy_A0 hh hρ c m F.hm s hs z hzi hre
  -- split g
  set Γ := ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 with hΓ
  have hB := lemmaB F hh hW z hzi hz
  -- sum of (U - Utau) at free points
  have hfree : ∑ l, (Usig ρ c m (z l / h) - Utau (z l / h))
      = ∑ l, gfun ρ ε c m (z l / h) - (1 - ε) * (∑ l, Real.pi * |(z l).im|) / h := by
    have : ∀ l, Usig ρ c m (z l / h) - Utau (z l / h)
        = gfun ρ ε c m (z l / h) - (1 - ε) * (Real.pi * |(z l).im|) / h := by
      intro l
      unfold gfun
      rw [Complex.div_natCast_im, abs_div, abs_of_pos hh']
      field_simp
      ring
    simp_rw [this, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  -- removed nodes
  set r := rmask s with hr
  have hr0 : ∀ b, 0 ≤ r b := fun b => by rcases rmask_cases s b with e | e <;> rw [hr, e] <;> norm_num
  have hrs : ∑ b, r b = (h : ℝ) - k := by
    have := sum_mask s hs (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_sub_distrib] at this
    simp only [hr]; linarith
  have hnode : ∀ b : Fin h, Usig ρ c m (nodeC h b) - Utau (nodeC h b)
      = gfun ρ ε c m (nodeC h b) := by
    intro b; unfold gfun nodeC; simp
  have hgnode : ∀ b : Fin h, (F.gmin : ℝ) ≤ gfun ρ ε c m (nodeC h b) := by
    intro b
    have h0 : (0 : ℝ) ≤ (b : ℝ) / h := by positivity
    have h1 : (b : ℝ) / h ≤ 1 := by
      rw [div_le_one hh']; exact_mod_cast b.2.le
    have := F.g_line_ge (x := (b : ℝ) / h) (by linarith) h1
    unfold nodeC
    convert this using 2
  have hremoved : (h - k : ℝ) * F.gmin ≤ ∑ b, r b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b)) := by
    simp_rw [hnode]
    calc (h - k : ℝ) * F.gmin = ∑ b, r b * F.gmin := by rw [← Finset.sum_mul, hrs]
      _ ≤ _ := Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hgnode b) (hr0 b))
  -- field term
  have hfield : ∑ l, Real.log (q l) ≤ (1 - ε) * (k * Cl - 2 * ∑ l, Real.pi * |(z l).im|) := by
    have := Finset.sum_le_sum (s := univ) (fun l _ => hq l)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have e : ∑ l : Fin k, 2 * Real.pi * |(z l).im| = 2 * ∑ l, Real.pi * |(z l).im| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [e] at this; exact this
  rw [hfree] at hE
  have hIb := F.I_ok
  have hD := F.Dcert_le
  have hc := F.ccert_ge
  have hmp : (F.mprime : ℝ) + 0 ≤ F.mprime := by linarith
  unfold Rerr
  have hε1 := F.hε1
  have hε0 := F.hε0
  set SIm := ∑ l, Real.pi * |(z l).im| with hSIm
  have hS0 : 0 ≤ SIm := Finset.sum_nonneg (fun l _ => by positivity)
  have e1 : (h : ℝ) * ((1 - ε) * SIm / h) = (1 - ε) * SIm := by field_simp
  set G := ∑ l, gfun ρ ε c m (z l / h) with hG
  set Rm := ∑ b, r b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b)) with hRm
  have hfin : 2 * h * (G - (1 - ε) * SIm / h + Rm) = 2 * h * (G + Rm) - 2 * ((1 - ε) * SIm) := by
    field_simp; ring
  rw [hfin] at hE
  have p10 : (1 - ε) * (k * Cl - 2 * SIm) = (1 - ε) * (k * Cl) - 2 * ((1 - ε) * SIm) := by ring
  rw [p10] at hfield
  exact arith_core (h : ℝ) (k : ℝ) Cl ε SIm G Rm Γ F.Ibound F.Dcert F.Scert F.mprime F.gmin F.ccert
    (Irho ρ c m) (Real.log ρ) (Real.log h) (Real.log (1 + 8 * h / 3)) (∑ l, Real.log (q l))
    (Real.log (‖cexpr z (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2)) hh' hk0 hkh' hCl hε1 hε0 hlog1
    hlogh hE hfield hB hremoved hIb hD hc

end CatalanLambda.Decay
