module

public import CatalanCore.Uniform.Decay.FarField.Agg
public import CatalanCore.Uniform.Decay.FarField.Near

@[expose] public section
set_option Elab.async false

/-!
# The far-field cell (lane D, package D15)

`mpCellOk M zc dd h W cpi m' rm rh` certifies, for every `z = zc + s·dd + δ` with `|s| ≤ h`, `|δ| ≤ W`,
`m' ≤ -∑ w_P Φ_P(z) + cpi · |Im z|`, from the exact moments `M.mu` of the measure about `M.c`:

* `rm ≤ ‖zc - c‖`, `‖dd‖ h ≤ rh`, `vr = rh + W < rm`, `a = vr/rm`, `r0 = rm - vr > R`;
* `S0 = ∑_{k<J} μ_{k+1} w^(k+1)/(k+1)`, `S1 = ∑_{k<J} μ_{k+1} w^(k+2)` with `w = 1/(zc-c)`;
* the value is `cpi y0 + Re S0 - lin - quad - tail - rem` with `lin` the first-order change,
  `quad` the second-order remainder of the first `J` terms (`tb`), `tail` the terms `J+1..K`
  bounded by `|μ_k|/(k r0^k)`, and `rem` the truncation remainder.
-/

namespace CatalanCore.Uniform.Decay.FarField

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.NearCells

def nrm (z : CQ) : ℚ := |z.re| + |z.im|

theorem norm_le_nrm (z : CQ) : ‖z.toC‖ ≤ (nrm z : ℝ) := by
  have := Complex.norm_le_abs_re_add_abs_im z.toC
  simpa [nrm, CQ.toC] using this

def mpS0 (mu wp : List CQ) (J : ℕ) : CQ :=
  CQ.sumTo (fun k => CQ.smul (1 / ((k : ℚ) + 1)) (CQ.mul (mu.getD k CQ.zero) (wp.getD (k + 1) CQ.zero))) J

def mpS1 (mu wp : List CQ) (J : ℕ) : CQ :=
  CQ.sumTo (fun k => CQ.mul (mu.getD k CQ.zero) (wp.getD (k + 2) CQ.zero)) J

def mpLin (S1 dd : CQ) (h W : ℚ) : ℚ := h * |(CQ.mul S1 dd).re| + W * |S1.re|

def mpQuad (mu : List CQ) (J : ℕ) (rm a : ℚ) : ℚ :=
  lsum (fun k => nrm (mu.getD k CQ.zero) / (((k : ℚ) + 1) * rm ^ (k + 1)) * tb a (k + 1)) J * a ^ 2

def mpTail (mu : List CQ) (J K : ℕ) (r0 : ℚ) : ℚ :=
  lsum (fun j => nrm (mu.getD (J + j) CQ.zero) / ((((J + j : ℕ) : ℚ) + 1) * r0 ^ (J + j + 1))) (K - J)

def mpRem (Aabs R r0 : ℚ) (K : ℕ) : ℚ :=
  Aabs * ((R / r0) ^ (K + 1) / (((K : ℚ) + 1) * (1 - R / r0)))

/-- The Boolean of one far-field cell. -/
def mpCellOk (M : MPData) (zc dd : CQ) (h W cpi m' rm rh : ℚ) : Bool :=
  let u0 := CQ.sub zc M.c
  let vr := rh + W
  let a := vr / rm
  let r0 := rm - vr
  let wp := powsFrom (CQ.inv u0) CQ.one (M.J + 2)
  let S0 := mpS0 M.mu wp M.J
  let S1 := mpS1 M.mu wp M.J
  let y0 := zc.im - h * |dd.im|
  decide (0 < h) && decide (0 ≤ W) && decide (0 < rm) && decide (rm * rm ≤ u0.nsq) &&
    decide (0 ≤ rh) && decide (dd.nsq * h ^ 2 ≤ rh ^ 2) && decide (vr < rm) && decide (M.R < r0) &&
    decide (0 ≤ cpi) && decide (0 ≤ y0) &&
    decide (m' ≤ cpi * y0 + S0.re - mpLin S1 dd h W - mpQuad M.mu M.J rm a
      - mpTail M.mu M.J M.K r0 - mpRem M.Aabs M.R r0 M.K)

theorem toC_mpS0 (mu wp : List CQ) (J : ℕ) (u0 : CQ) (hu : u0.nsq ≠ 0) (hwp : wp = powsFrom (CQ.inv u0) CQ.one (J + 2)) :
    (mpS0 mu wp J).toC = ∑ k ∈ range J, (mu.getD k CQ.zero).toC * (u0.toC)⁻¹ ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
  unfold mpS0
  rw [CQ.toC_sumTo]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [CQ.toC_smul, CQ.toC_mul, hwp, powsFrom_getD _ _ _ _ (by omega), CQ.toC_one, CQ.toC_inv _ hu]
  push_cast
  ring

theorem toC_mpS1 (mu wp : List CQ) (J : ℕ) (u0 : CQ) (hu : u0.nsq ≠ 0) (hwp : wp = powsFrom (CQ.inv u0) CQ.one (J + 2)) :
    (mpS1 mu wp J).toC = ∑ k ∈ range J, (mu.getD k CQ.zero).toC * (u0.toC)⁻¹ ^ (k + 2) := by
  unfold mpS1
  rw [CQ.toC_sumTo]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  rw [CQ.toC_mul, hwp, powsFrom_getD _ _ _ _ (by omega), CQ.toC_one, CQ.toC_inv _ hu]
  ring

/-- **Soundness of the far-field cell.** -/
theorem mpCellOk_sound {ps : List WP} {M : MPData} (hG : mpGlobalOk ps M = true)
    {zc dd : CQ} {h W cpi m' rm rh : ℚ} (hc : mpCellOk M zc dd h W cpi m' rm rh = true)
    (s δ : ℝ) (hs : |s| ≤ h) (hδ : |δ| ≤ W) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)))).sum
      + (cpi : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
  obtain ⟨hR, hJK, hmu, hmass, hAabs, hP⟩ := mpGlobalOk_sound hG
  simp only [mpCellOk, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hh, hW⟩, hrm⟩, hrm2⟩, hrh⟩, hdd⟩, hvr⟩, hRr⟩, hcpi⟩, hy0⟩, hfin⟩ := hc
  set u0 : CQ := CQ.sub zc M.c with hu0def
  set vr : ℚ := rh + W with hvrdef
  set a : ℚ := vr / rm with hadef
  set r0 : ℚ := rm - vr with hr0def
  set wp : List CQ := powsFrom (CQ.inv u0) CQ.one (M.J + 2) with hwpdef
  -- real versions of the hypotheses
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hWR : (0 : ℝ) ≤ W := by exact_mod_cast hW
  have hrmR : (0 : ℝ) < rm := by exact_mod_cast hrm
  have hvrR : (vr : ℝ) < rm := by exact_mod_cast hvr
  have hr0R : (r0 : ℝ) = rm - vr := by rw [hr0def]; push_cast; ring
  have hRrR : (M.R : ℝ) < r0 := by exact_mod_cast hRr
  have hR0 : (0 : ℝ) ≤ M.R := by exact_mod_cast hR
  -- the displacement
  set η : ℂ := (s : ℂ) * dd.toC + (δ : ℂ) with hηdef
  have hddn : ‖dd.toC‖ * (h : ℝ) ≤ rh := norm_le_of_nsq hh.le hrh hdd
  have hηn : ‖η‖ ≤ (vr : ℝ) := by
    rw [hηdef]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hvrdef]
    push_cast
    have hs' : |s| ≤ (h : ℝ) := hs
    have h1 : |s| * ‖dd.toC‖ ≤ (h : ℝ) * ‖dd.toC‖ := mul_le_mul_of_nonneg_right hs' (norm_nonneg _)
    nlinarith [hδ, hddn]
  -- the point
  have hzdef : zc.toC + (s : ℂ) * dd.toC + (δ : ℂ) = zc.toC + η := by rw [hηdef]; ring
  have hu0C : u0.toC = zc.toC - M.c.toC := by rw [hu0def, CQ.toC_sub]
  have hnu0 : ‖u0.toC‖ ≥ (rm : ℝ) := by
    have h1 : (rm : ℝ) * rm ≤ (u0.nsq : ℝ) := by exact_mod_cast hrm2
    have h2 : ‖u0.toC‖ ^ 2 = (u0.nsq : ℝ) := by rw [Complex.sq_norm, ← CQ.nsq_cast]
    by_contra hcon
    push_neg at hcon
    nlinarith [norm_nonneg u0.toC]
  have hu0ns : u0.nsq ≠ 0 := by
    intro h0
    have h1 : (rm : ℝ) * rm ≤ (u0.nsq : ℝ) := by exact_mod_cast hrm2
    rw [h0] at h1; simp at h1; nlinarith
  have hzu : zc.toC + η - M.c.toC = u0.toC + η := by rw [hu0C]; ring
  have hzn : (r0 : ℝ) ≤ ‖zc.toC + η - M.c.toC‖ := by
    rw [hzu, hr0R]
    have := norm_sub_norm_le u0.toC (-η)
    rw [sub_neg_eq_add, norm_neg] at this
    linarith
  -- aggregated expansion
  have hagg := agg_far hG (zc.toC + η) r0 hRrR hzn
  rw [hzu] at hagg
  -- split the sum at J
  obtain ⟨d, hd⟩ : ∃ d, M.K = M.J + d := ⟨M.K - M.J, by omega⟩
  have hdd' : M.K - M.J = d := by omega
  set f : ℕ → ℂ := fun k => (M.mu.getD k CQ.zero).toC / (((k + 1 : ℕ) : ℂ) * (u0.toC + η) ^ (k + 1)) with hf
  have hsplit : ∑ k ∈ range M.K, f k = ∑ k ∈ range M.J, f k + ∑ j ∈ range d, f (M.J + j) := by
    rw [hd]; exact Finset.sum_range_add f M.J d
  -- tail bound
  have htail : |(∑ j ∈ range d, f (M.J + j)).re| ≤ (mpTail M.mu M.J M.K r0 : ℝ) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans ?_
    unfold mpTail
    rw [lsum_eq, hdd']
    push_cast
    refine Finset.sum_le_sum fun j _ => ?_
    simp only [hf]
    rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
    have hn : (r0 : ℝ) ≤ ‖u0.toC + η‖ := by rw [← hzu]; exact hzn
    have hr0pos : (0 : ℝ) < r0 := by linarith
    have hpow : (r0 : ℝ) ^ (M.J + j + 1) ≤ ‖u0.toC + η‖ ^ (M.J + j + 1) :=
      pow_le_pow_left₀ hr0pos.le hn _
    have hnum := norm_le_nrm (M.mu.getD (M.J + j) CQ.zero)
    have hpos : (0 : ℝ) < ((M.J + j + 1 : ℕ) : ℝ) := by positivity
    have hnorm0 : 0 ≤ ‖(M.mu.getD (M.J + j) CQ.zero).toC‖ := norm_nonneg _
    push_cast
    calc ‖(M.mu.getD (M.J + j) CQ.zero).toC‖ / (((M.J : ℝ) + j + 1) * ‖u0.toC + η‖ ^ (M.J + j + 1))
        ≤ (nrm (M.mu.getD (M.J + j) CQ.zero) : ℝ) / (((M.J : ℝ) + j + 1) * (r0 : ℝ) ^ (M.J + j + 1)) := by
          apply div_le_div₀ ((norm_nonneg _).trans hnum) hnum (by positivity)
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by push_cast; ring
  -- near part
  have hnear := near_sum_bound M.J (fun k => (M.mu.getD k CQ.zero).toC)
    (fun k => (nrm (M.mu.getD k CQ.zero) : ℝ)) u0.toC η rm vr hrm hnu0 hηn hvr
    (fun k _ => norm_le_nrm _)
  have hS0 := toC_mpS0 M.mu wp M.J u0 hu0ns rfl
  have hS1 := toC_mpS1 M.mu wp M.J u0 hu0ns rfl
  rw [← hS0, ← hS1] at hnear
  -- the linear term
  have hlin : |((mpS1 M.mu wp M.J).toC * η).re| ≤ (mpLin (mpS1 M.mu wp M.J) dd h W : ℝ) := by
    set S1 := mpS1 M.mu wp M.J with hS1def
    have e : (S1.toC * η).re = s * (CQ.mul S1 dd).re + δ * S1.re := by
      rw [hηdef, mul_add, Complex.add_re, ← mul_assoc, mul_comm S1.toC (s : ℂ), mul_assoc,
        Complex.re_ofReal_mul]
      rw [← CQ.toC_mul, mul_comm S1.toC (δ : ℂ), Complex.re_ofReal_mul, CQ.toC_re]
      simp [CQ.toC_re]
    rw [e]
    unfold mpLin
    push_cast
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have hs' : |s| ≤ (h : ℝ) := hs
    have hδ' : |δ| ≤ (W : ℝ) := hδ
    have hre1 : |((CQ.mul S1 dd).re : ℝ)| = |((CQ.mul S1 dd).re : ℚ)| := by push_cast; rfl
    gcongr
  -- the imaginary part
  have him : (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im = (zc.im : ℝ) + s * (dd.im : ℝ) := by
    simp [CQ.toC]
  have hy : (zc.im : ℝ) - h * |(dd.im : ℝ)| ≤ (zc.im : ℝ) + s * dd.im := by
    have h1 : |s * (dd.im : ℝ)| ≤ h * |(dd.im : ℝ)| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    have := (abs_le.1 h1).1
    linarith
  have hy0R : (0 : ℝ) ≤ (zc.im : ℝ) - h * |(dd.im : ℝ)| := by exact_mod_cast hy0
  have hcpiR : (0 : ℝ) ≤ cpi := by exact_mod_cast hcpi
  have habs : (zc.im : ℝ) - h * |(dd.im : ℝ)| ≤ |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
    rw [him]; exact hy.trans (le_abs_self _)
  have hfinR : (m' : ℝ) ≤ cpi * (zc.im - h * |dd.im|) + ((mpS0 M.mu wp M.J).re : ℝ)
      - (mpLin (mpS1 M.mu wp M.J) dd h W : ℝ) - (mpQuad M.mu M.J rm a : ℝ)
      - (mpTail M.mu M.J M.K r0 : ℝ) - (mpRem M.Aabs M.R r0 M.K : ℝ) := by
    exact_mod_cast hfin
  -- assemble
  have hquad : (mpQuad M.mu M.J rm a : ℝ) =
      (∑ k ∈ range M.J, (nrm (M.mu.getD k CQ.zero) : ℝ) / (((k + 1 : ℕ) : ℝ) * (rm : ℝ) ^ (k + 1))
        * (tb (vr / rm) (k + 1) : ℝ)) * ((vr / rm : ℚ) : ℝ) ^ 2 := by
    rw [hadef]
    unfold mpQuad
    rw [lsum_eq]
    push_cast
    rfl
  have hrem : (mpRem M.Aabs M.R r0 M.K : ℝ)
      = (M.Aabs : ℝ) * (((M.R : ℝ) / r0) ^ (M.K + 1) / ((M.K + 1) * (1 - (M.R : ℝ) / r0))) := by
    unfold mpRem; push_cast; ring
  rw [hzdef]
  rw [hzdef] at habs
  have hre0 : ((mpS0 M.mu wp M.J).toC).re = ((mpS0 M.mu wp M.J).re : ℝ) := CQ.toC_re _
  rw [hsplit, Complex.add_re] at hagg
  beta_reduce at hnear
  have h1 := (abs_le.1 hagg).1
  have h2 := (abs_le.1 hnear).1
  have h3 := (abs_le.1 htail).1
  have h4 := (abs_le.1 hlin).2
  rw [hre0] at h2
  rw [hquad] at hfinR
  rw [hrem] at hfinR
  have h5 := mul_le_mul_of_nonneg_left habs hcpiR
  have hS0re : ((mpS0 M.mu wp M.J).toC).re = ((mpS0 M.mu wp M.J).re : ℝ) := hre0
  have hfJ : (∑ k ∈ range M.J, f k).re = (∑ k ∈ range M.J, (M.mu.getD k CQ.zero).toC /
      (((k + 1 : ℕ) : ℂ) * (u0.toC + η) ^ (k + 1))).re := rfl
  simp only [Rat.cast_abs] at hfinR
  linarith

end CatalanCore.Uniform.Decay.FarField
