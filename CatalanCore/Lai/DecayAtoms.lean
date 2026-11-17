module

public import CatalanCore.Lai.DecayCheck

@[expose] public section

/-!
# `CatalanCore.Lai.DecayAtoms`: the atoms `ha0`, `hA`, `hρ` of the Lai decay datum at `x* = 2211/500` (T-energy)

With `s = -x*`, the segment `ν = segMeasure laiM laiH laiC 8` and its potential tower at the constant
curve `γ 0 = s`, `γ 1 = 1`, `γ i = 0` (`i ≥ 2`): `segTower_encQ` at a checked rational point `φ̃`
encloses `U^ν(s)` (`j = 0`) and `-Re S₁(s)` (`j = 1`); the elementary atoms `ω`, `ω'` are enclosed by
`logQ`.  Statements:
* `lai_ha0_closed`: `ω(x*) + 2 ∫ log ‖x* + u‖ dσ ≤ A0q`,
* `lai_hA_closed`: `|ω'(x*) + 2 ∫ ln1 u x* dσ| ≤ AAq`,
* `lai_hρ_closed`: `A0q + AAq²/(2·49/100) ≤ ℓ + 4294856306/10^8`.
-/

open Set Real Finset MeasureTheory
open CatalanCore.Zeta5.Potential CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.Cert CatalanMeasure.CellCert
  OAI.InternalCatalan CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Lai.DecayCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Lai.DecayTowerSeg CatalanCore.Lai.DecayTowerV
  CatalanCore.Lai.DecayGlue CatalanCore.Lai.DecayInstance CatalanCore.Lai.DecayCheck
  CatalanCore.Decay.WedgeBounds

namespace CatalanCore.Lai.DecayAtoms

noncomputable section

def MQ : CQ := ⟨737 / 400, 1067 / 1000⟩
def HQ : CQ := ⟨93 / 400, 1023 / 1000⟩
def sQ : CQ := ⟨-2211 / 500, 0⟩
/-- the rational point `φ̃ ≈ jphi ζ₀`, `ζ₀ = (-x* - M)/h` -/
def atP : SegQ := { hq := HQ, φq := ⟨(-2589172830214921 / 562949953421312 : ℚ), (793127661269837 / 70368744177664 : ℚ)⟩, cq := cqL, N := 8 }
def atY (i : ℕ) : CQ := if i = 1 then ⟨1, 0⟩ else ⟨0, 0⟩
def atYm (i : ℕ) : ℚ := if i = 1 then 1 else 0
def atR : ℚ := (13384694675799 / 1099511627776 : ℚ)
def atδ : ℚ := (1 / 1099511627776 : ℚ)
def atlo : ℚ := (1126449467 / 1073741824 : ℚ)
def atdq : ℚ := (2888063187 / 536870912 : ℚ)
def atL1 : ℚ × ℚ := (logQ 8 atP.hq.nsq).getD (0, 0)
def atL2 : ℚ × ℚ := (logQ 8 (atP.φq.nsq / 4)).getD (0, 0)
def lg (q : ℚ) : ℚ × ℚ := (logQ 8 q).getD (0, 0)
def T0q : ℚ := atP.Tq atL1.1 atL2.1 atY 0
def E0q : ℚ := atP.Te atL1.2 atL2.2 atdq atδ atYm 0
def T1q : ℚ := atP.Tq atL1.1 atL2.1 atY 1
def E1q : ℚ := atP.Te atL1.2 atL2.2 atdq atδ atYm 1
/-- enclosure of `ω(x*) = omegaF 3 2 2 6 x*`: value and error -/
def wFv : ℚ := 12 * (lg 6).1 - 2 * (2211 / 500) * (lg (2211 / 500)).1 -
  2 * (789 / 500) * (lg (789 / 500)).1 + 3 * (3211 / 500) * (lg (3211 / 500)).1 -
  3 * (2211 / 500) * (lg (2211 / 500)).1 - 6 * (lg 2).1
def wFe : ℚ := 12 * (lg 6).2 + 2 * (2211 / 500) * (lg (2211 / 500)).2 +
  2 * (789 / 500) * (lg (789 / 500)).2 + 3 * (3211 / 500) * (lg (3211 / 500)).2 +
  3 * (2211 / 500) * (lg (2211 / 500)).2 + 6 * (lg 2).2
/-- enclosure of `ω'(x*) = omegaD1 3 2 2 6 x*` -/
def wDv : ℚ := -5 * (lg (2211 / 500)).1 + 2 * (lg (789 / 500)).1 + 3 * (lg (3211 / 500)).1
def wDe : ℚ := 5 * (lg (2211 / 500)).2 + 2 * (lg (789 / 500)).2 + 3 * (lg (3211 / 500)).2
/-- the atoms, rounded up on a `2^-40` grid -/
def A0q : ℚ := (4109625665751 / 137438953472 : ℚ)
def AAq : ℚ := (1030321825 / 1099511627776 : ℚ)

theorem toC_MQ : MQ.toC = DecayInstance.laiM := by
  apply Complex.ext <;> simp [CQ.toC, MQ, DecayInstance.laiM]
theorem toC_HQ : HQ.toC = DecayInstance.laiH := by
  apply Complex.ext <;> simp [CQ.toC, HQ, DecayInstance.laiH]
theorem toC_sQ : sQ.toC = -((2211 / 500 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [CQ.toC, sQ] <;> ring

/-! ### Kernel checks -/

theorem at_num :
    1 < atR ∧ atR ^ 2 ≤ atP.φq.nsq ∧ 0 ≤ atδ ∧
      (sQ.sub (MQ.add (atP.hq.mul atP.ζ))).nsq ≤ atδ ^ 2 ∧ 0 ≤ atlo ∧ atlo ^ 2 ≤ atP.hq.nsq ∧
      0 < atdq ∧ atdq ≤ atlo * ((atR + atR⁻¹) / 2 - 1) - atδ ∧ atP.hq.nsq ≠ 0 := by
  -- kcost: 0.05 s measured (bound: module 18.5 s wall incl. import)
  decide +kernel

theorem at_logs :
    (logQ 8 atP.hq.nsq).isSome = true ∧ (logQ 8 (atP.φq.nsq / 4)).isSome = true ∧
      (logQ 8 6).isSome = true ∧ (logQ 8 (2211 / 500)).isSome = true ∧ (logQ 8 (789 / 500)).isSome = true ∧
      (logQ 8 (3211 / 500)).isSome = true ∧ (logQ 8 2).isSome = true := by
  -- kcost: 0.2 s measured (bound: module 18.5 s wall incl. import)
  decide +kernel

theorem a0_num : wFv + wFe - 4 * (T0q - E0q) ≤ A0q := by
  -- kcost: 0.3 s measured (bound: module 18.5 s wall incl. import)
  decide +kernel

theorem AA_num : |wDv + 4 * T1q| + wDe + 4 * E1q ≤ AAq := by
  -- kcost: 0.3 s measured (bound: module 18.5 s wall incl. import)
  decide +kernel

theorem rho_num : A0q + AAq ^ 2 / (2 * (49 / 100)) ≤ -130471 / 10000 + 4294856306 / 10 ^ 8 := by
  -- kcost: 0.02 s measured (bound: module 18.5 s wall incl. import)
  unfold A0q AAq; norm_num

/-! ### The logarithmic enclosures -/

theorem lg_enc {q : ℚ} (h : (logQ 8 q).isSome = true) :
    |Real.log (q : ℝ) - ((lg q).1 : ℝ)| ≤ ((lg q).2 : ℝ) := by
  obtain ⟨⟨v, e⟩, hv⟩ := Option.isSome_iff_exists.1 h
  have hs := (logQ_spec hv).2
  unfold lg
  rw [hv]
  unfold Enc at hs
  simpa using hs

theorem omegaF_enc : |omegaF 3 2 2 6 (2211 / 500) - (wFv : ℝ)| ≤ (wFe : ℝ) := by
  obtain ⟨_, _, h6, hx, h6x, h2x, h2⟩ := at_logs
  have e6 := lg_enc h6
  have ex := lg_enc hx
  have e6x := lg_enc h6x
  have e2x := lg_enc h2x
  have e2 := lg_enc h2
  push_cast at e6 ex e6x e2x e2
  unfold omegaF wFv wFe
  have a1 : Real.log (6 - 2211 / 500 : ℝ) = Real.log (789 / 500 : ℝ) := by norm_num
  have a2 : Real.log (2 + 2211 / 500 : ℝ) = Real.log (3211 / 500 : ℝ) := by norm_num
  have a3 : (2 + 2211 / 500 : ℝ) = 3211 / 500 := by norm_num
  have a4 : (6 - 2211 / 500 : ℝ) = 789 / 500 := by norm_num
  rw [a1, a2, a3, a4]
  push_cast
  rw [abs_le] at e6 ex e6x e2x e2 ⊢
  constructor <;> nlinarith [e6.1, e6.2, ex.1, ex.2, e6x.1, e6x.2, e2x.1, e2x.2, e2.1, e2.2]

theorem omegaD1_enc : |omegaD1 3 2 2 6 (2211 / 500) - (wDv : ℝ)| ≤ (wDe : ℝ) := by
  obtain ⟨_, _, h6, hx, h6x, h2x, h2⟩ := at_logs
  have ex := lg_enc hx
  have e6x := lg_enc h6x
  have e2x := lg_enc h2x
  push_cast at ex e6x e2x
  unfold omegaD1 wDv wDe
  have a1 : Real.log (6 - 2211 / 500 : ℝ) = Real.log (789 / 500 : ℝ) := by norm_num
  have a2 : Real.log (2 + 2211 / 500 : ℝ) = Real.log (3211 / 500 : ℝ) := by norm_num
  rw [a1, a2]
  push_cast
  rw [abs_le] at ex e6x e2x ⊢
  constructor <;> linarith [ex.1, ex.2, e6x.1, e6x.2, e2x.1, e2x.2]

/-! ### The segment tower at `s = -x*` -/

def atγ : ℕ → ℝ → ℂ := fun i _ => if i = 0 then sQ.toC else (atY i).toC

theorem at_hc : ∀ k ≤ atP.N, (atP.cq k : ℝ) = DecayGlue.laiC k := fun k _ => cqL_real k

theorem at_enc : ∀ j ≤ 4, |potT DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8 atγ j 0 - ((atP.Tq atL1.1 atL2.1 atY j : ℚ) : ℝ)| ≤
    ((atP.Te atL1.2 atL2.2 atdq atδ atYm j : ℚ) : ℝ) := by
  obtain ⟨hR, hRφ, hδ, hs, hlo0, hlo2, hd, hdq, hne⟩ := at_num
  obtain ⟨hl1, hl2, -⟩ := at_logs
  obtain ⟨⟨a1, b1⟩, hl1'⟩ := Option.isSome_iff_exists.1 hl1
  obtain ⟨⟨a2, b2⟩, hl2'⟩ := Option.isSome_iff_exists.1 hl2
  have e1 : atL1 = (a1, b1) := by unfold atL1; rw [hl1']; rfl
  have e2 : atL2 = (a2, b2) := by unfold atL2; rw [hl2']; rfl
  have := segTower_encQ (M := DecayInstance.laiM) (h := DecayInstance.laiH) (c := DecayGlue.laiC) atP DecayGlue.laiC_hpos at_hc MQ sQ toC_MQ toC_HQ hne
    (γ := atγ) (x := 0) atY atYm (by simp [atγ]) (fun i hi _ => by simp [atγ]; omega)
    (fun i hi hi4 => by
      unfold atY atYm
      by_cases h1 : i = 1
      · simp [h1, CQ.nsq]
      · simp [h1, CQ.nsq])
    atR atδ atdq atlo a1 b1 a2 b2 8 8 hR hRφ hδ hs hlo0 hlo2 hd hdq hl1' hl2'
  rw [e1, e2]
  exact this

theorem at_jc : 1 < jc ((-((2211 / 500 : ℝ) : ℂ) - DecayInstance.laiM) / DecayInstance.laiH) := by
  obtain ⟨hR, hRφ, hδ, hs, hlo0, hlo2, hd, hdq, hne⟩ := at_num
  have hh0 : DecayInstance.laiH ≠ 0 := DecayInstance.laiH_ne
  have hRr : (1 : ℝ) < atR := by exact_mod_cast hR
  have hφsq : (atR : ℝ) ^ 2 ≤ ‖atP.φq.toC‖ ^ 2 := by
    rw [norm_toC_sq]; exact_mod_cast hRφ
  have hφR : (atR : ℝ) ≤ ‖atP.φq.toC‖ := by
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg atP.φq.toC]
  have hφ1 : 1 < ‖atP.φq.toC‖ := lt_of_lt_of_le hRr hφR
  have hφ0 : atP.φq.toC ≠ 0 := norm_pos_iff.1 (by linarith)
  have hφnsq : atP.φq.nsq ≠ 0 := nsq_ne_of_toC hφ0
  have hζ := toC_zeta atP hφnsq
  have hjcz : jc atP.ζ.toC = (‖atP.φq.toC‖ + ‖atP.φq.toC‖⁻¹) / 2 := by rw [hζ]; exact jc_jJ hφ0
  have hδs : ‖sQ.toC - (DecayInstance.laiM + DecayInstance.laiH * atP.ζ.toC)‖ ≤ atδ := by
    have e : (sQ.sub (MQ.add (atP.hq.mul atP.ζ))).toC = sQ.toC - (DecayInstance.laiM + DecayInstance.laiH * atP.ζ.toC) := by
      rw [CQ.toC_sub, CQ.toC_add, CQ.toC_mul, toC_MQ]
      have : atP.hq.toC = DecayInstance.laiH := toC_HQ
      rw [this]
    have h2 : ‖sQ.toC - (DecayInstance.laiM + DecayInstance.laiH * atP.ζ.toC)‖ ^ 2 ≤ (atδ : ℝ) ^ 2 := by
      rw [← e, norm_toC_sq]; exact_mod_cast hs
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg (sQ.toC - (DecayInstance.laiM + DecayInstance.laiH * atP.ζ.toC)), (by exact_mod_cast hδ : (0 : ℝ) ≤ atδ)]
  have hlh : (atlo : ℝ) ≤ ‖DecayInstance.laiH‖ := by
    have h2 : (atlo : ℝ) ^ 2 ≤ ‖DecayInstance.laiH‖ ^ 2 := by
      have : atP.hq.toC = DecayInstance.laiH := toC_HQ
      rw [← this, norm_toC_sq]; exact_mod_cast hlo2
    by_contra hcon
    push Not at hcon
    nlinarith [norm_nonneg DecayInstance.laiH, (by exact_mod_cast hlo0 : (0 : ℝ) ≤ atlo)]
  have hjcR : ((atR : ℝ) + (atR : ℝ)⁻¹) / 2 ≤ jc atP.ζ.toC := by
    rw [hjcz]; have := add_inv_mono hRr.le hφR; linarith
  have hseg0 := seg_dist_lb (M := DecayInstance.laiM) (h := DecayInstance.laiH) (s := sQ.toC) (s' := DecayInstance.laiM + DecayInstance.laiH * atP.ζ.toC)
    (ζ0 := atP.ζ.toC) (δ := atδ) (hlo := atlo) (R := atR) hh0 rfl hjcR hRr.le hδs
    (by exact_mod_cast hlo0) hlh
  have hw := hseg0 sQ.toC (right_mem_segment ℝ _ _)
  have hdq' : (atdq : ℝ) ≤ atlo * (((atR : ℝ) + (atR : ℝ)⁻¹) / 2 - 1) - atδ := by exact_mod_cast hdq
  have hdpos : (0 : ℝ) < atdq := by exact_mod_cast hd
  rw [toC_sQ] at hw
  have hnh : 0 < ‖DecayInstance.laiH‖ := norm_pos_iff.2 hh0
  by_contra hcon
  push Not at hcon
  nlinarith [mul_nonneg hnh.le (sub_nonneg.2 hcon)]

/-! ### The closed atoms -/

theorem lai_ha0_closed :
    omegaF 3 2 2 6 (2211 / 500) +
      2 * ∫ u, Real.log ‖((2211 / 500 : ℝ) : ℂ) + u‖ ∂(DecayInstance.laiSigma DecayGlue.laiC 8) ≤ (A0q : ℝ) := by
  refine lai_ha0_of_closed DecayGlue.laiC_hpos at_jc ?_
  rw [← logPotC_segMeasure DecayInstance.laiH_ne DecayGlue.laiC_hpos at_jc]
  have hU := at_enc 0 (by norm_num)
  have h0 : potT DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8 atγ 0 0 =
      logPotC (segMeasure DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8) (-((2211 / 500 : ℝ) : ℂ)) := by
    unfold potT; simp only [if_true]; unfold atγ; simp [toC_sQ]
  rw [h0] at hU
  have hTe : ((atP.Tq atL1.1 atL2.1 atY 0 : ℚ) : ℝ) = (T0q : ℝ) := rfl
  have hEe : ((atP.Te atL1.2 atL2.2 atdq atδ atYm 0 : ℚ) : ℝ) = (E0q : ℝ) := rfl
  rw [hTe, hEe, abs_le] at hU
  have hw := omegaF_enc
  rw [abs_le] at hw
  have hn : ((wFv + wFe - 4 * (T0q - E0q) : ℚ) : ℝ) ≤ (A0q : ℝ) := by exact_mod_cast a0_num
  push_cast at hn
  linarith [hU.1, hU.2, hw.1, hw.2]

theorem lai_hA_closed :
    |omegaD1 3 2 2 6 (2211 / 500) + 2 * ∫ u, ln1 u (2211 / 500) ∂(DecayInstance.laiSigma DecayGlue.laiC 8)| ≤ (AAq : ℝ) := by
  haveI := isFiniteMeasure_sig2 (M := DecayInstance.laiM) (h := DecayInstance.laiH) DecayGlue.laiC_hpos
  have hI := DecayInstance.laiSigma_hint1 (c := DecayGlue.laiC) (N := 8)
  have e1 : ∫ u, ln1 u (2211 / 500) ∂(DecayInstance.laiSigma DecayGlue.laiC 8) =
      2 * -(segSt DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8 1 (-((2211 / 500 : ℝ) : ℂ))).re := by
    rw [← integral_ln1_seg DecayInstance.laiH_ne DecayGlue.laiC_hpos at_jc]
    exact integral_sig2_eq _ (by unfold ln1; fun_prop) (fun u => by simp [ln1]) hI
  have h1 : potT DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8 atγ 1 0 = -(segSt DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8 1 (-((2211 / 500 : ℝ) : ℂ))).re := by
    unfold potT
    simp only [one_ne_zero, if_false]
    unfold fdb segD atγ
    have hy : (atY 1).toC = 1 := by apply Complex.ext <;> simp [atY, CQ.toC]
    simp [toC_sQ, hy]
  have hU := at_enc 1 (by norm_num)
  rw [h1] at hU
  have hTe : ((atP.Tq atL1.1 atL2.1 atY 1 : ℚ) : ℝ) = (T1q : ℝ) := rfl
  have hEe : ((atP.Te atL1.2 atL2.2 atdq atδ atYm 1 : ℚ) : ℝ) = (E1q : ℝ) := rfl
  rw [hTe, hEe, abs_le] at hU
  have hw := omegaD1_enc
  rw [abs_le] at hw
  have hn : ((|wDv + 4 * T1q| + wDe + 4 * E1q : ℚ) : ℝ) ≤ (AAq : ℝ) := by exact_mod_cast AA_num
  push_cast at hn
  rw [e1]
  rw [abs_le]
  constructor
  · cases abs_cases ((wDv : ℝ) + 4 * (T1q : ℝ)) <;> linarith [hU.1, hU.2, hw.1, hw.2]
  · cases abs_cases ((wDv : ℝ) + 4 * (T1q : ℝ)) <;> linarith [hU.1, hU.2, hw.1, hw.2]

theorem lai_hρ_closed : (A0q : ℝ) + (AAq : ℝ) ^ 2 / (2 * (49 / 100)) ≤ DecayInstance.laiEll + 4294856306 / 10 ^ 8 := by
  have h : ((A0q + AAq ^ 2 / (2 * (49 / 100)) : ℚ) : ℝ) ≤ ((-130471 / 10000 + 4294856306 / 10 ^ 8 : ℚ) : ℝ) := by
    exact_mod_cast rho_num
  push_cast at h
  have : DecayInstance.laiEll = -130471 / 10000 := by unfold DecayInstance.laiEll; norm_num
  rw [this]
  linarith

end

end CatalanCore.Lai.DecayAtoms

#print axioms CatalanCore.Lai.DecayAtoms.lai_ha0_closed
#print axioms CatalanCore.Lai.DecayAtoms.lai_hA_closed
#print axioms CatalanCore.Lai.DecayAtoms.lai_hρ_closed
