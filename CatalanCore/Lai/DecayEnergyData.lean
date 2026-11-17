module

public import CatalanCore.Lai.DecayEnergyCells

@[expose] public section

/-!
# `CatalanCore.Lai.DecayEnergyData`: the closed energy datum `laiEnergyOK_closed : LaiEnergyOK laiC 8` (T-energy)

The 26 cells `eC0 ... eC25` of `DecayEnergyCells` partition `[0, π]` at the multiples `π n/128`
(`nbL`), each cell passes `okA` and `okE` (`eAt_ok`), `okE_sound2` gives `hcen`, `h5`, `hE` and the cell
bound, and one rational inequality (`hfin_num`: self energy from the `K0E` enclosure plus
`eCb / (4 (π₄ + e))` against `208871/10^5`) closes `hfin` of `laiEnergyOK_of_cells`.
-/

open Set Real Finset
open CatalanCore.Zeta5.Potential CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.Cert CatalanMeasure.CellCert
  OAI.InternalCatalan CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Lai.DecayCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Lai.DecayTowerSeg CatalanCore.Lai.DecayTowerV
  CatalanCore.Lai.DecayGlue CatalanCore.Lai.DecayInstance CatalanCore.Lai.DecayEnergy
  CatalanCore.Lai.DecayCheck CatalanCore.Lai.DecayCert CatalanCore.Lai.DecayEnergyCheck
  CatalanCore.Lai.DecayEnergyCells

namespace CatalanCore.Lai.DecayEnergyData

noncomputable section

/-- the 26 energy cells -/
def eCells : List ECell := [eC0, eC1, eC2, eC3, eC4, eC5, eC6, eC7, eC8, eC9, eC10, eC11, eC12, eC13, eC14, eC15, eC16, eC17, eC18, eC19, eC20, eC21, eC22, eC23, eC24, eC25]
/-- the partition numerators: cell `i` is `[nbL i, nbL (i+1)] · π/128` -/
def nbL : List ℕ := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 92, 96, 100, 104, 108, 110, 112, 114, 116, 118, 120, 122, 124, 126, 128]
def eAt (i : ℕ) : ECell := eCells.getD i eC0
/-- the sum of the cell bounds -/
def eCb : ℚ := ∑ i ∈ Finset.range 26, (eAt i).Cb
/-- the partition points `a i = π nbL(i) / 128` -/
def aE (i : ℕ) : ℝ := Real.pi * (nbL.getD i 0 : ℝ) / 128

theorem eCells_len : eCells.length = 26 := by decide +kernel

theorem eCells_ok : eCells.all (fun e => okA e.d && okE e) = true := by
  simp only [eCells, List.all_cons, List.all_nil, Bool.and_true, eC0_okA, eC0_okE, eC1_okA, eC1_okE, eC2_okA, eC2_okE, eC3_okA, eC3_okE, eC4_okA, eC4_okE, eC5_okA, eC5_okE, eC6_okA, eC6_okE, eC7_okA, eC7_okE, eC8_okA, eC8_okE, eC9_okA, eC9_okE, eC10_okA, eC10_okE, eC11_okA, eC11_okE, eC12_okA, eC12_okE, eC13_okA, eC13_okE, eC14_okA, eC14_okE, eC15_okA, eC15_okE, eC16_okA, eC16_okE, eC17_okA, eC17_okE, eC18_okA, eC18_okE, eC19_okA, eC19_okE, eC20_okA, eC20_okE, eC21_okA, eC21_okE, eC22_okA, eC22_okE, eC23_okA, eC23_okE, eC24_okA, eC24_okE, eC25_okA, eC25_okE, Bool.and_self]

theorem eAt_mem {i : ℕ} (hi : i < 26) : eAt i ∈ eCells := by
  unfold eAt
  rw [List.getD_eq_getElem _ _ (by rw [eCells_len]; exact hi)]
  exact List.getElem_mem _

theorem eAt_ok {i : ℕ} (hi : i < 26) : okA (eAt i).d = true ∧ okE (eAt i) = true := by
  have := List.all_eq_true.1 eCells_ok _ (eAt_mem hi)
  simpa [Bool.and_eq_true] using this

theorem eAt_n : ∀ i, i < 26 → (eAt i).n0 = nbL.getD i 0 ∧ (eAt i).n1 = nbL.getD (i + 1) 0 := by
  -- kcost: 0.05 s estimated
  decide +kernel

theorem nb_facts : nbL.getD 0 0 = 0 ∧ nbL.getD 26 0 = 128 ∧
    ∀ i, i < 26 → nbL.getD i 0 ≤ nbL.getD (i + 1) 0 := by
  -- kcost: 0.02 s estimated
  decide +kernel

theorem eCb_neg : eCb < 0 := by
  -- kcost: 0.05 s estimated
  decide +kernel

/-- the rational inequality: self energy (`K0E` enclosure) plus the cross part against `208871/10^5` -/
theorem hfin_num :
    2 * ((3 / 2 : ℚ) * (K0E.1 + K0E.2) + ∑ k ∈ Finset.range 8, (cqL (k + 1)) ^ 2 / (2 * ((k + 1 : ℕ) : ℚ))) +
      2 * (eCb / (4 * (PI4 + PI4E))) ≤ 208871 / 10 ^ 5 := by
  -- kcost: 0.3 s estimated
  decide +kernel

theorem cq0 : (cqL 0 : ℚ) = 3 / 2 := by
  unfold cqL; norm_num

theorem laiC0 : DecayGlue.laiC 0 = 3 / 2 := by
  rw [← cqL_real 0, cq0]; norm_num

theorem hfin_real :
    2 * (-(DecayGlue.laiC 0 ^ 2 * (Real.log ‖DecayInstance.laiH‖ - Real.log 2)) +
        ∑ k ∈ Finset.range 8, DecayGlue.laiC (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) +
      2 * ((1 / Real.pi) * (eCb : ℝ)) ≤ 208871 / 10 ^ 5 := by
  have hk := K0_enc
  rw [abs_le] at hk
  have hs : ∑ k ∈ Finset.range 8, DecayGlue.laiC (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) =
      ((∑ k ∈ Finset.range 8, (cqL (k + 1)) ^ 2 / (2 * ((k + 1 : ℕ) : ℚ)) : ℚ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cqL_real]
  have hnum : ((2 * ((3 / 2 : ℚ) * (K0E.1 + K0E.2) + ∑ k ∈ Finset.range 8, (cqL (k + 1)) ^ 2 / (2 * ((k + 1 : ℕ) : ℚ))) +
      2 * (eCb / (4 * (PI4 + PI4E))) : ℚ) : ℝ) ≤ ((208871 / 10 ^ 5 : ℚ) : ℝ) := by
    exact_mod_cast hfin_num
  push_cast at hnum
  have hneg : (eCb : ℝ) < 0 := by exact_mod_cast eCb_neg
  have hπ := pi_bounds
  have hπ0 := Real.pi_pos
  have hπhi : (0 : ℝ) < 4 * (PI4 + PI4E) := by
    have : (0 : ℚ) < 4 * (PI4 + PI4E) := by unfold PI4 PI4E PI4N; norm_num
    exact_mod_cast this
  have hcross : (1 / Real.pi) * (eCb : ℝ) ≤ (eCb : ℝ) / (4 * ((PI4 : ℝ) + PI4E)) := by
    have h1 : (-(eCb : ℝ)) / (4 * ((PI4 : ℝ) + PI4E)) ≤ (-(eCb : ℝ)) / Real.pi :=
      div_le_div_of_nonneg_left (by linarith) hπ0 (by linarith [hπ.2])
    have e1 : (1 / Real.pi) * (eCb : ℝ) = -((-(eCb : ℝ)) / Real.pi) := by ring
    have e2 : (eCb : ℝ) / (4 * ((PI4 : ℝ) + PI4E)) = -((-(eCb : ℝ)) / (4 * ((PI4 : ℝ) + PI4E))) := by ring
    rw [e1, e2]; linarith
  have e0 : -(DecayGlue.laiC 0 ^ 2 * (Real.log ‖DecayInstance.laiH‖ - Real.log 2)) =
      (3 / 2) * (-DecayGlue.laiC 0 * Real.log ‖DecayInstance.laiH‖ + DecayGlue.laiC 0 * Real.log 2) := by
    rw [laiC0]; ring
  rw [e0, hs]
  push_cast
  linarith [hk.1, hk.2]

theorem laiEnergyOK_closed : CatalanCore.Lai.DecayCert.LaiEnergyOK DecayGlue.laiC 8 := by
  have hn0 : ∀ i, i < 26 → ((eAt i).n0 : ℝ) = (nbL.getD i 0 : ℝ) := fun i hi => by
    exact_mod_cast (eAt_n i hi).1
  have hn1 : ∀ i, i < 26 → ((eAt i).n1 : ℝ) = (nbL.getD (i + 1) 0 : ℝ) := fun i hi => by
    exact_mod_cast (eAt_n i hi).2
  have hsound := fun (i : ℕ) (hi : i < 26) =>
    okE_sound2 (eAt_ok hi).1 (eAt_ok hi).2 (a0 := aE i) (a1 := aE (i + 1))
      (by unfold aE; rw [hn0 i hi]) (by unfold aE; rw [hn1 i hi])
  refine DecayGlue.laiEnergyOK_of_cells DecayGlue.laiC_hpos 26 aE ?_ ?_ ?_
    (fun i j => tq2A (eAt i).d j) (fun i j => teE (eAt i) j)
    (fun i => ((eAt i).d.T2q : ℝ) / 120) (fun i => ((eAt i).Er : ℝ)) ?_ ?_ ?_ ?_
  · unfold aE; rw [nb_facts.1]; simp
  · unfold aE; rw [nb_facts.2.1]; push_cast; ring
  · intro i hi
    unfold aE
    have := nb_facts.2.2 i hi
    have h2 : (nbL.getD i 0 : ℝ) ≤ (nbL.getD (i + 1) 0 : ℝ) := by exact_mod_cast this
    have := Real.pi_pos
    gcongr
  · intro i hi j hj
    exact (hsound i hi).1 j hj
  · intro i hi x hx
    exact (hsound i hi).2.1 x hx
  · intro i hi
    have := (hsound i hi).2.2.1
    have h120 : 120 * (((eAt i).d.T2q : ℝ) / 120) = ((eAt i).d.T2q : ℝ) := by ring
    simpa using this
  · have hle : ∑ i ∈ Finset.range 26,
        crossCellBound (DecayGlue.crossT DecayGlue.laiC 8) DecayGlue.laiC 8 ((aE i + aE (i + 1)) / 2)
          ((aE (i + 1) - aE i) / 2) (((eAt i).Er : ℚ) : ℝ) ≤ (eCb : ℝ) := by
      unfold eCb
      push_cast
      exact Finset.sum_le_sum fun i hi => (hsound i (Finset.mem_range.1 hi)).2.2.2
    have h1 : 0 < 1 / Real.pi := by have := Real.pi_pos; positivity
    have := mul_le_mul_of_nonneg_left hle h1.le
    have hf := hfin_real
    linarith

end

end CatalanCore.Lai.DecayEnergyData

#print axioms CatalanCore.Lai.DecayEnergyData.laiEnergyOK_closed
