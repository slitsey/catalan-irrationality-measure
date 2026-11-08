module

public import CatalanMeasure.GenD.Signed.RouteI.TerminalC
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafAll
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm
public import CatalanMeasure.GenD.Signed.RouteI.G16
public import CatalanMeasure.GenD.Signed.RouteI.HCirc
public import CatalanMeasure.GenD.Signed.RouteI.RowCert.All
public import CatalanMeasure.GenD.Signed.RouteI.ColCert.MovedAll
public import CatalanMeasure.GenD.Signed.RouteI.AnchorE2Data
public import CatalanMeasure.GenD.Signed.RouteI.PhaseHoleProof
public import CatalanMeasure.GenD.Signed.RouteI.TrialC
public import CatalanMeasure.GenD.Signed.RouteI.ShiftGNum

@[expose] public section

namespace CatalanMeasure.GenD.Signed.RouteI.Measure270
open Set Filter CatalanMeasure.GenD.Signed.RouteI.TerminalC CatalanMeasure.GenD.Signed.RouteI.T4Instance
  CatalanMeasure.GenD.Signed.RouteI.T4LeafDefs
  CatalanMeasure.GenD.Signed.RouteI.T4LeafAll CatalanMeasure.GenD.Signed.RouteI.ShiftGAsm
  CatalanMeasure.GenD.Signed.RouteI.ShiftGSecond CatalanMeasure.GenD.Signed.RouteI.ShiftGFirst
  CatalanMeasure.GenD CatalanMeasure.GenD.D58 CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
  CatalanMeasure.GenD.Signed.RouteI CatalanMeasure.GenD.Signed.RouteI.CompletedGas
  CatalanMeasure.GenD.Signed.RouteI.CapFields CatalanMeasure.GenD.Signed.RouteI.CapSourceData
  CatalanMeasure.GenD.Signed.PhysicalPick OAI.InternalCatalan CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric

noncomputable section

/-- A chain of cells `[A k, B k]` with `B k = A (k+1)` covers `[A 0, B (n-1)]`. -/
theorem cover_chain {n : ℕ} (A B : Fin n → ℚ) (hn : 0 < n)
    (hch : ∀ j : ℕ, ∀ h : j + 1 < n, B ⟨j, by omega⟩ = A ⟨j + 1, h⟩)
    {α : ℝ} (h0 : (A ⟨0, hn⟩ : ℝ) ≤ α) (h1 : α ≤ (B ⟨n - 1, by omega⟩ : ℝ)) :
    ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k := by
  have key : ∀ j : ℕ, ∀ hj : j < n, α ≤ (B ⟨j, hj⟩ : ℝ) → ∃ k, (A k : ℝ) ≤ α ∧ α ≤ B k := by
    intro j
    induction j with
    | zero => intro hj hα; exact ⟨⟨0, hj⟩, h0, hα⟩
    | succ j ih =>
      intro hj hα
      by_cases hle : α ≤ (B ⟨j, by omega⟩ : ℝ)
      · exact ih (by omega) hle
      · refine ⟨⟨j + 1, hj⟩, ?_, hα⟩
        have := hch j hj
        rw [← this]
        exact (not_le.mp hle).le
  exact key (n - 1) (by omega) h1

theorem large_chain : ∀ j : Fin 5, largeB ⟨j, by omega⟩ = largeA ⟨j + 1, by omega⟩ := by
  decide +kernel -- kcost: 0.01 s estimated, 5 rational comparisons

theorem first_chain : ∀ j : Fin 5, firstB ⟨j, by omega⟩ = firstA ⟨j + 1, by omega⟩ := by
  decide +kernel -- kcost: 0.01 s estimated, 5 rational comparisons

theorem phys_chain : ∀ j : Fin 63, physB ⟨j, by omega⟩ = physA ⟨j + 1, by omega⟩ := by
  decide +kernel -- kcost: 0.1 s estimated, 63 rational comparisons

theorem large_hcov : ∀ α ∈ Icc (51 / 500 : ℝ) 1, ∃ k : Fin 6, (largeA k : ℝ) ≤ α ∧ α ≤ largeB k := by
  intro α hα
  refine cover_chain largeA largeB (by norm_num) (fun j h => large_chain ⟨j, by omega⟩) ?_ ?_
  · have : (largeA ⟨0, by norm_num⟩ : ℝ) = 51 / 500 := by norm_num [largeA]
    rw [this]; exact hα.1
  · have : (largeB ⟨6 - 1, by norm_num⟩ : ℝ) = 1 := by norm_num [largeB]
    rw [this]; exact hα.2

theorem first_hcov : ∀ α ∈ Icc (0 : ℝ) 1, ∃ k : Fin 6, (firstA k : ℝ) ≤ α ∧ α ≤ firstB k := by
  intro α hα
  refine cover_chain firstA firstB (by norm_num) (fun j h => first_chain ⟨j, by omega⟩) ?_ ?_
  · have : (firstA ⟨0, by norm_num⟩ : ℝ) = 0 := by norm_num [firstA]
    rw [this]; exact hα.1
  · have : (firstB ⟨6 - 1, by norm_num⟩ : ℝ) = 1 := by norm_num [firstB]
    rw [this]; exact hα.2

theorem phys_hcov : ∀ α ∈ Icc (0 : ℝ) (a1Q : ℝ), ∃ j : Fin 64, (physA j : ℝ) ≤ α ∧ α ≤ physB j := by
  intro α hα
  refine cover_chain physA physB (by norm_num) (fun j h => phys_chain ⟨j, by omega⟩) ?_ ?_
  · have : (physA ⟨0, by norm_num⟩ : ℝ) = 0 := by norm_num [physA, physAL]
    rw [this]; exact hα.1
  · have : (physB ⟨64 - 1, by norm_num⟩ : ℝ) = a1Q := by
      have h : physB ⟨64 - 1, by norm_num⟩ = a1Q := by decide +kernel
      rw [h]
    rw [this]; exact hα.2


theorem large_hN : ∀ k : Fin 6, ∀ β ∈ Icc (largeA k : ℝ) (largeB k), normCap2 1 ≤ evalQ (largeNC k) β := by
  intro k β _
  fin_cases k <;> norm_num [normCap2, K590.normCap, evalQ, largeNC]

theorem large_hF : ∀ k : Fin 6, ∀ β ∈ Icc (largeA k : ℝ) (largeB k),
    K590.fieldCap + 1 * X2cap + Y2fun β ≤ evalQ (largeFC k) β := by
  intro k β hβ
  obtain ⟨h0, h1⟩ := hβ
  fin_cases k <;> norm_num [largeA] at h0 <;> norm_num [largeB] at h1 <;>
    (unfold Y2fun yI; split_ifs <;> norm_num [evalQ, largeFC, K590.fieldCap, X2cap] <;> linarith)

theorem large_hr : ∀ k : Fin 6, ∀ β ∈ Icc (largeA k : ℝ) (largeB k),
    (7 / 1000 : ℝ) + 1 * (-268 / 10000 - 7 / 1000) ≤ evalQ (largeRs k) β := by
  intro k β _
  fin_cases k <;> norm_num [evalQ, largeRs]

theorem large_hnp : ∀ k : Fin 6, ∀ β ∈ Icc (largeA k : ℝ) (largeB k),
    (7 / 1000 : ℝ) + 1 * (233 / 10000 - 7 / 1000) ≤ evalQ (largeNp k) β := by
  intro k β _
  fin_cases k <;> norm_num [evalQ, largeNp]


theorem tau1_low {β : ℝ} (h : β ≤ 11 / 50) : tau1 β = β * 50 / 11 := by
  unfold tau1; exact min_eq_right (by linarith)

theorem tau1_high {β : ℝ} (h : 11 / 50 ≤ β) : tau1 β = 1 := by
  unfold tau1; exact min_eq_left (by linarith)

theorem first_np_eq : ∀ k : Fin 6, firstNp k = firstRs k := by
  intro k; fin_cases k <;> rfl

theorem first_hPoly' : ∀ k : Fin 6, PolyNonneg (wPq sigQ lC.η 0 (firstNC k) (firstFC k) (firstRs k) (firstRs k))
    (firstA k) (firstB k) := by
  intro k
  have := first_hPoly k
  have e : lC.σ = sigQ := by norm_num [lC, TerminalC.sigQ]
  rw [e] at this
  rw [first_np_eq] at this
  exact this

theorem first_hN : ∀ k : Fin 6, ∀ β ∈ Icc (firstA k : ℝ) (firstB k), normCap1 (tau1 β) ≤ evalQ (firstNC k) β := by
  intro k β hβ
  obtain ⟨h0, h1⟩ := hβ
  fin_cases k <;> norm_num [firstA] at h0 <;> norm_num [firstB] at h1
  · rw [tau1_low h1]
    norm_num [normCap1, n1, evalQ, firstNC]
    nlinarith
  all_goals
    rw [tau1_high (by linarith)]
    norm_num [normCap1, n1, evalQ, firstNC]

theorem first_hF : ∀ k : Fin 6, ∀ β ∈ Icc (firstA k : ℝ) (firstB k),
    F1 + tau1 β * X1cap + Y1tot β ≤ evalQ (firstFC k) β := by
  intro k β hβ
  obtain ⟨h0, h1⟩ := hβ
  fin_cases k <;> norm_num [firstA] at h0 <;> norm_num [firstB] at h1
  · rw [tau1_low h1]
    unfold Y1tot Y1ray
    simp only [h1, ite_true]
    norm_num [evalQ, firstFC, F1, X1cap]
    nlinarith
  all_goals
    rw [tau1_high (by linarith)]
    unfold Y1tot Y1fun yI
    split_ifs <;> norm_num [evalQ, firstFC, F1, X1cap, Y1ray] <;> linarith

theorem first_hM : ∀ k : Fin 6, ∀ β ∈ Icc (firstA k : ℝ) (firstB k),
    (1 - tau1 β) * (35072 / 100000 : ℝ) + tau1 β * (35295 / 100000) ≤ evalQ (firstRs k) β := by
  intro k β hβ
  obtain ⟨h0, h1⟩ := hβ
  fin_cases k <;> norm_num [firstA] at h0 <;> norm_num [firstB] at h1
  · rw [tau1_low h1]
    norm_num [evalQ, firstRs]
    linarith
  all_goals
    rw [tau1_high (by linarith)]
    norm_num [evalQ, firstRs]


/-! ### The anchor-move sequences -/

abbrev da0S : ℕ → ℝ := trialSeqOf TrialC.da0 (2 ^ 40)
abbrev da1S : ℕ → ℝ := trialSeqOf TrialC.da1 (2 ^ 40)
abbrev dv0S : ℕ → ℝ := trialSeqOf TrialC.dv0 (2 ^ 40)
abbrev dv1S : ℕ → ℝ := trialSeqOf TrialC.dv1 (2 ^ 40)

theorem movA0_eq : RowCert.movA0 = da0S := by
  unfold RowCert.movA0 da0S RowCertMoved.movSeq trialSeqOf
  funext k
  have : RowCert.aL0 = TrialC.da0 := by decide +kernel
  have h2 : RowCert.DH = 2 ^ 40 := rfl
  rw [this, h2]

theorem movA1_eq : RowCert.movA1 = da1S := by
  unfold RowCert.movA1 da1S RowCertMoved.movSeq trialSeqOf
  funext k
  have : RowCert.aL1 = TrialC.da1 := by decide +kernel
  have h2 : RowCert.DH = 2 ^ 40 := rfl
  rw [this, h2]

theorem movV0_eq : RowCert.movV0 = dv0S := by
  unfold RowCert.movV0 dv0S RowCertMoved.movSeq trialSeqOf
  funext k
  have : RowCert.vL0 = TrialC.dv0 := by decide +kernel
  have h2 : RowCert.DH = 2 ^ 40 := rfl
  rw [this, h2]

theorem movV1_eq : RowCert.movV1 = dv1S := by
  unfold RowCert.movV1 dv1S RowCertMoved.movSeq trialSeqOf
  funext k
  have : RowCert.vL1 = TrialC.dv1 := by decide +kernel
  have h2 : RowCert.DH = 2 ^ 40 := rfl
  rw [this, h2]

theorem movSeq_eq (l : List ℤ) : RowCertMoved.movSeq l TrialC.D = trialSeqOf l (2 ^ 40) := rfl

/-! ### The near sheet -/

theorem phys_mem {j : Fin 64} {β : ℝ} (hβ : β ∈ Icc (physA j : ℝ) (physB j)) : β ∈ Icc (0 : ℝ) (51 / 500) := by
  have h1 := phys_hA0 j
  have h2 := phys_hB1 j
  have e : (a1Q : ℝ) = 51 / 500 := ShiftGAsm.a1Q_real
  refine ⟨le_trans (by exact_mod_cast h1) hβ.1, le_trans hβ.2 ?_⟩
  rw [← e]; exact_mod_cast h2

theorem near_hr (β : ℝ) : (7 / 1000 : ℝ) + tauN β * (-268 / 10000 - 7 / 1000) ≤ evalQ physRS β := by
  unfold tauN; norm_num [evalQ, physRS]; linarith

theorem near_hnp (β : ℝ) : (7 / 1000 : ℝ) + tauN β * (233 / 10000 - 7 / 1000) ≤ evalQ physNP β := by
  unfold tauN; norm_num [evalQ, physNP]; linarith

def nearR (j : Fin 64) (β : ℝ) (hβ : β ∈ Icc (physA j : ℝ) (physB j)) :=
  nearRp (physΔ j) ((c2Q : ℝ) + lC.σ) (fun b => evalQ physRS b) (fun b => evalQ physNP b) β (phys_mem hβ)
    (near_hr β) (near_hnp β)

theorem near_hNp (j : Fin 64) (β : ℝ) (hβ : β ∈ Icc (physA j : ℝ) (physB j)) :
    (nearR j β hβ).normCap ≤ evalQ physNC β := by
  unfold nearR
  rw [nearRp_normCap]
  unfold normCap2 tauN
  norm_num [K590.normCap, evalQ, physNC]
  nlinarith

theorem near_hFp (j : Fin 64) (β : ℝ) (hβ : β ∈ Icc (physA j : ℝ) (physB j)) :
    (nearR j β hβ).fieldCap ≤ evalQ physFC β := by
  unfold nearR
  rw [nearRp_fieldCap]
  unfold tauN
  norm_num [K590.fieldCap, evalQ, physFC, X2cap, Y2ray]
  linarith

theorem FU_le : physFU ≤ FUex := by
  decide +kernel -- kcost: 0.1 s estimated, 32 rational terms

theorem du2_le : physDU2 ≤ (du40.getD 1 0 : ℚ) / 2 ^ 24 := by
  decide +kernel -- kcost: 0.01 s estimated

theorem near_hSp (j : Fin 64) (β : ℝ) (hβ : β ∈ Icc (physA j : ℝ) (physB j)) :
    (physU : ℝ) + (β / (a1Q : ℝ)) * physFU ≤ ∑' k : ℕ, testT.F (k + 1) * (nearR j β hβ).p (k + 1) :=
  hSp_of physU physFU (by norm_num [physU]) (by exact_mod_cast FU_le)

theorem near_hp2p (j : Fin 64) (β : ℝ) (hβ : β ∈ Icc (physA j : ℝ) (physB j)) :
    (physP2 : ℝ) + (β / (a1Q : ℝ)) * physDU2 ≤ (nearR j β hβ).p 2 :=
  hp2p_of physP2 physDU2 (by norm_num [physP2]) (by exact_mod_cast du2_le)
/-! ### The signed fields -/

theorem lC_σ : lC.σ = sigQ := by norm_num [lC, TerminalC.sigQ]

theorem hI1_lC : anchorVal 0 + gasConst capSource ≤ lC.I1 := by
  have h := I1_cap
  have e : ((lC.I1 : ℚ) : ℝ) = 2366997 / 1000000 := by norm_num [lC]
  rw [e]; exact h

theorem hL0_lC : 2 * barrierInner (aT capSource 0) da0S + barrierInner (aV capSource 0) dv0S ≤ lC.L0 := by
  have h := AnchorE2Data.L0_le
  have e : ((lC.L0 : ℚ) : ℝ) = ((-75421576 : ℤ) : ℝ) / 1000000000000 := by norm_num [lC]
  rw [e]; exact h

theorem hL1_lC : 2 * barrierInner (aT capSource 0) da1S + barrierInner (aV capSource 0) dv1S ≤ lC.L1 := by
  have h := AnchorE2Data.L1_le
  have e : ((lC.L1 : ℚ) : ℝ) = ((-4943292757 : ℤ) : ℝ) / 100000000000 := by norm_num [lC]
  rw [e]; exact h

theorem hQ00_lC : barrierInner da0S da0S + barrierInner dv0S dv0S / 2 ≤ lC.Q00 := by
  have h := ShiftGNum.hQ00_real
  have e : ((lC.Q00 : ℚ) : ℝ) = 16623 / 100000000000 := by norm_num [lC]
  rw [e]; exact h

theorem hQ01_lC : barrierInner da0S da1S + barrierInner dv0S dv1S / 2 ≤ lC.Q01 := by
  have h := ShiftGNum.hQ01_real
  have e : ((lC.Q01 : ℚ) : ℝ) = 95232 / 100000000000 := by norm_num [lC]
  rw [e]; exact h

theorem hQ11_lC : barrierInner da1S da1S + barrierInner dv1S dv1S / 2 ≤ lC.Q11 := by
  have h := ShiftGNum.hQ11_real
  have e : ((lC.Q11 : ℚ) : ℝ) = 1002863 / 1000000000 := by norm_num [lC]
  rw [e]; exact h

theorem R0_lC : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0S da1S dv0S dv1S 0 x ≤ lC.c0R := by
  intro x hx
  have h := RowCert.c0R_cert x hx
  rw [movA0_eq, movA1_eq, movV0_eq, movV1_eq] at h
  have e : ((lC.c0R : ℚ) : ℝ) = ((-2579740254 / 1000000000 : ℚ) : ℝ) := by norm_num [lC]
  rw [e]; exact h

theorem R1_lC : ∀ x ∈ CapSource.rowDom, capSource.freeRow Trunc.exact 0 x + fRm da0S da1S dv0S dv1S 1 x ≤ lC.c1R := by
  intro x hx
  have h := RowCert.c1R_cert x hx
  rw [movA0_eq, movA1_eq, movV0_eq, movV1_eq] at h
  have e : ((lC.c1R : ℚ) : ℝ) = ((-2574009165 / 1000000000 : ℚ) : ℝ) := by norm_num [lC]
  rw [e]; exact h

theorem C0_lC : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0S dv1S 0 s ≤ lC.c0C := by
  intro s hs
  have h := ColCert.Moved.movedC0' dv0S dv1S rfl s hs
  have e : lC.c0C = ColCert.Moved.c0Cq := by norm_num [lC, ColCert.Moved.c0Cq, ColCert.Moved.cap0n]
  rw [e]; exact h

theorem C1_lC : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0S dv1S 1 s +
    (aeQ : ℝ) * Real.log (1 + (3 / 4) * s) ≤ lC.c1C := by
  intro s hs
  have h := ColCert.Moved.movedC1' dv0S dv1S rfl rfl s hs
  have e : lC.c1C = ColCert.Moved.c1Cq := by norm_num [lC, ColCert.Moved.c1Cq, ColCert.Moved.cap1n]
  have e2 : (aeQ : ℝ) = 1 / 25 := by norm_num [aeQ]
  rw [e, e2]; exact h

theorem C2_lC : ∀ s ∈ Ioo (0 : ℝ) 1, capSource.colField 0 s + fCm dv0S dv1S 1 s +
    (a1Q : ℝ) * Real.log (1 + (3 / 4) * s) ≤ lC.c2C := by
  intro s hs
  have h := ColCert.Moved.movedC2' dv0S dv1S rfl rfl s hs
  have e : lC.c2C = ColCert.Moved.c2Cq := by norm_num [lC, ColCert.Moved.c2Cq, ColCert.Moved.cap2n]
  have e2 : (a1Q : ℝ) = 51 / 500 := ShiftGAsm.a1Q_real
  rw [e, e2]; exact h

/-! ### The three data records and the theorem -/

theorem len_da0_ : TrialC.da0.length + 1 = 161 := by rw [TrialC.len_da0]
theorem len_da1_ : TrialC.da1.length + 1 = 161 := by rw [TrialC.len_da1]
theorem len_dv0_ : TrialC.dv0.length + 1 = 161 := by rw [TrialC.len_dv0]
theorem len_dv1_ : TrialC.dv1.length + 1 = 161 := by rw [TrialC.len_dv1]

theorem large_hPoly' : ∀ k : Fin 6, PolyNonneg (wPq sigQ lC.η 0 (largeNC k) (largeFC k) (largeRs k) (largeNp k))
    (largeA k) (largeB k) := by
  intro k
  have := large_hPoly k
  rw [lC_σ] at this
  exact this

/-- The large sheet record: `ShiftGAsm.largeDataOf` at the cells `largeA, …`. -/
def largeData : LargeData :=
  largeDataOf largeA largeB large_hA0 large_hB1 large_hAB large_hcov largeNC largeFC largeRs largeNp lC.η
    lC_η_pos large_hPoly' large_hN large_hF large_hr large_hnp

/-- The first sheet record: `ShiftGAsm.firstDataOf` at the cells `firstA, …`. -/
def firstData : FirstData :=
  firstDataOf firstA firstB first_hA0 first_hB1 first_hAB first_hcov firstNC firstFC firstRs lC.η lC_η_pos
    first_hPoly' first_hN first_hF first_hM

theorem phys_hPW' : ∀ j : Fin 64, PolyNonneg (wPq lC.σ lC.η (physΔ j) physNC physFC physRS physNP) (physA j) (physB j) :=
  phys_hPW

/-- The near sheet record. -/
def nearData : NearData where
  oc := fun _ => -976 / 1000
  nc := -976 / 1000
  ho := G16.ho
  hn := G16.hn
  hoc := fun _ => le_rfl
  hnc := le_rfl
  ha := G16.ha
  da0 := da0S
  da1 := da1S
  dv0 := dv0S
  dv1 := dv1S
  K := 161
  ha0 := fun k hk => trialSeqOf_support _ _ (by rw [len_da0_]; exact hk)
  ha1 := fun k hk => trialSeqOf_support _ _ (by rw [len_da1_]; exact hk)
  hv0 := fun k hk => trialSeqOf_support _ _ (by rw [len_dv0_]; exact hk)
  hv1 := fun k hk => trialSeqOf_support _ _ (by rw [len_dv1_]; exact hk)
  l := lC
  hσ := lC_σ
  hI1 := hI1_lC
  hL0 := hL0_lC
  hL1 := hL1_lC
  hQ00 := hQ00_lC
  hQ01 := hQ01_lC
  hQ11 := hQ11_lC
  R0 := R0_lC
  R1 := R1_lC
  C0 := C0_lC
  C1 := C1_lC
  C2 := C2_lC
  hη := lC_η_pos
  hP1 := sig_hP1
  hP2 := sig_hP2
  κ := 64
  A := physA
  B' := physB
  hAB := phys_hAB
  hA0 := phys_hA0
  hB1 := phys_hB1
  hcovP := phys_hcov
  Δ := physΔ
  hΔ0 := phys_hΔ0
  nC := fun _ => physNC
  fC := fun _ => physFC
  rs := fun _ => physRS
  np := fun _ => physNP
  F0 := physF0
  U := physU
  FU := physFU
  p2 := physP2
  du2 := physDU2
  s := physS
  s' := physS'
  hF0 := phys_hF0
  hPW := phys_hPW'
  hPφ := phys_hPφ
  hPω := phys_hPω
  Rp := fun j β hβ => nearR j β hβ
  hNp := fun j β hβ => near_hNp j β hβ
  hFp := fun j β hβ => near_hFp j β hβ
  hSp := fun j β hβ => near_hSp j β hβ
  hp2p := fun j β hβ => near_hp2p j β hβ
  hs := phys_hs
  hs' := phys_hs'
  hole := phaseHole

/-- **The irrationality measure of Catalan's constant is at most 270.** -/
theorem catalan_irrationalityMeasure_270 :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(270 : ℝ)) <
        |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  measure_270 firstData largeData nearData HCirc.hcirc_d HCirc.hseg_d

end
end CatalanMeasure.GenD.Signed.RouteI.Measure270

#print axioms CatalanMeasure.GenD.Signed.RouteI.Measure270.catalan_irrationalityMeasure_270
