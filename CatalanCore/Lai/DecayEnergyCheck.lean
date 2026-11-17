module

public import CatalanCore.Lai.DecayCheck
public import CatalanCore.Lai.DecayCert

@[expose] public section

/-!
# `CatalanCore.Lai.DecayEnergyCheck`: energy cell checker `okE` and its soundness (T-energy)

For an A cell `d` of the cover and its angle cell `[n0, n1]/128`: the centre enclosure `hcen` of the
cross tower (re-centring `tq2A`, `te2A` to `π (n0+n1)/256`), the sup bound `h5`, the remainder `hE`
and the cell bound `crossCellBound ≤ Cb` (`okE_sound`).
-/

open Set Real Finset
open CatalanCore.Zeta5.Potential CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.Cert CatalanMeasure.CellCert
  OAI.InternalCatalan CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Lai.DecayCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Lai.DecayTowerSeg CatalanCore.Lai.DecayTowerV
  CatalanCore.Lai.DecayGlue CatalanCore.Lai.DecayInstance CatalanCore.Lai.DecayEnergy
  CatalanCore.Lai.DecayCheck CatalanCore.Lai.DecayCert

namespace CatalanCore.Lai.DecayEnergyCheck

noncomputable section

structure ECell where
  d : ACell
  n0 : ℕ
  n1 : ℕ
  Er : ℚ
  Cb : ℚ

def wE (e : ECell) : ℚ := ((e.n1 : ℚ) - e.n0) / 256
def ncE (e : ECell) : ℕ := (e.n0 + e.n1) / 2
def rloE (e : ECell) : ℚ := 4 * (PI4 - PI4E) * wE e
def rhiE (e : ECell) : ℚ := 4 * (PI4 + PI4E) * wE e
def dloE (e : ECell) : ℚ := e.d.dq - bA e.d
def etaE (e : ECell) : ℕ → ℚ := fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (dloE e) ^ k
def BE (e : ECell) (j : ℕ) : ℚ := fdb (etaE e) (fun _ => bhq) j
def epsE (e : ECell) : ℚ := epsA2 (thA e.d) (argA e.d).1 (argA e.d).2
def teE (e : ECell) (j : ℕ) : ℚ := te2A e.d j + epsE e * BE e (j + 1)
def supBq (e : ECell) (j : ℕ) : ℚ :=
  ((∑ m ∈ Finset.range (5 - j), (|tq2A e.d (j + m)| + teE e (j + m)) * rhiE e ^ m / (m.factorial : ℚ)) +
    e.d.T2q * rhiE e ^ (5 - j) / ((5 - j).factorial : ℚ)) / (j.factorial : ℚ)
def Vfq (k : ℕ) : ℚ := (∑ k' ∈ Finset.range 9, |cqL k'| * (k' : ℚ) ^ k) / (k.factorial : ℚ)
def fqE (e : ECell) (j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 9, cqL k * (k : ℚ) ^ j * DecayTrig.cosTm (k * ncE e + 64 * j)
def feE (j : ℕ) : ℚ := ∑ k ∈ Finset.range 9, |cqL k * (k : ℚ) ^ j| * DecayTrig.trigE
def mtE (e : ECell) (j : ℕ) : ℚ :=
  ∑ ij ∈ Finset.antidiagonal j, (j.choose ij.1 : ℚ) *
    (tq2A e.d ij.1 * fqE e ij.2 + |tq2A e.d ij.1| * feE ij.2 + |fqE e ij.2| * teE e ij.1 +
      teE e ij.1 * feE ij.2)
def puE (e : ECell) (c : ℚ) (k : ℕ) : ℚ := if 0 ≤ c then c * rhiE e ^ k else c * rloE e ^ k
def cbE (e : ECell) : ℚ :=
  puE e (2 * mtE e 0) 1 + puE e (mtE e 2 / 3) 3 + puE e (mtE e 4 / 60) 5 + puE e (e.Er / 3) 6

@[reducible] def okEProp (e : ECell) : Prop :=
  e.d.lo = (e.n0 : ℚ) / 128 ∧ e.d.hi = (e.n1 : ℚ) / 128 ∧ e.n0 ≤ e.n1 ∧ (e.n0 + e.n1) % 2 = 0 ∧
  0 ≤ teE e 0 ∧ 0 ≤ teE e 1 ∧ 0 ≤ teE e 2 ∧ 0 ≤ teE e 3 ∧ 0 ≤ teE e 4 ∧ 0 ≤ e.d.T2q ∧
  0 < dloE e ∧
  (∑ j ∈ Finset.range 6, supBq e j * Vfq (5 - j)) ≤ e.Er ∧ cbE e ≤ e.Cb

def okE (e : ECell) : Bool := decide (okEProp e)

theorem pu_le {c rlo rhi : ℚ} {r : ℝ} (k : ℕ) (h0 : 0 ≤ (rlo : ℝ)) (h1 : (rlo : ℝ) ≤ r)
    (h2 : r ≤ (rhi : ℝ)) :
    (c : ℝ) * r ^ k ≤ ((if 0 ≤ c then c * rhi ^ k else c * rlo ^ k : ℚ) : ℝ) := by
  split_ifs with hc
  · push_cast
    have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (h0.trans h1) h2 k) hc'
  · push_cast
    have hc' : (c : ℝ) ≤ 0 := by exact_mod_cast (not_le.1 hc).le
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ h0 h1 k) hc'

theorem okEProp_parts {e : ECell} (hE : okE e = true) : okEProp e := of_decide_eq_true hE

/-- the order-`j` majorant of the cross tower on the evaluation cell of an A cell -/
theorem crossT_bound {d : ACell} (hd : okA d = true) {j : ℕ} (hj1 : 1 ≤ j) (hj5 : j ≤ 5)
    (hdlo0 : 0 < d.dq - bA d) :
    ∀ y ∈ Icc (2 * Real.arctan (d.τ : ℝ) - d.ρ') (2 * Real.arctan (d.τ : ℝ) + d.ρ'),
      |DecayGlue.crossT DecayGlue.laiC 8 j y| ≤
        ((fdb (fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (d.dq - bA d) ^ k) (fun _ => bhq) j : ℚ) : ℝ) := by
  intro y hy
  have hdl := (okA_all hd).2.2.2.2.2 y hy
  have hdlo0R : (0 : ℝ) < ((d.dq - bA d : ℚ) : ℝ) := by exact_mod_cast hdlo0
  have hreg : 1 < jc ((armA DecayInstance.laiM DecayInstance.laiH 0 y - starRingEnd ℂ DecayInstance.laiM) /
      starRingEnd ℂ DecayInstance.laiH) := one_lt_jc_of_dlo laiH_cne hdlo0R hdl
  have := abs_potT_le (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
    laiH_cne (c := DecayGlue.laiC) (N := 8) DecayGlue.laiC_hpos
    (γ := armA DecayInstance.laiM DecayInstance.laiH) (x := y) (dlo := ((d.dq - bA d : ℚ) : ℝ))
    (Ym := fun _ => (bhq : ℝ)) hreg hdlo0R hdl
    (fun i hi1 _ => (norm_armA_le DecayInstance.laiM DecayInstance.laiH hi1 y).trans norm_laiH_le)
    hj1 hj5
  refine this.trans (le_of_eq ?_)
  rw [cast_fdb_rat]
  congr 1
  funext k
  push_cast
  rw [← cqL_real 0]


theorem Vf_eq (k : ℕ) : Vf DecayGlue.laiC 8 k = ((Vfq k : ℚ) : ℝ) := by
  unfold Vf Vfq
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [cqL_real]

theorem Vfq_nonneg (k : ℕ) : 0 ≤ Vfq k := by unfold Vfq; positivity

theorem puE_le (e : ECell) {r : ℝ} (c : ℚ) (k : ℕ) (h0 : 0 ≤ (rloE e : ℝ)) (h1 : (rloE e : ℝ) ≤ r)
    (h2 : r ≤ (rhiE e : ℝ)) : (c : ℝ) * r ^ k ≤ ((puE e c k : ℚ) : ℝ) := by
  unfold puE
  exact pu_le k h0 h1 h2

theorem pi_bounds : (4 * (PI4 - PI4E) : ℝ) ≤ Real.pi ∧ Real.pi ≤ 4 * (PI4 + PI4E) := by
  have h := abs_le.1 pi4_spec
  constructor <;> push_cast <;> linarith [h.1, h.2]

theorem pi_lo_nonneg : (0 : ℚ) ≤ 4 * (PI4 - PI4E) := by
  unfold PI4 PI4E PI4N; norm_num

theorem okE_sound {e : ECell} (hA : okA e.d = true) (hE : okE e = true) :
    (∀ j ≤ 4, |DecayGlue.crossT DecayGlue.laiC 8 j (Real.pi * (ncE e : ℝ) / 128) -
        ((tq2A e.d j : ℚ) : ℝ)| ≤ ((teE e j : ℚ) : ℝ)) ∧
    (∀ x ∈ Icc (Real.pi * (e.n0 : ℝ) / 128) (Real.pi * (e.n1 : ℝ) / 128),
        |DecayGlue.crossT DecayGlue.laiC 8 5 x| / 120 ≤ ((e.d.T2q : ℚ) : ℝ) / 120) ∧
    (∑ ij ∈ Finset.antidiagonal 5, supB (tq2A e.d) (teE e) (120 * ((e.d.T2q : ℝ) / 120))
        ((Real.pi * (e.n1 : ℝ) / 128 - Real.pi * (e.n0 : ℝ) / 128) / 2) ij.1 *
        Vf DecayGlue.laiC 8 ij.2 ≤ (e.Er : ℝ)) ∧
    crossCellBound (DecayGlue.crossT DecayGlue.laiC 8) DecayGlue.laiC 8 (Real.pi * (ncE e : ℝ) / 128)
      ((Real.pi * (e.n1 : ℝ) / 128 - Real.pi * (e.n0 : ℝ) / 128) / 2) (e.Er : ℝ) ≤ (e.Cb : ℝ) := by
  obtain ⟨hlo, hhi, hn01, hpar, ht0, ht1, ht2, ht3, ht4, hT0, hdlo, hEr, hCb⟩ := okEProp_parts hE
  obtain ⟨_, hcont, heps, hρ', hseg, hdist⟩ := okA_all hA
  have hAp := of_decide_eq_true hA
  obtain ⟨hτ, _, hargS, hρeps, hvS, hR, hRφ, hδ, hs, hlo0, hlo2, hdq0, hdq, hl2S, hY1, hY2, hY3, hY4,
    hdb, hT, hp1S, hp2S, hp3S, hTV, hTR, hok⟩ := hAp
  have hdlo' : 0 < e.d.dq - bA e.d := hdlo
  have hπ := pi_bounds
  have hπ4 : Real.pi < 3.1416 := Real.pi_lt_d4
  have hπ0 := Real.pi_pos
  have hn : (e.n0 : ℝ) ≤ e.n1 := by exact_mod_cast hn01
  have hnc : (ncE e : ℝ) * 2 = (e.n0 : ℝ) + e.n1 := by
    unfold ncE
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpar)
    exact_mod_cast this
  have hth : (thA e.d : ℝ) = (ncE e : ℝ) / 128 := by
    unfold thA
    push_cast
    rw [hlo, hhi]; push_cast
    linarith
  have hwE : (wE e : ℝ) = ((e.n1 : ℝ) - e.n0) / 256 := by unfold wE; push_cast; ring
  have hrr : (Real.pi * (e.n1 : ℝ) / 128 - Real.pi * (e.n0 : ℝ) / 128) / 2 = Real.pi * (wE e : ℝ) := by
    rw [hwE]; ring
  have hw0 : (0 : ℝ) ≤ (wE e : ℝ) := by rw [hwE]; linarith
  have hr0 : (0 : ℝ) ≤ Real.pi * (wE e : ℝ) := mul_nonneg hπ0.le hw0
  have hrlo : (rloE e : ℝ) ≤ Real.pi * (wE e : ℝ) := by
    unfold rloE; push_cast
    exact mul_le_mul_of_nonneg_right hπ.1 hw0
  have hrhi : Real.pi * (wE e : ℝ) ≤ (rhiE e : ℝ) := by
    unfold rhiE; push_cast
    exact mul_le_mul_of_nonneg_right hπ.2 hw0
  have hrlo0 : (0 : ℝ) ≤ (rloE e : ℝ) := by
    unfold rloE
    have hq : (e.n0 : ℚ) ≤ e.n1 := by exact_mod_cast hn01
    have hwQ : (0 : ℚ) ≤ wE e := by unfold wE; linarith
    have : (0 : ℚ) ≤ 4 * (PI4 - PI4E) * wE e := mul_nonneg pi_lo_nonneg hwQ
    exact_mod_cast this
  -- the A cell facts
  have hmI : Real.pi * (thA e.d : ℝ) ∈ Icc (2 * Real.arctan (e.d.τ : ℝ) - e.d.ρ')
      (2 * Real.arctan (e.d.τ : ℝ) + e.d.ρ') := by
    have h1 := abs_le.1 heps
    have h2 : ((rhoA e.d : ℚ) : ℝ) + (epsA2 (thA e.d) (argA e.d).1 (argA e.d).2 : ℝ) ≤ e.d.ρ' := by
      exact_mod_cast hρeps
    have h3 : (0 : ℝ) ≤ (rhoA e.d : ℝ) := by
      have : (0 : ℚ) ≤ rhoA e.d := by
        unfold rhoA
        have : e.d.lo ≤ e.d.hi := by
          rw [hlo, hhi]
          have : (e.n0 : ℚ) ≤ e.n1 := by exact_mod_cast hn01
          linarith
        linarith
      exact_mod_cast this
    constructor <;> linarith [h1.1, h1.2]
  have hcellsub : ∀ x ∈ Icc (Real.pi * (e.n0 : ℝ) / 128) (Real.pi * (e.n1 : ℝ) / 128),
      x ∈ Icc (2 * Real.arctan (e.d.τ : ℝ) - e.d.ρ') (2 * Real.arctan (e.d.τ : ℝ) + e.d.ρ') := by
    intro x hx
    apply hcont
    have hρ : ((rhoA e.d : ℚ) : ℝ) = (31416 / 10000 : ℝ) * (((e.n1 : ℝ) - e.n0) / 256) := by
      unfold rhoA; rw [hlo, hhi]; push_cast; ring
    have hb : Real.pi * (thA e.d : ℝ) - ((rhoA e.d : ℚ) : ℝ) ≤ Real.pi * (e.n0 : ℝ) / 128 := by
      rw [hth, hρ]
      nlinarith [mul_nonneg (sub_nonneg.2 hn) (sub_nonneg.2 hπ4.le), hnc]
    have hb2 : Real.pi * (e.n1 : ℝ) / 128 ≤ Real.pi * (thA e.d : ℝ) + ((rhoA e.d : ℚ) : ℝ) := by
      rw [hth, hρ]
      nlinarith [mul_nonneg (sub_nonneg.2 hn) (sub_nonneg.2 hπ4.le), hnc]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hB : ∀ j, 1 ≤ j → j ≤ 5 → ∀ y ∈ Icc (2 * Real.arctan (e.d.τ : ℝ) - e.d.ρ')
      (2 * Real.arctan (e.d.τ : ℝ) + e.d.ρ'),
      |DecayGlue.crossT DecayGlue.laiC 8 j y| ≤ ((BE e j : ℚ) : ℝ) := fun j hj1 hj5 =>
    crossT_bound hA hj1 hj5 hdlo'
  have hte : ∀ i, i ≤ 4 → 0 ≤ teE e i := by
    intro i hi; interval_cases i <;> assumption
  have hcen : ∀ j ≤ 4, |DecayGlue.crossT DecayGlue.laiC 8 j (Real.pi * (ncE e : ℝ) / 128) -
      ((tq2A e.d j : ℚ) : ℝ)| ≤ ((teE e j : ℚ) : ℝ) := by
    intro j hj
    have hT5 := isTower_cross (M := DecayInstance.laiM) (h := DecayInstance.laiH)
      (M' := starRingEnd ℂ DecayInstance.laiM) (h' := starRingEnd ℂ DecayInstance.laiH) laiH_cne
      DecayGlue.laiC_hpos lai_hsep (2 * Real.arctan (e.d.τ : ℝ)) (e.d.ρ' : ℝ)
    have hρ0 : (0 : ℝ) ≤ e.d.ρ' := by exact_mod_cast hρ'
    have haI : 2 * Real.arctan (e.d.τ : ℝ) ∈ Icc (2 * Real.arctan (e.d.τ : ℝ) - e.d.ρ')
        (2 * Real.arctan (e.d.τ : ℝ) + e.d.ρ') := ⟨by linarith, by linarith⟩
    have hmI' : Real.pi * (ncE e : ℝ) / 128 ∈ Icc (2 * Real.arctan (e.d.τ : ℝ) - e.d.ρ')
        (2 * Real.arctan (e.d.τ : ℝ) + e.d.ρ') := by
      have := hmI; rw [hth] at this; rwa [mul_div_assoc'] at this
    have hrec := tower_recentre hT5 haI hmI' hj (B := ((BE e (j + 1) : ℚ) : ℝ))
      (hB (j + 1) (by omega) (by omega))
    have hB0 : (0 : ℝ) ≤ ((BE e (j + 1) : ℚ) : ℝ) :=
      (abs_nonneg _).trans (hB (j + 1) (by omega) (by omega) _ haI)
    have hs1 := hseg j hj
    have heps' : |Real.pi * (ncE e : ℝ) / 128 - 2 * Real.arctan (e.d.τ : ℝ)| ≤ ((epsE e : ℚ) : ℝ) := by
      have := heps; rw [hth] at this; rwa [mul_div_assoc'] at this
    have h1 : |DecayGlue.crossT DecayGlue.laiC 8 j (Real.pi * (ncE e : ℝ) / 128) -
        DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ))| ≤
        ((BE e (j + 1) : ℚ) : ℝ) * ((epsE e : ℚ) : ℝ) :=
      hrec.trans (mul_le_mul_of_nonneg_left heps' hB0)
    have h2 : |DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ)) - ((tq2A e.d j : ℚ) : ℝ)|
        ≤ ((te2A e.d j : ℚ) : ℝ) := hs1
    have e1 : ((teE e j : ℚ) : ℝ) = ((te2A e.d j : ℚ) : ℝ) + ((epsE e : ℚ) : ℝ) * ((BE e (j + 1) : ℚ) : ℝ) := by
      unfold teE; push_cast; ring
    rw [e1]
    calc _ ≤ |DecayGlue.crossT DecayGlue.laiC 8 j (Real.pi * (ncE e : ℝ) / 128) -
          DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ))| +
        |DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ)) - ((tq2A e.d j : ℚ) : ℝ)| := by
          have := abs_add_le (DecayGlue.crossT DecayGlue.laiC 8 j (Real.pi * (ncE e : ℝ) / 128) -
            DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ)))
            (DecayGlue.crossT DecayGlue.laiC 8 j (2 * Real.arctan (e.d.τ : ℝ)) - ((tq2A e.d j : ℚ) : ℝ))
          simpa using this
      _ ≤ _ := by linarith
  refine ⟨hcen, ?_, ?_, ?_⟩
  · intro x hx
    have hxI := hcellsub x hx
    have hb5 := hB 5 (by norm_num) le_rfl x hxI
    have hT5q : BE e 5 ≤ e.d.T2q := hT
    have : |DecayGlue.crossT DecayGlue.laiC 8 5 x| ≤ ((e.d.T2q : ℚ) : ℝ) :=
      hb5.trans (by exact_mod_cast hT5q)
    exact div_le_div_of_nonneg_right this (by norm_num)
  · rw [hrr]
    have hT0R : (0 : ℝ) ≤ (e.d.T2q : ℝ) := by exact_mod_cast hT0
    have hsup : ∀ j, j ≤ 5 → supB (tq2A e.d) (teE e) (120 * ((e.d.T2q : ℝ) / 120)) (Real.pi * (wE e : ℝ)) j ≤
        ((supBq e j : ℚ) : ℝ) := by
      intro j hj
      unfold supB supBq
      have h120 : 120 * ((e.d.T2q : ℝ) / 120) = (e.d.T2q : ℝ) := by ring
      rw [h120]
      push_cast
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply add_le_add
      · apply Finset.sum_le_sum
        intro m hm
        have hm' := Finset.mem_range.1 hm
        have hnn : (0 : ℝ) ≤ (|(tq2A e.d (j + m) : ℝ)| + (teE e (j + m) : ℝ)) := by
          have := hte (j + m) (by omega)
          have h' : (0 : ℝ) ≤ (teE e (j + m) : ℝ) := by exact_mod_cast this
          positivity
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrhi m) hnn
      · apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hrhi _) hT0R
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    calc _ ≤ ∑ j ∈ Finset.range (5 + 1), ((supBq e j : ℚ) : ℝ) * ((Vfq (5 - j) : ℚ) : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          simp only
          rw [Vf_eq]
          exact mul_le_mul_of_nonneg_right (hsup j (by have := Finset.mem_range.1 hj; omega))
            (by exact_mod_cast Vfq_nonneg _)
      _ = ((∑ j ∈ Finset.range 6, supBq e j * Vfq (5 - j) : ℚ) : ℝ) := by push_cast; rfl
      _ ≤ _ := by exact_mod_cast hEr
  · rw [hrr]
    have hcc := fun (j : ℕ) (hj : j ≤ 4) =>
      mulTower_le_enc (Gt := DecayGlue.crossT DecayGlue.laiC 8) (Ft := Ftow DecayGlue.laiC 8)
        (a := Real.pi * (ncE e : ℝ) / 128) (gq := fun i => ((tq2A e.d i : ℚ) : ℝ))
        (ge := fun i => ((teE e i : ℚ) : ℝ)) (fq := fun i => ((fqE e i : ℚ) : ℝ))
        (fe := fun i => ((feE i : ℚ) : ℝ)) j (fun i hi => hcen i (by omega))
        (fun i hi => Ftow_enc (cq := cqL) 8 (fun k _ => cqL_real k) i (ncE e))
    have hu : ∀ j, j ≤ 4 → mulTower (DecayGlue.crossT DecayGlue.laiC 8) (Ftow DecayGlue.laiC 8) j
        (Real.pi * (ncE e : ℝ) / 128) ≤ ((mtE e j : ℚ) : ℝ) := by
      intro j hj
      refine (hcc j hj).trans (le_of_eq ?_)
      unfold mtE
      push_cast
      rfl
    have hfin := crossCellBound_le (DecayGlue.crossT DecayGlue.laiC 8) DecayGlue.laiC 8
      (a := Real.pi * (ncE e : ℝ) / 128) (r := Real.pi * (wE e : ℝ)) (E := (e.Er : ℝ)) hr0
      (hu 0 (by norm_num)) (hu 2 (by norm_num)) (hu 4 (by norm_num))
    have p1 := puE_le e (2 * mtE e 0) 1 hrlo0 hrlo hrhi
    have p3 := puE_le e (mtE e 2 / 3) 3 hrlo0 hrlo hrhi
    have p5 := puE_le e (mtE e 4 / 60) 5 hrlo0 hrlo hrhi
    have p6 := puE_le e (e.Er / 3) 6 hrlo0 hrlo hrhi
    have hcb : ((cbE e : ℚ) : ℝ) ≤ (e.Cb : ℝ) := by exact_mod_cast hCb
    have hcb' : ((cbE e : ℚ) : ℝ) = ((puE e (2 * mtE e 0) 1 : ℚ) : ℝ) + ((puE e (mtE e 2 / 3) 3 : ℚ) : ℝ) +
        ((puE e (mtE e 4 / 60) 5 : ℚ) : ℝ) + ((puE e (e.Er / 3) 6 : ℚ) : ℝ) := by
      unfold cbE; push_cast; ring
    refine hfin.trans ?_
    push_cast at p1 p3 p5 p6
    linarith [p1, p3, p5, p6, hcb, hcb']

/-- `okE_sound` with the partition endpoints `a0`, `a1` as variables. -/
theorem okE_sound2 {e : ECell} (hA : okA e.d = true) (hE : okE e = true) {a0 a1 : ℝ}
    (h0 : a0 = Real.pi * (e.n0 : ℝ) / 128) (h1 : a1 = Real.pi * (e.n1 : ℝ) / 128) :
    (∀ j ≤ 4, |DecayGlue.crossT DecayGlue.laiC 8 j ((a0 + a1) / 2) - ((tq2A e.d j : ℚ) : ℝ)| ≤
        ((teE e j : ℚ) : ℝ)) ∧
    (∀ x ∈ Icc a0 a1, |DecayGlue.crossT DecayGlue.laiC 8 5 x| / 120 ≤ ((e.d.T2q : ℚ) : ℝ) / 120) ∧
    (∑ ij ∈ Finset.antidiagonal 5, supB (tq2A e.d) (teE e) (120 * ((e.d.T2q : ℝ) / 120))
        ((a1 - a0) / 2) ij.1 * Vf DecayGlue.laiC 8 ij.2 ≤ (e.Er : ℝ)) ∧
    crossCellBound (DecayGlue.crossT DecayGlue.laiC 8) DecayGlue.laiC 8 ((a0 + a1) / 2)
      ((a1 - a0) / 2) (e.Er : ℝ) ≤ (e.Cb : ℝ) := by
  obtain ⟨_, _, _, hpar, _⟩ := okEProp_parts hE
  have hnc : (ncE e : ℝ) * 2 = (e.n0 : ℝ) + e.n1 := by
    unfold ncE
    have := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpar)
    exact_mod_cast this
  subst h0 h1
  have hπ : Real.pi * ((ncE e : ℝ) * 2) = Real.pi * ((e.n0 : ℝ) + e.n1) := by rw [hnc]
  have hc : (Real.pi * (e.n0 : ℝ) / 128 + Real.pi * (e.n1 : ℝ) / 128) / 2 =
      Real.pi * (ncE e : ℝ) / 128 := by linarith
  rw [hc]
  exact okE_sound hA hE

end

end CatalanCore.Lai.DecayEnergyCheck

#print axioms CatalanCore.Lai.DecayEnergyCheck.okE_sound2
