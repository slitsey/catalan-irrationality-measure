module

public import CatalanCore.Lai.DecayTowerV
public import CatalanCore.Lai.DecayGlue

@[expose] public section

/-!
# `CatalanCore.Lai.DecayCheck`: per-cell Boolean checkers of the Lai decay cover (T-data)

Part 0: global constants of Lai's design as rationals, the enclosure `κE` of the V constant, the
enclosure `K0E` of the own constant, `argQ` containment of the chain cell in the evaluation cell.
-/

open Set Real Finset
open CatalanCore.Zeta5.Potential CatalanMeasure.GenD.Signed.LogEval CatalanMeasure.Cert CatalanMeasure.CellCert
  OAI.InternalCatalan CatalanCore.Zeta5.Cells CatalanMeasure.GenD.Signed.TaylorCell
  CatalanCore.Tools.Joukowski CatalanCore.Decay.ComplexTaylor CatalanCore.Lai.DecayCells
  CatalanCore.Uniform.Decay.NearCells CatalanCore.Lai.DecayTowerSeg CatalanCore.Lai.DecayTowerV
  CatalanCore.Lai.DecayGlue CatalanCore.Lai.DecayInstance

namespace CatalanCore.Lai.DecayCheck

noncomputable section

/-! ### Constants of the design -/

def MG : GQ := ⟨737 / 400, 1067 / 1000⟩
def HG : GQ := ⟨93 / 400, 1023 / 1000⟩
def MC : CQ := ⟨737 / 400, -1067 / 1000⟩
def HC : CQ := ⟨93 / 400, -1023 / 1000⟩
def bhq : ℚ := 1100049 / 1048576
def ellq : ℚ := -130471 / 10000

theorem toC_MG : GQ.toC MG = DecayInstance.laiM := by
  apply Complex.ext <;> simp [GQ.toC, MG, DecayInstance.laiM]
theorem toC_HG : GQ.toC HG = DecayInstance.laiH := by
  apply Complex.ext <;> simp [GQ.toC, HG, DecayInstance.laiH]
theorem toC_MC : CQ.toC MC = starRingEnd ℂ DecayInstance.laiM := by
  apply Complex.ext <;> simp [CQ.toC, MC, DecayInstance.laiM] <;> ring
theorem toC_HC : CQ.toC HC = starRingEnd ℂ DecayInstance.laiH := by
  apply Complex.ext <;> simp [CQ.toC, HC, DecayInstance.laiH] <;> ring

theorem laiH_ne' : DecayInstance.laiH ≠ 0 := DecayInstance.laiH_ne
theorem laiH_cne : starRingEnd ℂ DecayInstance.laiH ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).2 DecayInstance.laiH_ne

theorem lai_hMh : |DecayInstance.laiH.im| < DecayInstance.laiM.im := by
  simp only [DecayInstance.laiH_im, DecayInstance.laiM_im]; norm_num [abs_of_pos]

theorem ell_eq : (ellq : ℝ) = DecayInstance.laiEll := by
  unfold ellq DecayInstance.laiEll; push_cast; norm_num

theorem nsq_HG : nsq HG ≤ bhq ^ 2 := by unfold nsq HG bhq; norm_num

theorem norm_laiH_le : ‖DecayInstance.laiH‖ ≤ (bhq : ℝ) := by
  have h1 : ‖GQ.toC HG‖ ^ 2 = ((nsq HG : ℚ) : ℝ) := norm_sq_toC HG
  rw [toC_HG] at h1
  have h2 : ((nsq HG : ℚ) : ℝ) ≤ (bhq : ℝ) ^ 2 := by exact_mod_cast nsq_HG
  have hb : (0 : ℝ) ≤ bhq := by unfold bhq; norm_num
  by_contra hc
  push Not at hc
  nlinarith [norm_nonneg DecayInstance.laiH]

/-- the own-potential coefficients `c_k` as rationals (literal list; `laiCq` is the definitional source). -/
def cqL : ℕ → ℚ := fun k => ([(3 / 2 : ℚ), (-28044550870449 / 46912495987199 : ℚ), (-57092645318385 / 46912495987199 : ℚ), (62105507661106 / 140737487961597 : ℚ), (-14878369728805 / 140737487961597 : ℚ), (7283330240408 / 140737487961597 : ℚ), (2580479367155 / 140737487961597 : ℚ), (208374684237 / 46912495987199 : ℚ), (1806765466792 / 140737487961597 : ℚ)] : List ℚ).getD k 0

/-! ### `κ` and `K0` enclosures -/

def kapE : ℚ × ℚ :=
  match logQ 8 6, logQ 8 2 with
  | some (l6, e6), some (l2, e2) => (12 * l6 - 6 * l2 - 6, 12 * e6 + 6 * e2)
  | _, _ => (0, 0)

theorem kapE_ok : (logQ 8 6).isSome = true ∧ (logQ 8 2).isSome = true := by decide +kernel

theorem kapE_enc : Enc (2 * (6 * Real.log 6 - 6) - 3 * (2 * Real.log 2 - 2)) kapE := by
  obtain ⟨h6, h2⟩ := kapE_ok
  obtain ⟨⟨l6, e6⟩, hl6⟩ := Option.isSome_iff_exists.1 h6
  obtain ⟨⟨l2, e2⟩, hl2⟩ := Option.isSome_iff_exists.1 h2
  have s6 := (logQ_spec hl6).2
  have s2 := (logQ_spec hl2).2
  unfold kapE; rw [hl6, hl2]
  unfold Enc at s6 s2 ⊢
  push_cast at s6 s2 ⊢
  rw [abs_le] at s6 s2 ⊢
  constructor <;> nlinarith [s6.1, s6.2, s2.1, s2.2]


theorem cqL_eq (k : ℕ) : cqL k = DecayGlue.laiCq k := by
  by_cases hk : k < 9
  · interval_cases k <;> decide +kernel
  · have h9 : 9 ≤ k := by omega
    have h1 : cqL k = 0 := by
      unfold cqL
      exact List.getD_eq_default _ _ (by simp; omega)
    have h2 : DecayGlue.laiCq k = 0 := by
      unfold DecayGlue.laiCq aI
      have : ¬ k = 0 := by omega
      simp [this, show 9 - k = 0 by omega]
    rw [h1, h2]

theorem cqL_real (k : ℕ) : (cqL k : ℝ) = DecayGlue.laiC k := by
  rw [cqL_eq, DecayGlue.laiC_eq_q]

def K0E : ℚ × ℚ :=
  match logQ 8 HC.nsq, logQ 8 2 with
  | some (l1, e1), some (l2, e2) => (-(3 / 2) * l1 / 2 + (3 / 2) * l2, (3 / 2) * e1 / 2 + (3 / 2) * e2)
  | _, _ => (0, 0)

theorem K0_ok : (logQ 8 HC.nsq).isSome = true ∧ (logQ 8 2).isSome = true := by decide +kernel

theorem K0_enc : |(-DecayGlue.laiC 0 * Real.log ‖DecayInstance.laiH‖ + DecayGlue.laiC 0 * Real.log 2) - (K0E.1 : ℝ)| ≤ (K0E.2 : ℝ) := by
  obtain ⟨h1, h2⟩ := K0_ok
  obtain ⟨⟨l1, e1⟩, hl1⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨⟨l2, e2⟩, hl2⟩ := Option.isSome_iff_exists.1 h2
  have s1 := (logQ_spec hl1).2
  have s2 := (logQ_spec hl2).2
  have hn : ‖DecayInstance.laiH‖ ^ 2 = ((HC.nsq : ℚ) : ℝ) := by
    have h := norm_sq_toC HG
    rw [toC_HG] at h
    rw [h]; unfold nsq CQ.nsq HG HC; push_cast; ring
  have hlog : Real.log ‖DecayInstance.laiH‖ = Real.log ((HC.nsq : ℚ) : ℝ) / 2 := by
    rw [← hn, Real.log_pow]; push_cast; ring
  rw [DecayGlue.laiC_zero, hlog]
  unfold K0E; rw [hl1, hl2]
  unfold Enc at s1 s2
  push_cast at s1 s2 ⊢
  rw [abs_le] at s1 s2 ⊢
  constructor <;> nlinarith [s1.1, s1.2, s2.1, s2.2]

theorem opt_some {α : Type*} {o : Option α} (x : α) (h : o.isSome = true) : o = some (o.getD x) := by
  cases o <;> simp_all

/-! ### A cells -/

def epsA2 (θ v e : ℚ) : ℚ := |θ| * (4 * PI4E) + |4 * PI4 * θ - v| + e

theorem arg_two_arctan (τ : ℚ) (hτ : 0 ≤ τ) :
    Complex.arg ⟨((((1 - τ ^ 2) / (1 + τ ^ 2) : ℚ)) : ℝ), (((2 * τ / (1 + τ ^ 2) : ℚ)) : ℝ)⟩ =
      2 * Real.arctan (τ : ℝ) := by
  obtain ⟨hc, hs⟩ := cos_two_arctan_q τ
  have h0 : 0 ≤ 2 * Real.arctan (τ : ℝ) := by
    have := Real.arctan_nonneg.2 (by exact_mod_cast hτ : (0 : ℝ) ≤ τ); linarith
  have h1 : 2 * Real.arctan (τ : ℝ) ≤ Real.pi := by
    have := Real.arctan_lt_pi_div_two (τ : ℝ); linarith
  have e : (⟨((((1 - τ ^ 2) / (1 + τ ^ 2) : ℚ)) : ℝ), (((2 * τ / (1 + τ ^ 2) : ℚ)) : ℝ)⟩ : ℂ) =
      ((Real.cos (2 * Real.arctan (τ : ℝ)) : ℝ) : ℂ) + ((Real.sin (2 * Real.arctan (τ : ℝ)) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      rw [hc]; ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      rw [hs]; ring
  rw [e, Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], h1⟩

theorem epsA2_spec {n : ℕ} {τ θ v e : ℚ} (hτ : 0 ≤ τ)
    (h : argQ n ((1 - τ ^ 2) / (1 + τ ^ 2)) (2 * τ / (1 + τ ^ 2)) = some (v, e)) :
    |Real.pi * (θ : ℝ) - 2 * Real.arctan (τ : ℝ)| ≤ (epsA2 θ v e : ℝ) := by
  have h1 := argQ_spec h
  rw [arg_two_arctan τ hτ] at h1
  have h2 := pi4_spec
  unfold epsA2
  push_cast
  have e1 : Real.pi * (θ : ℝ) - 2 * Real.arctan (τ : ℝ) =
      (θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ))) + (4 * (PI4 : ℝ) * θ - (v : ℝ)) +
        ((v : ℝ) - 2 * Real.arctan (τ : ℝ)) := by ring
  rw [e1]
  have a1 : |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ)))| ≤ |(θ : ℝ)| * (4 * (PI4E : ℝ)) := by
    rw [abs_mul, abs_mul]
    have : |(4 : ℝ)| = 4 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left (by nlinarith [h2]) (abs_nonneg _)
  have a3 : |(v : ℝ) - 2 * Real.arctan (τ : ℝ)| ≤ (e : ℝ) := by
    rw [abs_sub_comm]; exact h1
  calc _ ≤ |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ))) + (4 * (PI4 : ℝ) * θ - (v : ℝ))| +
        |(v : ℝ) - 2 * Real.arctan (τ : ℝ)| := abs_add_le _ _
    _ ≤ |(θ : ℝ) * (4 * (Real.pi / 4 - (PI4 : ℝ)))| + |4 * (PI4 : ℝ) * θ - (v : ℝ)| +
        |(v : ℝ) - 2 * Real.arctan (τ : ℝ)| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by linarith

theorem contain_A2 {n : ℕ} {τ θ v e ρ ρ' : ℚ} (hτ : 0 ≤ τ)
    (h : argQ n ((1 - τ ^ 2) / (1 + τ ^ 2)) (2 * τ / (1 + τ ^ 2)) = some (v, e))
    (hρ : ρ + epsA2 θ v e ≤ ρ') :
    ∀ x ∈ Icc (Real.pi * (θ : ℝ) - ρ) (Real.pi * (θ : ℝ) + ρ),
      x ∈ Icc (2 * Real.arctan (τ : ℝ) - ρ') (2 * Real.arctan (τ : ℝ) + ρ') := by
  intro x hx
  have h1 := abs_le.mp (epsA2_spec (θ := θ) hτ h)
  have h2 : (ρ : ℝ) + (epsA2 θ v e : ℝ) ≤ ρ' := by exact_mod_cast hρ
  constructor <;> linarith [hx.1, hx.2]

structure ACell where
  lo : ℚ
  hi : ℚ
  τ : ℚ
  ρ' : ℚ
  φq : CQ
  R : ℚ
  δ : ℚ
  hlo : ℚ
  dq : ℚ
  T2q : ℚ
  TV : ℚ
  TR : ℚ
  q1 : ℚ
  p1 : ℚ
  q2 : ℚ
  p2 : ℚ
  q3 : ℚ
  p3 : ℚ

def thA (d : ACell) : ℚ := (d.lo + d.hi) / 2
def rhoA (d : ACell) : ℚ := (31416 / 10000) * (d.hi - d.lo) / 2
def sqA (d : ACell) : GQ :=
  ⟨MG.re + HG.re * ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)), MG.im + HG.im * ((1 - d.τ ^ 2) / (1 + d.τ ^ 2))⟩
def YA (d : ACell) : ℕ → GQ :=
  fun i => GQ.sc (cosJ ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2)) i) HG
def toCQ (x : GQ) : CQ := ⟨x.re, x.im⟩
def argA (d : ACell) : ℚ × ℚ :=
  (argQ 8 ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2))).getD (0, 0)
def vo3 : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) := ((0, 0), (0, 0), (0, 0))
def voA (d : ACell) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) := (vEncOut 8 8 kapE (sqA d)).getD vo3
def segA (d : ACell) : SegQ := { hq := HC, φq := d.φq, cq := cqL, N := 8 }
def l1C : ℚ × ℚ := (logQ 8 HC.nsq).getD (0, 0)
def l2A (d : ACell) : ℚ × ℚ := (logQ 8 (d.φq.nsq / 4)).getD (0, 0)
def tq2A (d : ACell) : ℕ → ℚ := (segA d).Tq l1C.1 (l2A d).1 (fun i => toCQ (YA d i))
def te2A (d : ACell) : ℕ → ℚ := (segA d).Te l1C.2 (l2A d).2 d.dq d.δ (fun _ => bhq)
def bA (d : ACell) : ℚ := bhq * d.ρ'
def LA (d : ACell) (n q p : ℚ) : ℚ := (vPole 8 n q p (bA d)).getD 0
def wcA (d : ACell) : Bool :=
  wedgeCellOk
    (wTq (vTW (voA d).1 (voA d).2.1 (voA d).2.2 (sqA d) (YA d)).1
      (fun j => ownATr K0E.1 cqL 8 j ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2))) (tq2A d))
    (wTe (vTW (voA d).1 (voA d).2.1 (voA d).2.2 (sqA d) (YA d)).2
      (fun j => if j = 0 then K0E.2 else 0) (te2A d)) d.TR d.ρ' ellq

@[reducible] def okAProp (d : ACell) : Prop :=
  0 ≤ d.τ ∧ 0 ≤ d.ρ' ∧
  (argQ 8 ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2))).isSome = true ∧
  rhoA d + epsA2 (thA d) (argA d).1 (argA d).2 ≤ d.ρ' ∧
  (vEncOut 8 8 kapE (sqA d)).isSome = true ∧
  1 < d.R ∧ d.R ^ 2 ≤ d.φq.nsq ∧ 0 ≤ d.δ ∧
  ((toCQ (sqA d)).sub (MC.add (HC.mul (segA d).ζ))).nsq ≤ d.δ ^ 2 ∧
  0 ≤ d.hlo ∧ d.hlo ^ 2 ≤ HC.nsq ∧ 0 < d.dq ∧ d.dq ≤ d.hlo * ((d.R + d.R⁻¹) / 2 - 1) - d.δ ∧
  (logQ 8 (d.φq.nsq / 4)).isSome = true ∧
  (toCQ (YA d 1)).nsq ≤ bhq ^ 2 ∧ (toCQ (YA d 2)).nsq ≤ bhq ^ 2 ∧ (toCQ (YA d 3)).nsq ≤ bhq ^ 2 ∧ (toCQ (YA d 4)).nsq ≤ bhq ^ 2 ∧
  0 < d.dq - bA d ∧
  fdbBound (fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (d.dq - bA d) ^ k) (fun _ => bhq) ≤ d.T2q ∧
  (vPole 8 (nsq (sqA d)) d.q1 d.p1 (bA d)).isSome = true ∧
  (vPole 8 (nsq (GQ.sub ⟨2, 0⟩ (sqA d))) d.q2 d.p2 (bA d)).isSome = true ∧
  (vPole 8 (nsq (GQ.add (sqA d) ⟨6, 0⟩)) d.q3 d.p3 (bA d)).isSome = true ∧
  fdbBound (psiDmQ (d.q1 - bA d) (d.q2 - bA d) (d.q3 - bA d)
    (LA d (nsq (sqA d)) d.q1 d.p1) (LA d (nsq (GQ.sub ⟨2, 0⟩ (sqA d))) d.q2 d.p2)
    (LA d (nsq (GQ.add (sqA d) ⟨6, 0⟩)) d.q3 d.p3)) (fun _ => bhq) ≤ d.TV ∧
  d.TV + 2 * ownSumQ cqL 8 + 2 * d.T2q ≤ d.TR ∧
  wcA d = true

def okA (d : ACell) : Bool := decide (okAProp d)

theorem toC_toCQ (x : GQ) : CQ.toC (toCQ x) = GQ.toC x := rfl

theorem toC_lin (m h : GQ) (c : ℚ) :
    GQ.toC m + GQ.toC h * ((c : ℚ) : ℂ) = GQ.toC ⟨m.re + h.re * c, m.im + h.im * c⟩ := by
  apply Complex.ext <;> simp [GQ.toC]

theorem okA_all {d : ACell} (hd : okA d = true) :
    (∀ x ∈ Icc (Real.pi * (thA d : ℝ) - (rhoA d : ℝ)) (Real.pi * (thA d : ℝ) + (rhoA d : ℝ)),
      Wan DecayGlue.laiC 8 (DecayInstance.laiM + DecayInstance.laiH * ((Real.cos x : ℝ) : ℂ)) ≤
        DecayInstance.laiEll) ∧
    (∀ x ∈ Icc (Real.pi * (thA d : ℝ) - (rhoA d : ℝ)) (Real.pi * (thA d : ℝ) + (rhoA d : ℝ)),
      x ∈ Icc (2 * Real.arctan (d.τ : ℝ) - d.ρ') (2 * Real.arctan (d.τ : ℝ) + d.ρ')) ∧
    |Real.pi * (thA d : ℝ) - 2 * Real.arctan (d.τ : ℝ)| ≤ ((epsA2 (thA d) (argA d).1 (argA d).2 : ℚ) : ℝ) ∧
    0 ≤ d.ρ' ∧
    (∀ j ≤ 4, |potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) DecayGlue.laiC 8
      (armA DecayInstance.laiM DecayInstance.laiH) j (2 * Real.arctan (d.τ : ℝ)) -
        ((tq2A d j : ℚ) : ℝ)| ≤ ((te2A d j : ℚ) : ℝ)) ∧
    (∀ y ∈ Icc (2 * Real.arctan (d.τ : ℝ) - d.ρ') (2 * Real.arctan (d.τ : ℝ) + d.ρ'),
      ((d.dq - bA d : ℚ) : ℝ) ≤ ‖starRingEnd ℂ DecayInstance.laiH‖ *
        (jc ((armA DecayInstance.laiM DecayInstance.laiH 0 y - starRingEnd ℂ DecayInstance.laiM) /
          starRingEnd ℂ DecayInstance.laiH) - 1)) := by
  have hp : okAProp d := of_decide_eq_true hd
  obtain ⟨hτ, hρ', hargS, heps, hvS, hR, hRφ, hδ, hs, hlo0, hlo2, hdq0, hdq, hl2S, hY1, hY2, hY3, hY4,
    hdb, hT, hp1S, hp2S, hp3S, hTV, hTR, hok⟩ := hp
  have hargE : argQ 8 ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2)) = some (argA d) :=
    opt_some (0, 0) hargS
  have hcont := contain_A2 (θ := thA d) (ρ := rhoA d) hτ hargE heps
  have hvE : vEncOut 8 8 kapE (sqA d) = some (voA d) := opt_some vo3 hvS
  have hl1 : logQ 8 HC.nsq = some l1C := opt_some (0, 0) K0_ok.1
  have hl2 : logQ 8 (d.φq.nsq / 4) = some (l2A d) := opt_some (0, 0) hl2S
  obtain ⟨hc, hs'⟩ := cos_two_arctan_q d.τ
  have hz : armA DecayInstance.laiM DecayInstance.laiH 0 (2 * Real.arctan (d.τ : ℝ)) =
      CQ.toC (toCQ (sqA d)) := by
    rw [armA_rat _ _ hc hs' 0, if_pos rfl, ← toC_MG, ← toC_HG, toC_lin, toC_toCQ]
    have e0 : cosJ ((1 - d.τ ^ 2) / (1 + d.τ ^ 2)) (2 * d.τ / (1 + d.τ ^ 2)) 0 =
        (1 - d.τ ^ 2) / (1 + d.τ ^ 2) := by simp [cosJ]
    rw [e0]; rfl
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 →
      armA DecayInstance.laiM DecayInstance.laiH i (2 * Real.arctan (d.τ : ℝ)) =
        CQ.toC (toCQ (YA d i)) := by
    intro i hi _
    rw [armA_rat _ _ hc hs' i, if_neg (by omega), zero_add, toC_toCQ, YA, GQ.toC_sc, toC_HG, mul_comm]
  have hρR : (0 : ℝ) ≤ (d.ρ' : ℝ) := by exact_mod_cast hρ'
  have hρR' : 0 ≤ d.ρ' := hρ'
  have hne : HC.nsq ≠ 0 := by decide +kernel
  have hseg : ∀ j ≤ 4, |potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) DecayGlue.laiC 8
      (armA DecayInstance.laiM DecayInstance.laiH) j (2 * Real.arctan (d.τ : ℝ)) - ((tq2A d j : ℚ) : ℝ)| ≤
        ((te2A d j : ℚ) : ℝ) :=
    segTower_encQ (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (segA d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqA d)) toC_MC toC_HC hne
      (γ := armA DecayInstance.laiM DecayInstance.laiH) (x := 2 * Real.arctan (d.τ : ℝ))
      (fun i => toCQ (YA d i)) (fun _ => bhq) hz hYi
      (fun i hi1 hi4 => ⟨by unfold bhq; norm_num, by
        interval_cases i <;> assumption⟩)
      d.R d.δ d.dq d.hlo l1C.1 l1C.2 (l2A d).1 (l2A d).2 8 8 hR hRφ hδ hs hlo0 hlo2 hdq0 hdq hl1 hl2
  let X : SegCell (CQ.toC (toCQ (sqA d)))
      (fun _ => ‖DecayInstance.laiH‖) (d.ρ' : ℝ) (starRingEnd ℂ DecayInstance.laiM)
      (starRingEnd ℂ DecayInstance.laiH) (DecayGlue.laiC 0) (d.T2q : ℝ) :=
    segCell_of_enc (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (segA d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqA d)) toC_MC toC_HC hne
      d.R d.δ d.dq d.hlo hR hRφ hδ hs hlo0 hlo2 hdq
      (Ym := fun _ => ‖DecayInstance.laiH‖) (ρ := (d.ρ' : ℝ)) hρR (b := bA d)
      (by unfold bA; push_cast; exact mul_le_mul_of_nonneg_right norm_laiH_le hρR)
      (YmQ := fun _ => bhq) (fun i _ _ => ⟨norm_nonneg _, norm_laiH_le⟩) hdb hT
  have hXd : X.dlo = ((d.dq - bA d : ℚ) : ℝ) := rfl
  have hX : SegCell (armA DecayInstance.laiM DecayInstance.laiH 0 (2 * Real.arctan (d.τ : ℝ)))
      (fun _ => ‖DecayInstance.laiH‖) (d.ρ' : ℝ) (starRingEnd ℂ DecayInstance.laiM)
      (starRingEnd ℂ DecayInstance.laiH) (DecayGlue.laiC 0) (d.T2q : ℝ) := by
    rw [hz]; exact X
  have key := cellA_rat (c := DecayGlue.laiC) (N := 8) DecayGlue.laiC_hpos DecayInstance.laiH_ne lai_hMh toC_MG toC_HG d.τ hρ'
    (nL := 8) (nA := 8) kapE_enc (t0 := (voA d).1) (d1r := (voA d).2.1) (d1i := (voA d).2.2) hvE
    (K0q := K0E.1) (eK := K0E.2) K0_enc (cq := cqL) (fun k _ => cqL_real (k + 1)) laiH_cne DecayGlue.laiC_hpos
    (tq2 := tq2A d) (te2 := te2A d) hseg hX (bh := bhq) norm_laiH_le
    (opt_some 0 hp1S) (opt_some 0 hp2S) (opt_some 0 hp3S) hTV (ℓ := ellq) hTR hok
  refine ⟨fun x hx => ?_, hcont, epsA2_spec hτ hargE, hρR', hseg, ?_⟩
  · have := key x (hcont x hx)
    rw [ell_eq] at this
    exact this
  · intro y hy
    have hh := X.hdlo
    rw [hXd, ← hz] at hh
    exact dlo_cell laiH_cne (γ := armA DecayInstance.laiM DecayInstance.laiH 0)
      (γ' := armA DecayInstance.laiM DecayInstance.laiH 1)
      (fun x => hasDerivAt_armA DecayInstance.laiM DecayInstance.laiH 0 x)
      (S := ‖DecayInstance.laiH‖)
      (fun x _ => norm_armA_le DecayInstance.laiM DecayInstance.laiH (le_refl 1) x) hh hy

theorem okA_sound {d : ACell} (hd : okA d = true) :
    ∀ x ∈ Icc (Real.pi * (thA d : ℝ) - (rhoA d : ℝ)) (Real.pi * (thA d : ℝ) + (rhoA d : ℝ)),
      Wan DecayGlue.laiC 8 (DecayInstance.laiM + DecayInstance.laiH * ((Real.cos x : ℝ) : ℂ)) ≤
        DecayInstance.laiEll := (okA_all hd).1

/-! ### `cellG_rat'`: `cellG_rat` with the domain hypothesis `hIm` replaced by `hD` -/

theorem cellG_rat' {c : ℕ → ℝ} {N : ℕ} (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    {M h : ℂ} (hh : h ≠ 0) {Mq hq : GQ} (hM : GQ.toC Mq = M) (hH : GQ.toC hq = h)
    {sg : ℚ} (hsg : sg = 1 ∨ sg = -1) {ρq ρ' : ℚ} (hρq : 0 < ρq) (hρq1 : ρq ≤ 1) (hρ' : 0 ≤ ρ')
    (hρ'1 : ρ' < 1)
    (hD : (0 < M.im + h.im * (sg : ℝ) * 1 ∧
        0 < M.im + h.im * (sg : ℝ) * ((chQ (ρq * (1 - ρ')) 0 : ℚ) : ℝ)) ∨
      (0 < M.re + h.re * (sg : ℝ) * 1 ∧ M.re + h.re * (sg : ℝ) * 1 < 2 ∧
        0 < M.re + h.re * (sg : ℝ) * ((chQ (ρq * (1 - ρ')) 0 : ℚ) : ℝ) ∧
        M.re + h.re * (sg : ℝ) * ((chQ (ρq * (1 - ρ')) 0 : ℚ) : ℝ) < 2))
    {nL nA : ℕ} {κE t0 d1r d1i : ℚ × ℚ}
    (hκ : Enc (2 * (6 * Real.log 6 - 6) - 3 * (2 * Real.log 2 - 2)) κE)
    (hv : vEncOut nL nA κE
      ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩ = some (t0, d1r, d1i))
    {K0q eK c0q lq el : ℚ} (hK0 : |(-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) - (K0q : ℝ)| ≤ (eK : ℝ))
    (hc0 : (c0q : ℝ) = c 0) (hl : |Real.log (ρq : ℝ) - (lq : ℝ)| ≤ (el : ℝ))
    {cq : ℕ → ℚ} (hcq : ∀ k < N, (cq (k + 1) : ℝ) = c (k + 1))
    {M₂ h₂ : ℂ} (hh₂ : h₂ ≠ 0) {c₂ : ℕ → ℝ} {N₂ : ℕ}
    (hpos₂ : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c₂ N₂ x) {tq2 te2 : ℕ → ℚ}
    (hseg : ∀ j ≤ 4, |potT M₂ h₂ c₂ N₂ (armG M h (sg : ℝ)) j (-Real.log (ρq : ℝ)) - (tq2 j : ℝ)| ≤
      (te2 j : ℝ))
    {T2q : ℚ}
    (hX : SegCell (armG M h (sg : ℝ) 0 (-Real.log (ρq : ℝ)))
      (YmG h (-Real.log ((ρq * (1 - ρ') : ℚ) : ℝ))) (ρ' : ℝ) M₂ h₂ (c₂ 0) (T2q : ℝ))
    {bh : ℚ} (hbh : ‖h‖ ≤ (bh : ℝ)) {q1 q2 q3 p1 p2 p3 L1 L2 L3 : ℚ}
    (h1 : vPole nL (nsq ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩)
      q1 p1 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L1)
    (h2 : vPole nL (nsq (GQ.sub ⟨2, 0⟩
      ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩))
      q2 p2 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L2)
    (h3 : vPole nL (nsq (GQ.add ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
      ⟨6, 0⟩)) q3 p3 (bh * chQ (ρq * (1 - ρ')) 1 * ρ') = some L3)
    {TV : ℚ}
    (hTV : fdbBound (psiDmQ (q1 - bh * chQ (ρq * (1 - ρ')) 1 * ρ')
      (q2 - bh * chQ (ρq * (1 - ρ')) 1 * ρ') (q3 - bh * chQ (ρq * (1 - ρ')) 1 * ρ') L1 L2 L3)
      (fun i => bh * chQ (ρq * (1 - ρ')) i) ≤ TV)
    {TR ℓ : ℚ} (hTR : TV + 2 * ownSumGQ cq N (ρq / (1 - ρ')) + 2 * T2q ≤ TR)
    (hok : wedgeCellOk
      (wTq (vTW t0 d1r d1i ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
        (fun i => GQ.sc (sg * chQ ρq i) hq)).1
        (fun j => ownGTq K0q c0q sg (fun k => cq k) N j ρq lq) tq2)
      (wTe (vTW t0 d1r d1i ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩
        (fun i => GQ.sc (sg * chQ ρq i) hq)).2
        (fun j => if j = 0 then eK + |c0q| * el else 0) te2) TR ρ' ℓ = true) :
    ∀ x ∈ Icc (-Real.log (ρq : ℝ) - ρ') (-Real.log (ρq : ℝ) + ρ'), 0 ≤ x →
      vAnal 3 2 2 6 (2 * Real.pi) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) +
        (-2) * logPotC (segMeasure M h c N) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) +
        (-2) * logPotC (segMeasure M₂ h₂ c₂ N₂) (M + h * (((sg : ℝ) * Real.cosh x : ℝ) : ℂ)) ≤
          (ℓ : ℝ) := by
  have hρR : (0 : ℝ) < (ρq : ℝ) := by exact_mod_cast hρq
  have hρ'R : (0 : ℝ) ≤ (ρ' : ℝ) := by exact_mod_cast hρ'
  have hρ'1R : (ρ' : ℝ) < 1 := by exact_mod_cast hρ'1
  have hρ1R : (ρq : ℝ) ≤ 1 := by exact_mod_cast hρq1
  set ρh : ℚ := ρq * (1 - ρ') with hρh
  have hρh0 : (0 : ℝ) < (ρh : ℝ) := by
    rw [hρh]; push_cast; exact mul_pos hρR (by linarith)
  have hρh1 : (ρh : ℝ) ≤ 1 := by
    rw [hρh]; push_cast; nlinarith
  set s : ℝ := (sg : ℝ) with hsdef
  have hs1 : s = 1 ∨ s = -1 := by
    rcases hsg with h | h <;> simp [hsdef, h]
  set a : ℝ := -Real.log (ρq : ℝ) with ha
  set whi : ℝ := -Real.log ((ρh : ℚ) : ℝ) with hwdef
  have hcoshw : ∀ i, YmG h whi i = ‖h‖ * ((chQ ρh i : ℚ) : ℝ) := by
    intro i
    unfold YmG
    rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
    by_cases hi : i % 2 = 0
    · simp [hi, hwdef, cosh_neg_log hρh0]
    · simp [hi, hwdef, sinh_neg_log hρh0]
  have hch0 : ∀ i, (0 : ℝ) ≤ ((chQ ρh i : ℚ) : ℝ) := by
    intro i
    rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
    split_ifs
    · have : (0 : ℝ) < (ρh : ℝ)⁻¹ := inv_pos.2 hρh0
      linarith
    · have h1 : (ρh : ℝ) ≤ 1 := hρh1
      have h2 : (1 : ℝ) ≤ (ρh : ℝ)⁻¹ := (one_le_inv₀ hρh0).2 h1
      linarith
  have hY0 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ YmG h whi i := fun i _ _ => by
    rw [hcoshw]; exact mul_nonneg (norm_nonneg _) (hch0 i)
  have hρ : (0 : ℝ) ≤ (ρ' : ℝ) := hρ'R
  have hb : YmG h whi 1 * (ρ' : ℝ) ≤ ((bh * chQ ρh 1 * ρ' : ℚ) : ℝ) := by
    rw [hcoshw]; push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbh (hch0 1)) hρ
  have hYQ : ∀ i, 1 ≤ i → i ≤ 5 → YmG h whi i ≤ (((fun i => bh * chQ ρh i) i : ℚ) : ℝ) := by
    intro i _ _
    rw [hcoshw]; push_cast
    exact mul_le_mul_of_nonneg_right hbh (hch0 i)
  set sq : GQ := ⟨Mq.re + hq.re * (sg * chQ ρq 0), Mq.im + hq.im * (sg * chQ ρq 0)⟩ with hsq
  set Yq : ℕ → GQ := fun i => GQ.sc (sg * chQ ρq i) hq with hYq
  have hρq' : 0 < ρq := hρq
  have harm : ∀ i, armG M h s i a = (if i = 0 then M else 0) +
      h * (((sg * chQ ρq i : ℚ) : ℝ) : ℂ) := by
    intro i
    have hc := chQ_spec hρq' i
    rw [ha, armG_neg_log M h s hρR i]
    simp only [Rat.cast_mul, Complex.ofReal_mul]
    rw [← hc]
  have hz : armG M h s 0 a = GQ.toC sq := by
    rw [harm 0, if_pos rfl, ← hM, ← hH, hsq]
    apply Complex.ext <;> simp [GQ.toC] <;> (try ring)
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → armG M h s i a = GQ.toC (Yq i) := by
    intro i hi _
    rw [harm i, if_neg (by omega), zero_add, hYq, GQ.toC_sc, hH]
    push_cast
    ring
  have hV := mkVCell (nL := nL) (z := sq) (Ym := YmG h whi) (ρ := (ρ' : ℝ)) hρ hY0 hb h1 h2 h3
    hYQ hTV
  rw [← hz] at hV
  have hTenc := cell_tenc (γ := armG M h s) (a := a)
    (f₁ := ownGT (-c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c 0) s c N)
    (f₂ := potT M₂ h₂ c₂ N₂ (armG M h s)) hκ hv hz hYi
    (tq1 := fun j => ownGTq K0q c0q sg (fun k => cq k) N j ρq lq)
    (te1 := fun j => if j = 0 then eK + |c0q| * el else 0)
    (fun j _ => by
      have := ownGT_enc_rho (K0 := -c 0 * Real.log ‖h‖ + c 0 * Real.log 2) (c0 := c 0) (s := s)
        (K0q := K0q) (eK := eK) (c0q := c0q) (sq := sg) (ρq := ρq) (lq := lq) (el := el)
        (w := c) (wq := fun k => cq k) N hK0 hc0 rfl hcq hρR hl j
      by_cases hj0 : j = 0
      · subst hj0
        simp only [if_true, Rat.cast_add, Rat.cast_mul, Rat.cast_abs, hc0] at this ⊢
        exact this
      · simpa [hj0] using this)
    hseg
  have hwhi : ∀ x ∈ Icc (a - ρ') (a + ρ'), |x| ≤ whi := by
    intro x hx
    have hlog1 : Real.log (1 - (ρ' : ℝ)) ≤ -(ρ' : ℝ) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - ρ' by linarith)
      linarith
    have hw : a + ρ' ≤ whi := by
      rw [hwdef, hρh]
      push_cast
      rw [Real.log_mul hρR.ne' (by linarith)]
      rw [ha]; linarith
    have ha0 : 0 ≤ a := by
      rw [ha]; have := Real.log_nonpos hρR.le hρ1R; linarith
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hdom : ∀ x ∈ Icc (a - ρ') (a + ρ'), psiDom 2 6 (M + h * ((s * Real.cosh x : ℝ) : ℂ)) := by
    intro x hx
    have hxw := hwhi x hx
    have hc1 : Real.cosh x ≤ Real.cosh whi :=
      Real.cosh_le_cosh.2 (by rw [abs_of_nonneg (abs_nonneg x |>.trans hxw)]; exact hxw)
    have hc2 : Real.cosh whi = ((chQ ρh 0 : ℚ) : ℝ) := by
      rw [← chQ_spec (by rw [hρh]; exact mul_pos hρq (by linarith [show (ρ' : ℚ) < 1 from hρ'1]))]
      simp [hwdef, cosh_neg_log hρh0]
    have hc3 : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have hcx : Real.cosh x ≤ ((chQ ρh 0 : ℚ) : ℝ) := hc1.trans hc2.le
    rcases hD with ⟨hD1, hD2⟩ | ⟨hR1, hR2, hR3, hR4⟩
    · apply psiDom_of_im_pos
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        add_zero]
      rcases le_total 0 (h.im * s) with hh0 | hh0
      · nlinarith [mul_le_mul_of_nonneg_left hc3 hh0]
      · nlinarith [mul_le_mul_of_nonpos_left hcx hh0]
    · have hre : (M + h * ((s * Real.cosh x : ℝ) : ℂ)).re = M.re + h.re * (s * Real.cosh x) := by
        simp
      apply psiDom_of_re_pos
      · rw [hre]
        rcases le_total 0 (h.re * s) with hh0 | hh0
        · nlinarith [mul_le_mul_of_nonneg_left hc3 hh0]
        · nlinarith [mul_le_mul_of_nonpos_left hcx hh0]
      · rw [hre]
        rcases le_total 0 (h.re * s) with hh0 | hh0
        · nlinarith [mul_le_mul_of_nonneg_left hcx hh0]
        · nlinarith [mul_le_mul_of_nonpos_left hc3 hh0]
      · rw [hre]
        rcases le_total 0 (h.re * s) with hh0 | hh0
        · nlinarith [mul_le_mul_of_nonneg_left hc3 hh0]
        · nlinarith [mul_le_mul_of_nonpos_left hcx hh0]
  have hE : ∀ k < N, Real.exp (-(((k + 1 : ℕ) : ℝ) * (a - ρ'))) ≤
      (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ) := by
    intro k _
    have e1 : -(((k + 1 : ℕ) : ℝ) * (a - ρ')) = ((k + 1 : ℕ) : ℝ) * (Real.log ρq + ρ') := by
      rw [ha]; ring
    rw [e1, Real.exp_nat_mul, Real.exp_add, Real.exp_log hρR]
    push_cast
    refine pow_le_pow_left₀ (mul_nonneg hρR.le (Real.exp_pos _).le) ?_ _
    have := Real.exp_bound_div_one_sub_of_interval hρ'R hρ'1R
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left this hρR.le
  have key := cellG_sound_nn 3 2 2 6 (2 * Real.pi) (((-2 : ℚ)) : ℝ) (((-2 : ℚ)) : ℝ) (by norm_num)
    (by norm_num) hh hpos hs1 (whi := whi) hwhi hdom hV hh₂ hpos₂ hX
    (E := fun k => (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ)) hE (rq := ρ') (ℓ := ℓ) rfl
    (by simpa using hTenc) ?_ hok
  · intro x hx hx0
    have := key x hx hx0
    simpa using this
  · have hs1' : ∑ k ∈ Finset.range N, |c (k + 1)| * ((k + 1 : ℕ) : ℝ) ^ 4 *
        (((ρq / (1 - ρ')) ^ (k + 1) : ℚ) : ℝ) = (ownSumGQ cq N (ρq / (1 - ρ')) : ℝ) := by
      unfold ownSumGQ
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hcq k (Finset.mem_range.1 hk)]
    rw [hs1']
    have := (Rat.cast_le (K := ℝ)).2 hTR
    push_cast at this ⊢
    simp only [abs_neg, abs_two, Rat.cast_neg, Rat.cast_ofNat]
    linarith




/-! ### G cells -/

theorem toC_lin2 (m h : GQ) (c : ℚ) :
    GQ.toC m + GQ.toC h * (((c : ℚ) : ℝ) : ℂ) = GQ.toC ⟨m.re + h.re * c, m.im + h.im * c⟩ := by
  apply Complex.ext <;> simp [GQ.toC]

theorem chQ_nonneg {ρ : ℚ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (i : ℕ) : 0 ≤ chQ ρ i := by
  unfold chQ
  split_ifs
  · have : 0 < ρ⁻¹ := inv_pos.2 hρ
    linarith
  · have h2 : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).2 hρ1
    linarith

structure GCell where
  lo : ℚ
  hi : ℚ
  sg : ℚ
  ρq : ℚ
  ρ' : ℚ
  φq : CQ
  R : ℚ
  δ : ℚ
  hlo : ℚ
  dq : ℚ
  T2q : ℚ
  TV : ℚ
  TR : ℚ
  q1 : ℚ
  p1 : ℚ
  q2 : ℚ
  p2 : ℚ
  q3 : ℚ
  p3 : ℚ

def thG (d : GCell) : ℚ := (d.lo + d.hi) / 2
def rhoG (d : GCell) : ℚ := (d.hi - d.lo) / 2
def sqG (d : GCell) : GQ :=
  ⟨MG.re + HG.re * (d.sg * chQ d.ρq 0), MG.im + HG.im * (d.sg * chQ d.ρq 0)⟩
def YG (d : GCell) : ℕ → GQ := fun i => GQ.sc (d.sg * chQ d.ρq i) HG
def ρhG (d : GCell) : ℚ := d.ρq * (1 - d.ρ')
def lqG (d : GCell) : ℚ × ℚ := (logQ 8 d.ρq).getD (0, 0)
def voG (d : GCell) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) := (vEncOut 8 8 kapE (sqG d)).getD vo3
def segG (d : GCell) : SegQ := { hq := HC, φq := d.φq, cq := cqL, N := 8 }
def l2G (d : GCell) : ℚ × ℚ := (logQ 8 (d.φq.nsq / 4)).getD (0, 0)
def tq2G (d : GCell) : ℕ → ℚ := (segG d).Tq l1C.1 (l2G d).1 (fun i => toCQ (YG d i))
def te2G (d : GCell) : ℕ → ℚ :=
  (segG d).Te l1C.2 (l2G d).2 d.dq d.δ (fun i => bhq * chQ d.ρq i)
def bG (d : GCell) : ℚ := bhq * chQ (d.ρq * (1 - d.ρ')) 1 * d.ρ'
def LG (d : GCell) (n q p : ℚ) : ℚ := (vPole 8 n q p (bG d)).getD 0
def wcG (d : GCell) : Bool :=
  wedgeCellOk
    (wTq (vTW (voG d).1 (voG d).2.1 (voG d).2.2 (sqG d) (YG d)).1
      (fun j => ownGTq K0E.1 (3 / 2) d.sg (fun k => cqL k) 8 j d.ρq (lqG d).1) (tq2G d))
    (wTe (vTW (voG d).1 (voG d).2.1 (voG d).2.2 (sqG d) (YG d)).2
      (fun j => if j = 0 then K0E.2 + |(3 / 2 : ℚ)| * (lqG d).2 else 0) (te2G d)) d.TR d.ρ' ellq

@[reducible] def okGProp (d : GCell) : Prop :=
  (d.sg = 1 ∨ d.sg = -1) ∧ 0 < d.ρq ∧ d.ρq ≤ 1 ∧ 0 ≤ d.ρ' ∧ d.ρ' < 1 ∧ 0 ≤ d.lo ∧ d.lo ≤ d.hi ∧
  (logQ 8 d.ρq).isSome = true ∧ rhoG d + epsG (thG d) (lqG d).1 (lqG d).2 ≤ d.ρ' ∧
  ((0 < MG.im + HG.im * d.sg * 1 ∧ 0 < MG.im + HG.im * d.sg * chQ (ρhG d) 0) ∨
    (0 < MG.re + HG.re * d.sg * 1 ∧ MG.re + HG.re * d.sg * 1 < 2 ∧
      0 < MG.re + HG.re * d.sg * chQ (ρhG d) 0 ∧ MG.re + HG.re * d.sg * chQ (ρhG d) 0 < 2)) ∧
  (vEncOut 8 8 kapE (sqG d)).isSome = true ∧
  1 < d.R ∧ d.R ^ 2 ≤ d.φq.nsq ∧ 0 ≤ d.δ ∧
  ((toCQ (sqG d)).sub (MC.add (HC.mul (segG d).ζ))).nsq ≤ d.δ ^ 2 ∧
  0 ≤ d.hlo ∧ d.hlo ^ 2 ≤ HC.nsq ∧ 0 < d.dq ∧ d.dq ≤ d.hlo * ((d.R + d.R⁻¹) / 2 - 1) - d.δ ∧
  (logQ 8 (d.φq.nsq / 4)).isSome = true ∧
  (toCQ (YG d 1)).nsq ≤ (bhq * chQ d.ρq 1) ^ 2 ∧ (toCQ (YG d 2)).nsq ≤ (bhq * chQ d.ρq 2) ^ 2 ∧
  (toCQ (YG d 3)).nsq ≤ (bhq * chQ d.ρq 3) ^ 2 ∧ (toCQ (YG d 4)).nsq ≤ (bhq * chQ d.ρq 4) ^ 2 ∧
  0 < d.dq - bG d ∧
  fdbBound (fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (d.dq - bG d) ^ k)
    (fun i => bhq * chQ (d.ρq * (1 - d.ρ')) i) ≤ d.T2q ∧
  (vPole 8 (nsq (sqG d)) d.q1 d.p1 (bG d)).isSome = true ∧
  (vPole 8 (nsq (GQ.sub ⟨2, 0⟩ (sqG d))) d.q2 d.p2 (bG d)).isSome = true ∧
  (vPole 8 (nsq (GQ.add (sqG d) ⟨6, 0⟩)) d.q3 d.p3 (bG d)).isSome = true ∧
  fdbBound (psiDmQ (d.q1 - bG d) (d.q2 - bG d) (d.q3 - bG d)
    (LG d (nsq (sqG d)) d.q1 d.p1) (LG d (nsq (GQ.sub ⟨2, 0⟩ (sqG d))) d.q2 d.p2)
    (LG d (nsq (GQ.add (sqG d) ⟨6, 0⟩)) d.q3 d.p3)) (fun i => bhq * chQ (d.ρq * (1 - d.ρ')) i) ≤ d.TV ∧
  d.TV + 2 * ownSumGQ cqL 8 (d.ρq / (1 - d.ρ')) + 2 * d.T2q ≤ d.TR ∧
  wcG d = true

def okG (d : GCell) : Bool := decide (okGProp d)

theorem okG_sound {d : GCell} (hd : okG d = true) :
    ∀ w ∈ Icc ((thG d : ℝ) - rhoG d) ((thG d : ℝ) + rhoG d),
      Wan DecayGlue.laiC 8 (DecayInstance.laiM +
        DecayInstance.laiH * (((d.sg : ℝ) * Real.cosh w : ℝ) : ℂ)) ≤ DecayInstance.laiEll := by
  have hp : okGProp d := of_decide_eq_true hd
  obtain ⟨hsg, hρq, hρq1, hρ', hρ'1, hlo, hlohi, hlqS, heps, hD, hvS, hR, hRφ, hδ, hs, hlo0, hlo2, hdq0,
    hdq, hl2S, hY1, hY2, hY3, hY4, hdb, hT, hp1S, hp2S, hp3S, hTV, hTR, hok⟩ := hp
  have hlE : logQ 8 d.ρq = some (lqG d) := opt_some (0, 0) hlqS
  have hcont := contain_G (θ := thG d) (ρ := rhoG d) hlE heps
  have hvE : vEncOut 8 8 kapE (sqG d) = some (voG d) := opt_some vo3 hvS
  have hl1 : logQ 8 HC.nsq = some l1C := opt_some (0, 0) K0_ok.1
  have hl2 : logQ 8 (d.φq.nsq / 4) = some (l2G d) := opt_some (0, 0) hl2S
  have hρR : (0 : ℝ) < (d.ρq : ℝ) := by exact_mod_cast hρq
  have hρ'R : (0 : ℝ) ≤ (d.ρ' : ℝ) := by exact_mod_cast hρ'
  have hρ'1R : (d.ρ' : ℝ) < 1 := by exact_mod_cast hρ'1
  have hρh : 0 < ρhG d := by unfold ρhG; exact mul_pos hρq (by linarith)
  have hρhR : (0 : ℝ) < ((ρhG d : ℚ) : ℝ) := by exact_mod_cast hρh
  have hρh1 : ρhG d ≤ 1 := by unfold ρhG; nlinarith
  have hch0 : ∀ i, 0 ≤ chQ d.ρq i := chQ_nonneg hρq hρq1
  have hchh0 : ∀ i, 0 ≤ chQ (ρhG d) i := chQ_nonneg hρh hρh1
  -- the arm at a' = -log ρq
  have harm : ∀ i, armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ) i (-Real.log (d.ρq : ℝ)) =
      (if i = 0 then DecayInstance.laiM else 0) +
        DecayInstance.laiH * (((d.sg * chQ d.ρq i : ℚ) : ℝ) : ℂ) := by
    intro i
    have hc := chQ_spec hρq i
    rw [armG_neg_log _ _ _ hρR i]
    simp only [Rat.cast_mul, Complex.ofReal_mul]
    rw [← hc]
  have hz : armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ) 0 (-Real.log (d.ρq : ℝ)) =
      CQ.toC (toCQ (sqG d)) := by
    rw [harm 0, if_pos rfl, ← toC_MG, ← toC_HG, toC_lin2, toC_toCQ]
    rfl
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ) i
      (-Real.log (d.ρq : ℝ)) = CQ.toC (toCQ (YG d i)) := by
    intro i hi _
    rw [harm i, if_neg (by omega), zero_add, toC_toCQ, YG, GQ.toC_sc, toC_HG, mul_comm]
    simp
  have hne : HC.nsq ≠ 0 := by decide +kernel
  have hseg : ∀ j ≤ 4, |potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH)
      DecayGlue.laiC 8 (armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ)) j
        (-Real.log (d.ρq : ℝ)) - ((tq2G d j : ℚ) : ℝ)| ≤ ((te2G d j : ℚ) : ℝ) :=
    segTower_encQ (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (segG d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqG d))
      toC_MC toC_HC hne (γ := armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ))
      (x := -Real.log (d.ρq : ℝ)) (fun i => toCQ (YG d i)) (fun i => bhq * chQ d.ρq i) hz hYi
      (fun i hi1 hi4 => ⟨mul_nonneg (by unfold bhq; norm_num) (hch0 i), by
        interval_cases i <;> assumption⟩)
      d.R d.δ d.dq d.hlo l1C.1 l1C.2 (l2G d).1 (l2G d).2 8 8 hR hRφ hδ hs hlo0 hlo2 hdq0 hdq hl1 hl2
  -- Ym on the cell
  have hcoshw : ∀ i, YmG DecayInstance.laiH (-Real.log (((ρhG d : ℚ)) : ℝ)) i =
      ‖DecayInstance.laiH‖ * ((chQ (ρhG d) i : ℚ) : ℝ) := by
    intro i
    unfold YmG
    rw [← chQ_spec hρh]
    by_cases hi : i % 2 = 0
    · simp [hi, cosh_neg_log hρhR]
    · simp [hi, sinh_neg_log hρhR]
  have hchh0R : ∀ i, (0 : ℝ) ≤ ((chQ (ρhG d) i : ℚ) : ℝ) := fun i => by exact_mod_cast hchh0 i
  have hb : YmG DecayInstance.laiH (-Real.log (((ρhG d : ℚ)) : ℝ)) 1 * (d.ρ' : ℝ) ≤ ((bG d : ℚ) : ℝ) := by
    rw [hcoshw]; unfold bG; push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right norm_laiH_le (hchh0R 1)) hρ'R
  have hX : SegCell (armG DecayInstance.laiM DecayInstance.laiH (d.sg : ℝ) 0 (-Real.log (d.ρq : ℝ)))
      (YmG DecayInstance.laiH (-Real.log (((d.ρq * (1 - d.ρ') : ℚ)) : ℝ))) (d.ρ' : ℝ)
      (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH) (DecayGlue.laiC 0)
      (d.T2q : ℝ) := by
    rw [hz]
    exact segCell_of_enc (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (segG d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqG d))
      toC_MC toC_HC hne d.R d.δ d.dq d.hlo hR hRφ hδ hs hlo0 hlo2 hdq
      (Ym := YmG DecayInstance.laiH (-Real.log (((d.ρq * (1 - d.ρ') : ℚ)) : ℝ))) (ρ := (d.ρ' : ℝ))
      hρ'R (b := bG d) hb (YmQ := fun i => bhq * chQ (d.ρq * (1 - d.ρ')) i)
      (fun i _ _ => ⟨by
          rw [show d.ρq * (1 - d.ρ') = ρhG d from rfl, hcoshw]
          exact mul_nonneg (norm_nonneg _) (hchh0R i), by
          rw [show d.ρq * (1 - d.ρ') = ρhG d from rfl, hcoshw]; push_cast
          exact mul_le_mul_of_nonneg_right norm_laiH_le (hchh0R i)⟩) hdb hT
  have hDr : (0 < DecayInstance.laiM.im + DecayInstance.laiH.im * (d.sg : ℝ) * 1 ∧
        0 < DecayInstance.laiM.im + DecayInstance.laiH.im * (d.sg : ℝ) *
          ((chQ (d.ρq * (1 - d.ρ')) 0 : ℚ) : ℝ)) ∨
      (0 < DecayInstance.laiM.re + DecayInstance.laiH.re * (d.sg : ℝ) * 1 ∧
        DecayInstance.laiM.re + DecayInstance.laiH.re * (d.sg : ℝ) * 1 < 2 ∧
        0 < DecayInstance.laiM.re + DecayInstance.laiH.re * (d.sg : ℝ) *
          ((chQ (d.ρq * (1 - d.ρ')) 0 : ℚ) : ℝ) ∧
        DecayInstance.laiM.re + DecayInstance.laiH.re * (d.sg : ℝ) *
          ((chQ (d.ρq * (1 - d.ρ')) 0 : ℚ) : ℝ) < 2) := by
    rcases hD with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
    · left
      refine ⟨?_, ?_⟩
      · have := (Rat.cast_pos (K := ℝ)).2 h1
        push_cast [MG, HG] at this
        simpa using this
      · have := (Rat.cast_pos (K := ℝ)).2 h2
        push_cast [MG, HG, ρhG] at this
        simpa using this
    · right
      refine ⟨?_, ?_, ?_, ?_⟩
      · have := (Rat.cast_pos (K := ℝ)).2 h1
        push_cast [MG, HG] at this
        simpa using this
      · have := (Rat.cast_lt (K := ℝ)).2 h2
        push_cast [MG, HG] at this
        simpa using this
      · have := (Rat.cast_pos (K := ℝ)).2 h3
        push_cast [MG, HG, ρhG] at this
        simpa using this
      · have := (Rat.cast_lt (K := ℝ)).2 h4
        push_cast [MG, HG, ρhG] at this
        simpa using this
  have key := cellG_rat' (c := DecayGlue.laiC) (N := 8) DecayGlue.laiC_hpos DecayInstance.laiH_ne
    toC_MG toC_HG (sg := d.sg) hsg hρq hρq1 hρ' hρ'1 hDr
    (nL := 8) (nA := 8) kapE_enc (t0 := (voG d).1) (d1r := (voG d).2.1) (d1i := (voG d).2.2) hvE
    (K0q := K0E.1) (eK := K0E.2) (c0q := 3 / 2) (lq := (lqG d).1) (el := (lqG d).2) K0_enc
    (by rw [DecayGlue.laiC_zero]; norm_num) (logQ_spec hlE).2 (cq := cqL) (fun k _ => cqL_real (k + 1))
    laiH_cne DecayGlue.laiC_hpos (tq2 := tq2G d) (te2 := te2G d) hseg hX (bh := bhq) norm_laiH_le
    (opt_some 0 hp1S) (opt_some 0 hp2S) (opt_some 0 hp3S) hTV (ℓ := ellq) hTR hok
  intro w hw
  by_cases hw0 : 0 ≤ w
  · have := key w (hcont w hw) hw0
    rw [ell_eq] at this
    exact this
  · push Not at hw0
    have hθ : (0 : ℝ) ≤ (thG d : ℝ) := by
      have : 0 ≤ thG d := by unfold thG; linarith
      exact_mod_cast this
    have hx : -w ∈ Icc ((thG d : ℝ) - rhoG d) ((thG d : ℝ) + rhoG d) :=
      ⟨by linarith [hw.1], by linarith [hw.1]⟩
    have := key (-w) (hcont (-w) hx) (by linarith)
    rw [Real.cosh_neg, ell_eq] at this
    exact this

/-! ### R cells -/

def PG : GQ := ⟨21 / 10, 11 / 5⟩
def HP : CQ := ⟨93 / 400, 1023 / 1000⟩
def MP : CQ := ⟨737 / 400, 1067 / 1000⟩

theorem toC_PG : GQ.toC PG = DecayInstance.laiP := by
  apply Complex.ext <;> simp [GQ.toC, PG, DecayInstance.laiP]
theorem toC_MP : CQ.toC MP = DecayInstance.laiM := by
  apply Complex.ext <;> simp [CQ.toC, MP, DecayInstance.laiM]
theorem toC_HP : CQ.toC HP = DecayInstance.laiH := by
  apply Complex.ext <;> simp [CQ.toC, HP, DecayInstance.laiH]

theorem HP_nsq : HP.nsq = HC.nsq := by
  unfold CQ.nsq HP HC; norm_num

structure RCell where
  lo : ℚ
  hi : ℚ
  φ1 : CQ
  R1 : ℚ
  δ1 : ℚ
  hlo1 : ℚ
  dq1 : ℚ
  T1q : ℚ
  φ2 : CQ
  R2 : ℚ
  δ2 : ℚ
  hlo2 : ℚ
  dq2 : ℚ
  T2q : ℚ
  TV : ℚ
  TR : ℚ
  q1 : ℚ
  p1 : ℚ
  q2 : ℚ
  p2 : ℚ
  q3 : ℚ
  p3 : ℚ

def aR (d : RCell) : ℚ := (d.lo + d.hi) / 2
def rhoR (d : RCell) : ℚ := (d.hi - d.lo) / 2
def sqR (d : RCell) : GQ := ⟨PG.re, PG.im + aR d⟩
def YR : ℕ → GQ := fun i => if i = 1 then ⟨0, 1⟩ else ⟨0, 0⟩
def YmR : ℕ → ℚ := fun i => if i = 1 then 1 else 0
def voR (d : RCell) : (ℚ × ℚ) × (ℚ × ℚ) × (ℚ × ℚ) := (vEncOut 8 8 kapE (sqR d)).getD vo3
def seg1R (d : RCell) : SegQ := { hq := HP, φq := d.φ1, cq := cqL, N := 8 }
def seg2R (d : RCell) : SegQ := { hq := HC, φq := d.φ2, cq := cqL, N := 8 }
def l21R (d : RCell) : ℚ × ℚ := (logQ 8 (d.φ1.nsq / 4)).getD (0, 0)
def l22R (d : RCell) : ℚ × ℚ := (logQ 8 (d.φ2.nsq / 4)).getD (0, 0)
def tq1R (d : RCell) : ℕ → ℚ := (seg1R d).Tq l1C.1 (l21R d).1 (fun i => toCQ (YR i))
def te1R (d : RCell) : ℕ → ℚ := (seg1R d).Te l1C.2 (l21R d).2 d.dq1 d.δ1 YmR
def tq2R (d : RCell) : ℕ → ℚ := (seg2R d).Tq l1C.1 (l22R d).1 (fun i => toCQ (YR i))
def te2R (d : RCell) : ℕ → ℚ := (seg2R d).Te l1C.2 (l22R d).2 d.dq2 d.δ2 YmR
def LR (d : RCell) (n q p : ℚ) : ℚ := (vPole 8 n q p (rhoR d)).getD 0
def wcR (d : RCell) : Bool :=
  wedgeCellOk
    (wTq (vTW (voR d).1 (voR d).2.1 (voR d).2.2 (sqR d) YR).1 (tq1R d) (tq2R d))
    (wTe (vTW (voR d).1 (voR d).2.1 (voR d).2.2 (sqR d) YR).2 (te1R d) (te2R d)) d.TR (rhoR d) ellq

@[reducible] def okRProp (d : RCell) : Prop :=
  0 ≤ rhoR d ∧ 0 < PG.im + (aR d - rhoR d) ∧
  (vEncOut 8 8 kapE (sqR d)).isSome = true ∧
  1 < d.R1 ∧ d.R1 ^ 2 ≤ d.φ1.nsq ∧ 0 ≤ d.δ1 ∧
  ((toCQ (sqR d)).sub (MP.add (HP.mul (seg1R d).ζ))).nsq ≤ d.δ1 ^ 2 ∧
  0 ≤ d.hlo1 ∧ d.hlo1 ^ 2 ≤ HP.nsq ∧ 0 < d.dq1 ∧ d.dq1 ≤ d.hlo1 * ((d.R1 + d.R1⁻¹) / 2 - 1) - d.δ1 ∧
  (logQ 8 (d.φ1.nsq / 4)).isSome = true ∧ 0 < d.dq1 - rhoR d ∧
  fdbBound (fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (d.dq1 - rhoR d) ^ k) YmR ≤ d.T1q ∧
  1 < d.R2 ∧ d.R2 ^ 2 ≤ d.φ2.nsq ∧ 0 ≤ d.δ2 ∧
  ((toCQ (sqR d)).sub (MC.add (HC.mul (seg2R d).ζ))).nsq ≤ d.δ2 ^ 2 ∧
  0 ≤ d.hlo2 ∧ d.hlo2 ^ 2 ≤ HC.nsq ∧ 0 < d.dq2 ∧ d.dq2 ≤ d.hlo2 * ((d.R2 + d.R2⁻¹) / 2 - 1) - d.δ2 ∧
  (logQ 8 (d.φ2.nsq / 4)).isSome = true ∧ 0 < d.dq2 - rhoR d ∧
  fdbBound (fun k => (((k - 1).factorial : ℕ) : ℚ) * cqL 0 / (d.dq2 - rhoR d) ^ k) YmR ≤ d.T2q ∧
  (vPole 8 (nsq (sqR d)) d.q1 d.p1 (rhoR d)).isSome = true ∧
  (vPole 8 (nsq (GQ.sub ⟨2, 0⟩ (sqR d))) d.q2 d.p2 (rhoR d)).isSome = true ∧
  (vPole 8 (nsq (GQ.add (sqR d) ⟨6, 0⟩)) d.q3 d.p3 (rhoR d)).isSome = true ∧
  fdbBound (psiDmQ (d.q1 - rhoR d) (d.q2 - rhoR d) (d.q3 - rhoR d)
    (LR d (nsq (sqR d)) d.q1 d.p1) (LR d (nsq (GQ.sub ⟨2, 0⟩ (sqR d))) d.q2 d.p2)
    (LR d (nsq (GQ.add (sqR d) ⟨6, 0⟩)) d.q3 d.p3)) YmR ≤ d.TV ∧
  d.TV + 2 * d.T1q + 2 * d.T2q ≤ d.TR ∧
  wcR d = true

def okR (d : RCell) : Bool := decide (okRProp d)

theorem okR_sound {d : RCell} (hd : okR d = true) :
    ∀ y ∈ Icc ((aR d : ℝ) - rhoR d) ((aR d : ℝ) + rhoR d),
      Wan DecayGlue.laiC 8 (DecayInstance.laiP + Complex.I * (y : ℂ)) ≤ DecayInstance.laiEll := by
  have hp : okRProp d := of_decide_eq_true hd
  obtain ⟨hρ, hIm, hvS, hR1, hRφ1, hδ1, hs1, hlo01, hlo21, hdq01, hdq1, hl21S, hdb1, hT1,
    hR2, hRφ2, hδ2, hs2, hlo02, hlo22, hdq02, hdq2, hl22S, hdb2, hT2, hp1S, hp2S, hp3S, hTV, hTR, hok⟩ := hp
  have hvE : vEncOut 8 8 kapE (sqR d) = some (voR d) := opt_some vo3 hvS
  have hl1C : logQ 8 HC.nsq = some l1C := opt_some (0, 0) K0_ok.1
  have hl1P : logQ 8 HP.nsq = some l1C := by rw [HP_nsq]; exact hl1C
  have hl21 : logQ 8 (d.φ1.nsq / 4) = some (l21R d) := opt_some (0, 0) hl21S
  have hl22 : logQ 8 (d.φ2.nsq / 4) = some (l22R d) := opt_some (0, 0) hl22S
  have hnP : HP.nsq ≠ 0 := by decide +kernel
  have hnC : HC.nsq ≠ 0 := by decide +kernel
  have hρR : (0 : ℝ) ≤ (rhoR d : ℝ) := by exact_mod_cast hρ
  have hz : lineC DecayInstance.laiP Complex.I 0 (aR d : ℝ) = CQ.toC (toCQ (sqR d)) := by
    rw [← toC_PG]
    apply Complex.ext <;> simp [lineC, GQ.toC, CQ.toC, toCQ, sqR]
  have hYi : ∀ i, 1 ≤ i → i ≤ 4 → lineC DecayInstance.laiP Complex.I i (aR d : ℝ) =
      CQ.toC (toCQ (YR i)) := by
    intro i hi _
    by_cases h1 : i = 1
    · subst h1; apply Complex.ext <;> simp [lineC, YR, GQ.toC, CQ.toC, toCQ]
    · have : i ≠ 0 := by omega
      apply Complex.ext <;> simp [lineC, YR, GQ.toC, CQ.toC, toCQ, h1, this]
  have hYY : ∀ i, 1 ≤ i → i ≤ 4 → 0 ≤ YmR i ∧ (toCQ (YR i)).nsq ≤ YmR i ^ 2 := by
    intro i _ _
    by_cases h1 : i = 1
    · subst h1; unfold YmR YR toCQ CQ.nsq; norm_num
    · unfold YmR YR toCQ CQ.nsq; simp [h1]
  have hseg1 : ∀ j ≤ 4, |potT DecayInstance.laiM DecayInstance.laiH DecayGlue.laiC 8
      (lineC DecayInstance.laiP Complex.I) j (aR d : ℝ) - ((tq1R d j : ℚ) : ℝ)| ≤ ((te1R d j : ℚ) : ℝ) :=
    segTower_encQ (M := DecayInstance.laiM) (h := DecayInstance.laiH) (c := DecayGlue.laiC) (seg1R d)
      DecayGlue.laiC_hpos (fun k _ => cqL_real k) MP (toCQ (sqR d)) toC_MP toC_HP hnP
      (γ := lineC DecayInstance.laiP Complex.I) (x := (aR d : ℝ)) (fun i => toCQ (YR i)) YmR hz hYi hYY
      d.R1 d.δ1 d.dq1 d.hlo1 l1C.1 l1C.2 (l21R d).1 (l21R d).2 8 8 hR1 hRφ1 hδ1 hs1 hlo01 hlo21 hdq01
      hdq1 hl1P hl21
  have hseg2 : ∀ j ≤ 4, |potT (starRingEnd ℂ DecayInstance.laiM) (starRingEnd ℂ DecayInstance.laiH)
      DecayGlue.laiC 8 (lineC DecayInstance.laiP Complex.I) j (aR d : ℝ) - ((tq2R d j : ℚ) : ℝ)| ≤
        ((te2R d j : ℚ) : ℝ) :=
    segTower_encQ (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (seg2R d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqR d))
      toC_MC toC_HC hnC (γ := lineC DecayInstance.laiP Complex.I) (x := (aR d : ℝ))
      (fun i => toCQ (YR i)) YmR hz hYi hYY
      d.R2 d.δ2 d.dq2 d.hlo2 l1C.1 l1C.2 (l22R d).1 (l22R d).2 8 8 hR2 hRφ2 hδ2 hs2 hlo02 hlo22 hdq02
      hdq2 hl1C hl22
  have hYm1 : ∀ i, 1 ≤ i → i ≤ 5 → 0 ≤ (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) i ∧
      (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) i ≤ ((YmR i : ℚ) : ℝ) := by
    intro i _ _
    by_cases h1 : i = 1 <;> simp [YmR, h1]
  have hb1 : (fun i : ℕ => if i = 1 then (1 : ℝ) else 0) 1 * (rhoR d : ℝ) ≤ ((rhoR d : ℚ) : ℝ) := by
    simp
  have hX1 : SegCell (lineC DecayInstance.laiP Complex.I 0 (aR d : ℝ))
      (fun i => if i = 1 then 1 else 0) (rhoR d : ℝ) DecayInstance.laiM DecayInstance.laiH
      (DecayGlue.laiC 0) (d.T1q : ℝ) := by
    rw [hz]
    exact segCell_of_enc (M := DecayInstance.laiM) (h := DecayInstance.laiH) (c := DecayGlue.laiC)
      (seg1R d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MP (toCQ (sqR d)) toC_MP toC_HP hnP
      d.R1 d.δ1 d.dq1 d.hlo1 hR1 hRφ1 hδ1 hs1 hlo01 hlo21 hdq1
      (Ym := fun i => if i = 1 then 1 else 0) (ρ := (rhoR d : ℝ)) hρR (b := rhoR d) hb1
      (YmQ := YmR) hYm1 hdb1 hT1
  have hX2 : SegCell (lineC DecayInstance.laiP Complex.I 0 (aR d : ℝ))
      (fun i => if i = 1 then 1 else 0) (rhoR d : ℝ) (starRingEnd ℂ DecayInstance.laiM)
      (starRingEnd ℂ DecayInstance.laiH) (DecayGlue.laiC 0) (d.T2q : ℝ) := by
    rw [hz]
    exact segCell_of_enc (M := starRingEnd ℂ DecayInstance.laiM) (h := starRingEnd ℂ DecayInstance.laiH)
      (c := DecayGlue.laiC) (seg2R d) DecayGlue.laiC_hpos (fun k _ => cqL_real k) MC (toCQ (sqR d))
      toC_MC toC_HC hnC d.R2 d.δ2 d.dq2 d.hlo2 hR2 hRφ2 hδ2 hs2 hlo02 hlo22 hdq2
      (Ym := fun i => if i = 1 then 1 else 0) (ρ := (rhoR d : ℝ)) hρR (b := rhoR d) hb1
      (YmQ := YmR) hYm1 hdb2 hT2
  have hImR : 0 < DecayInstance.laiP.im + (((aR d : ℚ) : ℝ) - (rhoR d : ℚ)) := by
    have := (Rat.cast_pos (K := ℝ)).2 hIm
    simp only [PG] at this
    push_cast at this
    simpa [DecayInstance.laiP] using this
  have key := cellR_rat (pq := PG) toC_PG (a := aR d) (ρ := rhoR d) hρ hImR (nL := 8) (nA := 8)
    kapE_enc (t0 := (voR d).1) (d1r := (voR d).2.1) (d1i := (voR d).2.2) hvE
    DecayInstance.laiH_ne DecayGlue.laiC_hpos (tq1 := tq1R d) (te1 := te1R d) hseg1 (T1q := d.T1q) hX1
    laiH_cne DecayGlue.laiC_hpos (tq2 := tq2R d) (te2 := te2R d) hseg2 (T2q := d.T2q) hX2
    (opt_some 0 hp1S) (opt_some 0 hp2S) (opt_some 0 hp3S) hTV (ℓ := ellq) hTR hok
  intro y hy
  have := key y hy
  rw [ell_eq] at this
  exact this

/-! ### Assembly: the four chains give `LaiCover` -/

def chA (L : List ACell) : List (ℚ × ℚ) := L.map fun d => (thA d, rhoA d)
def chG (L : List GCell) : List (ℚ × ℚ) := L.map fun d => (thG d, rhoG d)
def chR (L : List RCell) : List (ℚ × ℚ) := L.map fun d => (aR d, rhoR d)

/-- the endpoint and chain conditions of `laiCover_of_cells` (`wA = 146127/500000`, `wB = 459681/10^6`) -/
def coverOK (a0 : ACell) (aT : List ACell) (g0 : GCell) (gT : List GCell) (h0 : GCell)
    (hT : List GCell) (r0 : RCell) (rT : List RCell) : Bool :=
  decide (
    chainOK (31416 / 10000) ((thA a0, rhoA a0) :: aT.map fun d => (thA d, rhoA d)) = true ∧
    (0 ≤ thA a0 ∧ thA a0 * (31416 / 10000) ≤ rhoA a0) ∧
    ((((thA a0, rhoA a0) :: aT.map fun d => (thA d, rhoA d)).getLast (by simp)).1 ≤ 1 ∧
      (1 - (((thA a0, rhoA a0) :: aT.map fun d => (thA d, rhoA d)).getLast (by simp)).1) * (31416 / 10000) ≤
        (((thA a0, rhoA a0) :: aT.map fun d => (thA d, rhoA d)).getLast (by simp)).2) ∧
    chainOK 1 ((thG g0, rhoG g0) :: gT.map fun d => (thG d, rhoG d)) = true ∧ thG g0 - rhoG g0 ≤ 0 ∧
    (146127 / 500000 : ℚ) ≤ (((thG g0, rhoG g0) :: gT.map fun d => (thG d, rhoG d)).getLast (by simp)).1 +
      (((thG g0, rhoG g0) :: gT.map fun d => (thG d, rhoG d)).getLast (by simp)).2 ∧
    chainOK 1 ((thG h0, rhoG h0) :: hT.map fun d => (thG d, rhoG d)) = true ∧ thG h0 - rhoG h0 ≤ 0 ∧
    (459681 / 1000000 : ℚ) ≤ (((thG h0, rhoG h0) :: hT.map fun d => (thG d, rhoG d)).getLast (by simp)).1 +
      (((thG h0, rhoG h0) :: hT.map fun d => (thG d, rhoG d)).getLast (by simp)).2 ∧
    chainOK 1 ((aR r0, rhoR r0) :: rT.map fun d => (aR d, rhoR d)) = true ∧ aR r0 - rhoR r0 ≤ 0 ∧
    (11 / 10 : ℚ) ≤ (((aR r0, rhoR r0) :: rT.map fun d => (aR d, rhoR d)).getLast (by simp)).1 +
      (((aR r0, rhoR r0) :: rT.map fun d => (aR d, rhoR d)).getLast (by simp)).2)

theorem real_of_rat_le {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ b := by exact_mod_cast h

theorem laiCover_of_data (a0 : ACell) (aT : List ACell) (g0 : GCell) (gT : List GCell) (h0 : GCell)
    (hT : List GCell) (r0 : RCell) (rT : List RCell)
    (hc : coverOK a0 aT g0 gT h0 hT r0 rT = true)
    (hA : ∀ d ∈ a0 :: aT, okA d = true)
    (hG : ∀ d ∈ g0 :: gT, okG d = true ∧ d.sg = -1)
    (hH : ∀ d ∈ h0 :: hT, okG d = true ∧ d.sg = 1)
    (hR : ∀ d ∈ r0 :: rT, okR d = true) :
    DecayInstance.LaiCover DecayGlue.laiC 8 DecayInstance.laiEll (146127 / 500000) (459681 / 1000000) := by
  have hc' := of_decide_eq_true hc
  obtain ⟨hcA, hA0, hA1, hcG, hG0, hG1, hcH, hH0, hH1, hcR, hR0, hR1⟩ := hc'
  refine laiCover_of_cells DecayGlue.laiC 8 (146127 / 500000) (459681 / 1000000) (by norm_num)
    (by norm_num) DecayGlue.cosh_wA DecayGlue.cosh_wB
    (thA a0, rhoA a0) (aT.map fun d => (thA d, rhoA d)) hcA hA0 hA1
    (thG g0, rhoG g0) (gT.map fun d => (thG d, rhoG d)) hcG (by exact_mod_cast hG0)
    (by have h := real_of_rat_le hG1; push_cast at h; linarith)
    (thG h0, rhoG h0) (hT.map fun d => (thG d, rhoG d)) hcH (by exact_mod_cast hH0)
    (by have h := real_of_rat_le hH1; push_cast at h; linarith)
    (aR r0, rhoR r0) (rT.map fun d => (aR d, rhoR d)) hcR (by exact_mod_cast hR0)
    (by have h := real_of_rat_le hR1; push_cast at h; linarith)
    (fun q => ∃ d ∈ a0 :: aT, okA d = true ∧ (thA d, rhoA d) = q)
    (fun q => ∃ d ∈ g0 :: gT, okG d = true ∧ d.sg = -1 ∧ (thG d, rhoG d) = q)
    (fun q => ∃ d ∈ h0 :: hT, okG d = true ∧ d.sg = 1 ∧ (thG d, rhoG d) = q)
    (fun q => ∃ d ∈ r0 :: rT, okR d = true ∧ (aR d, rhoR d) = q)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro q ⟨d, _, hd, rfl⟩ x hx
    exact okA_sound hd x ⟨by simpa [rhoA, thA] using hx.1, by simpa [rhoA, thA] using hx.2⟩
  · rintro q ⟨d, _, hd, hsg, rfl⟩ w hw
    have := okG_sound hd w hw
    rw [hsg] at this
    simpa using this
  · rintro q ⟨d, _, hd, hsg, rfl⟩ w hw
    have := okG_sound hd w hw
    rw [hsg] at this
    simpa using this
  · rintro q ⟨d, _, hd, rfl⟩ y hy
    exact okR_sound hd y hy
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (show q ∈ (a0 :: aT).map (fun d => (thA d, rhoA d)) from hq)
    exact ⟨d, hd, hA d hd, rfl⟩
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (show q ∈ (g0 :: gT).map (fun d => (thG d, rhoG d)) from hq)
    exact ⟨d, hd, (hG d hd).1, (hG d hd).2, rfl⟩
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (show q ∈ (h0 :: hT).map (fun d => (thG d, rhoG d)) from hq)
    exact ⟨d, hd, (hH d hd).1, (hH d hd).2, rfl⟩
  · intro q hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 (show q ∈ (r0 :: rT).map (fun d => (aR d, rhoR d)) from hq)
    exact ⟨d, hd, hR d hd, rfl⟩

end

end CatalanCore.Lai.DecayCheck
