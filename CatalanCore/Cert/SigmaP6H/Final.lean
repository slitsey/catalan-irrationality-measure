module

public import CatalanCore.Cert.SigmaP6H.Dom
public import CatalanCore.Cert.SigmaP6H.Energy
public import CatalanCore.Cert.SigmaHyb.JfunH
public import CatalanCore.Decay.Rect.CertGTransfer
public import CatalanCore.Decay.Rect.DecayRect
public import CatalanCore.Decay.Rect.DecayTop
public import CatalanCore.Cert.Sigma300.Glue

@[expose] public section

/-!
# The P6 hybrid decay certificate (P6DECAY)

`certP6H := certCore.toG.ofLe gH ...` : the square P6 certificate (row D, `m′ = 1.883395`) transferred
to `gH = g_sq + h`, `h ≥ 0` (`Dom`), with the new energy bound `IboundP6H` (`Energy`).
`D = 3.7251` at `α = 1/8`, density `d = 3`, `c = 6.6510`.
-/

open Real

namespace CatalanCore.Cert.SigmaP6H

open CatalanCore.Cert.SigmaP6 (certCore segBq seg_geom' segCellG)

set_option maxRecDepth 100000

theorem hseg_P6 : ∀ i, ((certCore.toG.segB i : ℚ) : ℝ) ≤ 1 := by
  intro i
  have hg := seg_geom' i i.2
  have hb : ((segCellG i).2.1 : ℝ) ≤ 0 := by exact_mod_cast hg.2
  show ((CatalanCore.Cert.SigmaP6.segBq i : ℚ) : ℝ) ≤ 1
  unfold CatalanCore.Cert.SigmaP6.segBq
  push_cast
  have : ((segCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb (by positivity)
  linarith

theorem hle_P6 : ∀ s : ℂ, ((s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(certCore.toG.r0 : ℝ) + certCore.toG.W) →
    certCore.toG.g s ≤ gH s := by
  intro s hs
  have hs' : (s.im = 0 ∧ s.re ≤ 1) ∨ s.re ≤ -(1 / 10 : ℝ) + 1 / 2 ^ 30 := by
    rcases hs with h | h
    · exact Or.inl h
    · right
      have e1 : ((certCore.toG.r0 : ℚ) : ℝ) = 1 / 10 := by
        show (((1 / 10 : ℚ)) : ℝ) = 1 / 10; push_cast; norm_num
      have e2 : ((certCore.toG.W : ℚ) : ℝ) = 1 / 2 ^ 30 := by
        show (((1 / 2 ^ 30 : ℚ)) : ℝ) = 1 / 2 ^ 30; push_cast; norm_num
      rw [e1, e2] at h; exact h
  rw [gH_decomp]
  have := h_nonneg hs'
  show CatalanLambda.Decay.gfun (1 / 2048) (1 / 1000) _ _ s ≤ _
  linarith

/-- **The P6 hybrid certificate.** -/
noncomputable def certP6H :
    CertCoreG (699 + 32) (1 / 2048 : ℝ) (1 / 1000 : ℝ) cH wtH :=
  certCore.toG.ofLe gH hle_P6 (by show (0 : ℝ) ≤ ((3 / 2 : ℚ) : ℝ); norm_num) hseg_P6
    gH_conj wtH_sum IboundP6H I_ok_P6H

theorem hg_P6 : ∀ s : ℂ, certP6H.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) *
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) cH wtH s
    - CatalanCore.Decay.Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - (1 / 1000 : ℝ)) * Real.pi * |s.im| := by
  intro s
  have e : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by push_cast; norm_num
  rw [e]
  rfl

theorem certP6H_ccert : certP6H.ccert = 66510 / 10000 := rfl

theorem D_le : (37251 / 10000 : ℚ) ≤ certP6H.Dof 3 (1 / 8) (17024457 / 10 ^ 7) := by
  unfold certP6H
  rw [CertCoreG.ofLe_Dof]
  show (37251 / 10000 : ℚ) ≤ 2 * ((1 + 1 / 8) * CatalanCore.Cert.SigmaP6.MPRAY
    + (3 : ℕ) * CatalanCore.Cert.SigmaP6.SBASE) - (1 + 1 / 8) ^ 2 * IboundP6H + 17024457 / 10 ^ 7
  simp only [CatalanCore.Cert.SigmaP6.SBASE, CatalanCore.Cert.SigmaP6.MPRAY,
    CatalanCore.Cert.SigmaP6.SVAL, IboundP6H]
  norm_num

theorem cH_norm' (k : Fin (699 + 32)) : ‖cH k‖ ≤ 4 := cH_norm k

/-- **The P6 hybrid decay** (member 1): `D = 3.7251`, `c = 6.6510` at `α = 1/8`. -/
theorem p6_hybrid_decay :
    HasDecay (CatalanCore.hybridFamUp CatalanFrames.P6.p6Frame (1 / 8 : ℚ))
      (((37251 / 10000 : ℚ)) : ℝ) (((66510 / 10000 : ℚ)) : ℝ) := by
  have := CatalanCore.decay_of_certG_rect (Fr := CatalanFrames.P6.p6Frame)
    CatalanCore.Cert.Sigma300.p6_decayOK certP6H (α := 1 / 8) (by norm_num) hg_P6
    (fun k => wtH_nonneg k) (Rc := 4) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le D_le
  rwa [certP6H_ccert] at this

/-- **The P6 first-member decay** on every relation inside `α r ≤ m ≤ α r + a` (P6GAP). -/
theorem p6_mem1_decay_slack {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + a) :
    CatalanCore.Rect.Mem1DecayA CatalanFrames.P6.p6Frame A (((37251 / 10000 : ℚ)) : ℝ)
      (((66510 / 10000 : ℚ)) : ℝ) := by
  have := CatalanCore.mem1DecayA_of_certG_rect_slack (Fr := CatalanFrames.P6.p6Frame)
    CatalanCore.Cert.Sigma300.p6_decayOK certP6H (α := 1 / 8) (by norm_num) hg_P6
    (fun k => wtH_nonneg k) (Rc := 4) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le D_le ha hA
  rwa [certP6H_ccert] at this

/-- **The P6 second-member decay** on every relation inside `α r ≤ m ≤ α r + a` (P6GAP). -/
theorem p6_mem2_decay_slack {a : ℝ} (ha : 0 ≤ a) {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + a) :
    CatalanCore.Rect.Mem2DecayA CatalanFrames.P6.p6Frame A (((37251 / 10000 : ℚ)) : ℝ)
      (((66510 / 10000 : ℚ)) : ℝ) := by
  have := CatalanCore.mem2DecayA_of_certG_rect_slack (Fr := CatalanFrames.P6.p6Frame)
    CatalanCore.Cert.Sigma300.p6_decayOK certP6H (α := 1 / 8) (by norm_num) hg_P6
    (fun k => wtH_nonneg k) (Rc := 4) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le D_le (by rw [certP6H_ccert]; norm_num) ha hA
  rwa [certP6H_ccert] at this

/-- **The P6 second-member decay** on every admissible relation inside `α r ≤ m ≤ α r + 1`
(the window-`1` case of `p6_mem2_decay_slack`). -/
theorem p6_mem2_decay_of {A : ℕ → ℕ → Prop}
    (hA : ∀ r m, A r m → ((1 / 8 : ℚ) : ℝ) * r ≤ m ∧ (m : ℝ) ≤ ((1 / 8 : ℚ) : ℝ) * r + 1) :
    CatalanCore.Rect.Mem2DecayA CatalanFrames.P6.p6Frame A (((37251 / 10000 : ℚ)) : ℝ)
      (((66510 / 10000 : ℚ)) : ℝ) :=
  p6_mem2_decay_slack zero_le_one hA

end CatalanCore.Cert.SigmaP6H
