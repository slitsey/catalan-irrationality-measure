module

public import CatalanArchive.CatalanCore.Cert.SigmaHyb.RayHyb2
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.SegHyb
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LineHyb
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.TailH
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.EnergyH
public import CatalanCore.Cert.SigmaHyb.JfunH
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.HSymm
public import CatalanCore.Decay.Rect.DecayRect
public import CatalanCore.Cert.Sigma300.Glue

@[expose] public section

/-!
# The hybrid λ decay certificate (σ300 + correction λ of mass 1/8, `K_λ = 180`, ρ = 1/1024)

`certHyb : CertCoreG 480 (1/1024) (1/1000) cH wtH` with `m′ = 22147/10000`, `g_min = -16093/10000`,
and the decay theorem for the λ frame at `α = 1/8` via `decay_of_certG_rect`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

noncomputable def certHyb : CatalanCore.Cert.CertCoreG (300 + 180) (1 / 1024 : ℝ) (1 / 1000 : ℝ) cH wtH where
  g := gHyb
  r0 := 7 / 50
  W := 1 / 2 ^ 30
  umax := 3 / 2
  mprime := 22147 / 10000
  gmin := -16075 / 10000
  Sbase := SbaseH
  Ibound := IboundH
  ccert := 76444 / 10000
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := wtH_sum
  g_conj := g_conj_hyb
  rayBoxes := rayBoxesH
  ray_box_ok := ray_box_ok_H
  ray_cover := ray_cover_H
  ray_tail := by
    intro u δ hu hδ
    push_cast at hu hδ ⊢
    exact tail_hyb u δ hu hδ
  nSeg := 2816
  segA := segAq
  segB := segBq
  segG := segGH
  seg_ab := seg_ab_H
  seg_ok := seg_ok_H
  seg_cover := seg_cover_thm
  Sbase_le := Sbase_le_H
  lineCells := lineCellsH
  line_ok := line_ok_H
  line_cover := line_cover_H
  I_ok := I_ok_H
  ccert_ge := by norm_num

theorem cH_norm (k : Fin (300 + 180)) : ‖cH k‖ ≤ 1 := by
  obtain ⟨a, b, c, d⟩ := pos_all k
  have h := Complex.norm_le_abs_re_add_abs_im (cH k)
  rw [abs_of_nonpos b] at h
  have : |(cH k).im| ≤ 2 / 5 := abs_le.2 ⟨by linarith, d⟩
  linarith

theorem hg_hyb : ∀ s : ℂ, certHyb.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) * CatalanLambda.Decay.Usig (1 / 1024 : ℝ) cH wtH s
    - CatalanCore.Decay.Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - (1 / 1000 : ℝ)) * Real.pi * |s.im| := by
  intro s
  have e : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by push_cast; norm_num
  rw [e]
  rfl

theorem D_le : (39028 / 10000 : ℚ) ≤ certHyb.Dof 2 (1 / 8) (17024457 / 10 ^ 7) := by
  unfold CatalanCore.Cert.CertCoreGs.Dof certHyb SbaseH IboundH SVALH
  norm_num

/-- **The hybrid λ decay certificate**: `D = 3.9028`, `c = 7.648` at `α = 1/8`. -/
theorem lam_hybrid_decay :
    HasDecay (CatalanCore.hybridFamUp CatalanFrames.Lambda.lamFrame (1 / 8 : ℚ))
      (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.decay_of_certG_rect (Fr := CatalanFrames.Lambda.lamFrame)
    CatalanCore.Cert.Sigma300.lam_decayOK certHyb (α := 1 / 8) (by norm_num) hg_hyb
    (fun k => wtH_nonneg k) (Rc := 1) (by norm_num) cH_norm Inu_le D_le

end CatalanCore.Cert.SigmaHyb
