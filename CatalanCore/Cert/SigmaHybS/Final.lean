module

public import CatalanCore.Cert.SigmaHybS.RayGlue
public import CatalanCore.Cert.SigmaHybS.SegLineGlue
public import CatalanCore.Cert.SigmaHybS.IBound
public import CatalanCore.Cert.SigmaHybS.Tail
public import CatalanCore.Cert.SigmaHyb.JfunH
public import CatalanCore.Cert.Facts
public import CatalanCore.Decay.Rect.DecayRect
public import CatalanCore.Cert.Sigma300.Glue

@[expose] public section

/-!
# The slope-`5/2`, `ρ = 1/4096` hybrid λ decay certificate (SigmaHybS)

`certS : CertCoreGs (5/2) 1650 (1/4096) (1/1000) cH wtH` with `r0 = 7/50`, `W = 2^-30`, `u_max = 3/2`,
`m′ = 54279/25000`, `g_min = -7530749/5000000`, `c = 18386549/2500000`, and the decay theorem for the λ frame
at `α = 1/8` via `decay_of_certG_rect_slope`.
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000

/-! ### rays -/

def rayBoxes : List (ℚ × ℚ) := (List.range 30720).map (fun i =>
  (2 * ((rayCellG i).2.2.1 : ℚ) / (5 * 2 ^ 40), 2 * ((rayCellG i).2.2.2 : ℚ) / (5 * 2 ^ 40)))

theorem ray_box_ok_thm : ∀ p ∈ rayBoxes, ∀ x y : ℝ,
    -((7 / 50 : ℚ) : ℝ) - p.2 - ((1 / 2 ^ 30 : ℚ) : ℝ) ≤ x →
    x ≤ -((7 / 50 : ℚ) : ℝ) - p.1 + ((1 / 2 ^ 30 : ℚ) : ℝ) →
    (5 / 2 : ℝ) * (p.1 : ℝ) ≤ y → y ≤ (5 / 2 : ℝ) * (p.2 : ℝ) →
    ((MPRAY : ℚ) : ℝ) ≤ gHyb ⟨x, y⟩ := by
  intro p hp x y hx1 hx2 hy1 hy2
  simp only [rayBoxes, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨g1, g2, g3, g4, g5⟩ := ray_geom' i hi
  have hsd := ray_sound i hi x y
  rcases hb : rayCellG i with ⟨xlo, xhi, ylo, yhi⟩
  simp only [hb] at g1 g2 g3 g4 g5 hsd hx1 hx2 hy1 hy2
  have g1r : (xhi : ℝ) < 0 := by exact_mod_cast g1
  have g2r : (0 : ℝ) ≤ ylo := by exact_mod_cast g2
  have g4r : (50 : ℝ) * xlo ≤ -7 * 2 ^ 40 - 20 * yhi - 51200 := by exact_mod_cast g4
  have g5r : (-7 : ℝ) * 2 ^ 40 - 20 * ylo + 51200 ≤ 50 * xhi := by exact_mod_cast g5
  push_cast at hx1 hx2 hy1 hy2
  have hZ : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hW : (2 : ℝ) ^ 30 = 1073741824 := by norm_num
  rw [hZ] at hx1 hx2 hy1 hy2 g4r g5r
  rw [hW] at hx1 hx2
  have hxneg : x < 0 := by linarith
  have hy0 : 0 ≤ y := by linarith
  have h1 : (xlo : ℝ) / 2 ^ 40 ≤ x := by rw [hZ]; linarith
  have h2 : x ≤ (xhi : ℝ) / 2 ^ 40 := by rw [hZ]; linarith
  have h3 : (ylo : ℝ) / 2 ^ 40 ≤ y := by rw [hZ]; linarith
  have h4 : y ≤ (yhi : ℝ) / 2 ^ 40 := by rw [hZ]; linarith
  rw [gHyb_split x y hxneg hy0]
  exact hsd h1 h2 h3 h4

theorem ray_cover_thm : ∀ u : ℝ, 0 ≤ u → u ≤ ((3 / 2 : ℚ) : ℝ) →
    ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ (p.2 : ℝ) := by
  intro u hu0 hu1
  have hc := cover_chain 30720 (fun i => 2 * ((rayCellG i).2.2.1 : ℝ) / (5 * 2 ^ 40))
    (fun i => 2 * ((rayCellG i).2.2.2 : ℝ) / (5 * 2 ^ 40)) 0 ((3 / 2 : ℚ) : ℝ) (by norm_num)
    (by
      have : (rayCellG 0).2.2.1 = 0 := ray_ends.1
      simp [this])
    (by
      have h := ray_ends.2
      have h' : (15 : ℝ) * 2 ^ 40 ≤ 4 * ((rayCellG 30719).2.2.2 : ℝ) := by exact_mod_cast h
      show ((3 / 2 : ℚ) : ℝ) ≤ 2 * ((rayCellG (30720 - 1)).2.2.2 : ℝ) / (5 * 2 ^ 40)
      rw [le_div_iff₀ (by positivity)]
      push_cast
      norm_num
      linarith)
    (by
      intro i hi
      have h := ray_chain' i hi
      have h' : ((rayCellG (i + 1)).2.2.1 : ℝ) ≤ ((rayCellG i).2.2.2 : ℝ) := by exact_mod_cast h
      have : 0 < (5 * 2 ^ 40 : ℝ) := by positivity
      exact div_le_div_of_nonneg_right (by linarith) this.le)
    u hu0 hu1
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · push_cast; exact h1
  · push_cast; exact h2

theorem ray_tail_thm : ∀ u δ : ℝ, ((3 / 2 : ℚ) : ℝ) ≤ u → |δ| ≤ ((1 / 2 ^ 30 : ℚ) : ℝ) →
    ((MPRAY : ℚ) : ℝ) ≤ gHyb ⟨-((7 / 50 : ℚ) : ℝ) + δ - u, (5 / 2 : ℝ) * u⟩ := by
  intro u δ hu hδ
  have h := tail_hyb u δ (by push_cast at hu; exact hu) (by push_cast at hδ; exact hδ)
  have e : ((MPRAY : ℚ) : ℝ) = 217116 / 100000 := by unfold MPRAY; push_cast; norm_num
  rw [e]
  push_cast
  exact h

/-! ### segment cells -/

def segAq (i : Fin 6144) : ℚ := ((segCellG i).1 : ℚ) / 2 ^ 40
def segBq (i : Fin 6144) : ℚ := ((segCellG i).2.1 : ℚ) / 2 ^ 40
def segGq (i : Fin 6144) : ℚ := ((segCellG i).2.2 : ℚ) / 2 ^ 32

theorem seg_ab_thm : ∀ i, segAq i ≤ segBq i := by
  intro i
  have h := (seg_geom' i i.2).1
  unfold segAq segBq
  have : ((segCellG i).1 : ℚ) ≤ ((segCellG i).2.1 : ℚ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

theorem gHyb_axis_nonpos {x : ℝ} (hx : x ≤ 0) : gHyb ⟨x, 0⟩ = gHR sigH x 0 := by
  rcases lt_or_eq_of_le hx with h | h
  · exact gHyb_split x 0 h le_rfl
  · subst h; exact gHyb_split_axis 0 le_rfl zero_le_one

theorem seg_ok_thm : ∀ i, ∀ x : ℝ, (segAq i : ℝ) ≤ x → x ≤ (segBq i : ℝ) →
    (segGq i : ℝ) ≤ gHyb ⟨x, 0⟩ := by
  intro i x h1 h2
  have hg := seg_geom' i i.2
  have hb : ((segCellG i).2.1 : ℝ) ≤ 0 := by exact_mod_cast hg.2
  have hx0 : x ≤ 0 := by
    have : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40 := by
      have h2' := h2; unfold segBq at h2'; push_cast at h2'; exact h2'
    have : ((segCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb (by positivity)
    linarith
  rw [gHyb_axis_nonpos hx0]
  have := seg_sound i i.2 x (by unfold segAq at h1; push_cast at h1; exact h1)
    (by unfold segBq at h2; push_cast at h2; exact h2)
  unfold segGq
  exact this

theorem seg_cover_thm : ∀ x : ℝ, -((7 / 50 : ℚ) : ℝ) ≤ x → x ≤ 0 →
    ∃ i : Fin 6144, (segAq i : ℝ) ≤ x ∧ x ≤ (segBq i : ℝ) := by
  intro x hx1 hx2
  have hc := cover_chain 6144 (fun i => ((segCellG i).1 : ℝ) / 2 ^ 40)
    (fun i => ((segCellG i).2.1 : ℝ) / 2 ^ 40) (-((7 / 50 : ℚ) : ℝ)) 0 (by norm_num)
    (by
      have h : (50 : ℝ) * ((segCellG 0).1 : ℝ) ≤ -7 * 2 ^ 40 := by exact_mod_cast seg_ends.1
      show ((segCellG 0).1 : ℝ) / 2 ^ 40 ≤ -((7 / 50 : ℚ) : ℝ)
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith)
    (by
      have h : (0 : ℝ) ≤ ((segCellG 6143).2.1 : ℝ) := by exact_mod_cast seg_ends.2
      show (0 : ℝ) ≤ ((segCellG (6144 - 1)).2.1 : ℝ) / 2 ^ 40
      positivity)
    (by
      intro i hi
      have h := seg_chain' i hi
      have h' : ((segCellG (i + 1)).1 : ℝ) ≤ ((segCellG i).2.1 : ℝ) := by exact_mod_cast h
      exact div_le_div_of_nonneg_right h' (by positivity))
    x hx1 hx2
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · unfold segAq; push_cast; exact h1
  · unfold segBq; push_cast; exact h2

lemma segterm (i : ℕ) :
    (((segCellG i).2.1 : ℝ) / 2 ^ 40 - ((segCellG i).1 : ℝ) / 2 ^ 40) *
      min ((((segCellG i).2.2 : ℝ) / 2 ^ 32) - 217116 / 100000) 0
      = (fSeg i : ℝ) / (100000 * 2 ^ 72) := by
  unfold fSeg
  by_cases h : (segCellG i).2.2 * 100000 ≤ 217116 * 2 ^ 32
  · rw [if_pos h]
    have hr : ((segCellG i).2.2 : ℝ) * 100000 ≤ 217116 * 2 ^ 32 := by exact_mod_cast h
    have hm : (((segCellG i).2.2 : ℝ) / 2 ^ 32 - 217116 / 100000) ≤ 0 := by
      have : ((segCellG i).2.2 : ℝ) / 2 ^ 32 ≤ 217116 / 100000 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_left hm]
    push_cast
    field_simp
    ring
  · rw [if_neg h]
    have hr : (217116 : ℝ) * 2 ^ 32 < ((segCellG i).2.2 : ℝ) * 100000 := by exact_mod_cast not_le.mp h
    have hm : 0 ≤ (((segCellG i).2.2 : ℝ) / 2 ^ 32 - 217116 / 100000) := by
      have : 217116 / 100000 ≤ ((segCellG i).2.2 : ℝ) / 2 ^ 32 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_right hm]
    simp

lemma sacc_sum (n : ℕ) : ∑ i ∈ Finset.range n, (fSeg i : ℝ) / (100000 * 2 ^ 72) = (sacc n : ℝ) / (100000 * 2 ^ 72) := by
  induction n with
  | zero => simp [sacc]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [sacc]; push_cast; ring

def SBASE : ℚ := (SVAL : ℚ) / (100000 * 2 ^ 72)

theorem Sbase_le_thm : (SBASE : ℝ) ≤ ∑ i : Fin 6144,
    ((segBq i : ℝ) - segAq i) * min ((segGq i : ℝ) - ((MPRAY : ℚ) : ℝ)) 0 := by
  have e : ∀ i : Fin 6144, ((segBq i : ℝ) - segAq i) * min ((segGq i : ℝ) - ((MPRAY : ℚ) : ℝ)) 0
      = (fSeg i : ℝ) / (100000 * 2 ^ 72) := by
    intro i
    rw [← segterm i]
    unfold segBq segAq segGq MPRAY
    push_cast
    norm_num
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => (fSeg i : ℝ) / (100000 * 2 ^ 72)) 6144, sacc_sum, sacc_val]
  unfold SBASE
  push_cast
  apply le_of_eq
  ring

/-! ### line cells -/

def lineCellsL : List (ℚ × ℚ) := (List.range 7168).map (fun i =>
  (((lineCellG i).1 : ℚ) / 2 ^ 40, ((lineCellG i).2.1 : ℚ) / 2 ^ 40))

theorem line_ok_thm : ∀ p ∈ lineCellsL, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ (p.2 : ℝ) →
    ((GMINS : ℚ) : ℝ) ≤ gHyb ⟨x, 0⟩ := by
  intro p hp x h1 h2
  simp only [lineCellsL, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨g0, g1, g2⟩ := line_geom' i hi
  have hb : ((lineCellG i).2.1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast g2
  have ha : (0 : ℝ) ≤ ((lineCellG i).1 : ℝ) := by exact_mod_cast g0
  push_cast at h1 h2
  have hx1 : x ≤ 1 := by
    have : ((lineCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hx0 : 0 ≤ x := by
    have : (0 : ℝ) ≤ ((lineCellG i).1 : ℝ) / 2 ^ 40 := by positivity
    linarith
  rw [gHyb_split_axis x hx0 hx1]
  exact line_sound i hi x h1 h2

theorem line_cover_thm : ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    ∃ p ∈ lineCellsL, (p.1 : ℝ) ≤ x ∧ x ≤ (p.2 : ℝ) := by
  intro x hx1 hx2
  have hc := cover_chain 7168 (fun i => ((lineCellG i).1 : ℝ) / 2 ^ 40)
    (fun i => ((lineCellG i).2.1 : ℝ) / 2 ^ 40) 0 1 (by norm_num)
    (by
      have h : ((lineCellG 0).1 : ℝ) ≤ 0 := by exact_mod_cast line_ends.1
      show ((lineCellG 0).1 : ℝ) / 2 ^ 40 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg h (by positivity))
    (by
      have h : (2 : ℝ) ^ 40 ≤ ((lineCellG 7167).2.1 : ℝ) := by exact_mod_cast line_ends.2
      show (1 : ℝ) ≤ ((lineCellG (7168 - 1)).2.1 : ℝ) / 2 ^ 40
      rw [le_div_iff₀ (by positivity)]
      linarith)
    (by
      intro i hi
      have h := line_chain' i hi
      have h' : ((lineCellG (i + 1)).1 : ℝ) ≤ ((lineCellG i).2.1 : ℝ) := by exact_mod_cast h
      exact div_le_div_of_nonneg_right h' (by positivity))
    x hx1 hx2
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · push_cast; exact h1
  · push_cast; exact h2

/-! ### the packaged certificate -/

open CatalanCore.Cert in
noncomputable def certS : CertCoreGs (5 / 2 : ℝ) 1650 (1 / 4096 : ℝ) (1 / 1000 : ℝ) cH wtH where
  g := gHyb
  r0 := 7 / 50
  W := 1 / 2 ^ 30
  umax := 3 / 2
  mprime := MPRAY
  gmin := GMINS
  Sbase := SBASE
  Ibound := IBOUNDS
  ccert := 18386549 / 2500000
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := wtH_sum
  g_conj := g_conj_hyb
  rayBoxes := rayBoxes
  ray_box_ok := ray_box_ok_thm
  ray_cover := ray_cover_thm
  ray_tail := ray_tail_thm
  nSeg := 6144
  segA := segAq
  segB := segBq
  segG := segGq
  seg_ab := seg_ab_thm
  seg_ok := seg_ok_thm
  seg_cover := seg_cover_thm
  Sbase_le := Sbase_le_thm
  lineCells := lineCellsL
  line_ok := line_ok_thm
  line_cover := line_cover_thm
  I_ok := I_ok_S
  ccert_ge := by
    unfold MPRAY GMINS
    push_cast
    norm_num

theorem hg_hybS : ∀ s : ℂ, certS.g s = (1 + (((1 / 8 : ℚ)) : ℝ)) *
    CatalanLambda.Decay.Usig (1 / 4096 : ℝ) cH wtH s
    - CatalanCore.Decay.Unu (((1 / 8 : ℚ)) : ℝ) s + (1 - (1 / 1000 : ℝ)) * Real.pi * |s.im| := by
  intro s
  have e : (((1 / 8 : ℚ)) : ℝ) = 1 / 8 := by push_cast; norm_num
  rw [e]
  rfl

theorem D_le : (39055 / 10000 : ℚ) ≤ certS.Dof 2 (1 / 8) (17024457 / 10 ^ 7) := by
  unfold CatalanCore.Cert.CertCoreGs.Dof certS
  simp only [SBASE, IBOUNDS, MPRAY, SVAL]
  norm_num

theorem lam_decayOKs : CatalanFrames.Lambda.lamFrame.DecayOKs' (5 / 2 : ℝ) where
  contour := CatalanCore.Cert.Sigma300.lam_decayOK.contour
  slope := ⟨by norm_num, by norm_num, by norm_num [CatalanFrames.Lambda.lamFrame]⟩
  atomRange := CatalanCore.Cert.Sigma300.lam_decayOK.atomRange
  norm_ge := CatalanCore.Cert.Sigma300.lam_decayOK.norm_ge

/-- **The slope-`5/2`, `ρ = 1/4096` hybrid λ decay certificate**: `D = 3.9055`, `c = 7.3546196` at `α = 1/8`. -/
theorem lam_hybrid_decayS :
    HasDecay (CatalanCore.hybridFamUp CatalanFrames.Lambda.lamFrame (1 / 8 : ℚ))
      (((39055 / 10000 : ℚ)) : ℝ) (((18386549 / 2500000 : ℚ)) : ℝ) :=
  CatalanCore.decay_of_certG_rect_slope (sl := (5 / 2 : ℝ)) (Fr := CatalanFrames.Lambda.lamFrame)
    lam_decayOKs certS (α := 1 / 8) (by norm_num) hg_hybS
    (fun k => wtH_nonneg k) (Rc := 2) (by norm_num) cH_norm
    CatalanCore.Cert.SigmaHyb.Inu_le D_le

end CatalanCore.Cert.SigmaHybS
