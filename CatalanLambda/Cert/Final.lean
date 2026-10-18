import CatalanLambda.Cert.RayGlue
import CatalanLambda.Cert.SegLineGlue
import CatalanLambda.Cert.IBound
import CatalanLambda.Cert.Tail

/-!
# The numerical certificate as `CertFacts` (BT §5)

`σ = ` the K = 300 measure `sigmaS`, `ρ = 1/1024`, `ε = 1/1000`, `r0 = 7/50`, `W = 2^-30`,
`u_max = 3/2`, `m′ = 197179/100000`, `g_min = -14645/10000`.
-/

open Real

namespace CatalanLambda.Cert

set_option maxRecDepth 100000

/-! ### rays -/

def rayBoxes : List (ℚ × ℚ) := (List.range 27648).map (fun i =>
  (((rayCellG i).2.2.1 : ℚ) / (3 * 2 ^ 40), ((rayCellG i).2.2.2 : ℚ) / (3 * 2 ^ 40)))

theorem ray_box_ok_thm : ∀ p ∈ rayBoxes, ∀ x y : ℝ,
    -((7 / 50 : ℚ) : ℝ) - p.2 - ((1 / 2 ^ 30 : ℚ) : ℝ) ≤ x →
    x ≤ -((7 / 50 : ℚ) : ℝ) - p.1 + ((1 / 2 ^ 30 : ℚ) : ℝ) →
    3 * (p.1 : ℝ) ≤ y → y ≤ 3 * (p.2 : ℝ) →
    ((MPRAY : ℚ) : ℝ) ≤ Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, y⟩ := by
  intro p hp x y hx1 hx2 hy1 hy2
  simp only [rayBoxes, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨g1, g2, g3, g4, g5⟩ := ray_geom' i hi
  have hsd := ray_sound i hi x y
  rcases hb : rayCellG i with ⟨xlo, xhi, ylo, yhi⟩
  simp only [hb] at g1 g2 g3 g4 g5 hsd hx1 hx2 hy1 hy2
  have g1r : (xhi : ℝ) < 0 := by exact_mod_cast g1
  have g2r : (0 : ℝ) ≤ ylo := by exact_mod_cast g2
  have g4r : (150 : ℝ) * xlo ≤ -21 * 2 ^ 40 - 50 * yhi - 153600 := by exact_mod_cast g4
  have g5r : (-21 : ℝ) * 2 ^ 40 - 50 * ylo + 153600 ≤ 150 * xhi := by exact_mod_cast g5
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
  rw [gfun_bridge x y hxneg hy0]
  exact hsd h1 h2 h3 h4

theorem ray_cover_thm : ∀ u : ℝ, 0 ≤ u → u ≤ ((3 / 2 : ℚ) : ℝ) →
    ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ (p.2 : ℝ) := by
  intro u hu0 hu1
  have hc := cover_chain 27648 (fun i => ((rayCellG i).2.2.1 : ℝ) / (3 * 2 ^ 40))
    (fun i => ((rayCellG i).2.2.2 : ℝ) / (3 * 2 ^ 40)) 0 ((3 / 2 : ℚ) : ℝ) (by norm_num)
    (by
      have : (rayCellG 0).2.2.1 = 0 := ray_ends.1
      simp [this])
    (by
      have h := ray_ends.2
      have h' : (9 : ℝ) * 2 ^ 40 ≤ 2 * ((rayCellG 27647).2.2.2 : ℝ) := by exact_mod_cast h
      show ((3 / 2 : ℚ) : ℝ) ≤ ((rayCellG (27648 - 1)).2.2.2 : ℝ) / (3 * 2 ^ 40)
      rw [le_div_iff₀ (by positivity)]
      push_cast
      norm_num
      linarith)
    (by
      intro i hi
      have h := ray_chain' i hi
      have h' : ((rayCellG (i + 1)).2.2.1 : ℝ) ≤ ((rayCellG i).2.2.2 : ℝ) := by exact_mod_cast h
      exact div_le_div_of_nonneg_right h' (by positivity))
    u hu0 hu1
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · push_cast; exact h1
  · push_cast; exact h2

theorem ray_tail_thm : ∀ u δ : ℝ, ((3 / 2 : ℚ) : ℝ) ≤ u → |δ| ≤ ((1 / 2 ^ 30 : ℚ) : ℝ) →
    ((MPRAY : ℚ) : ℝ) ≤
      Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨-((7 / 50 : ℚ) : ℝ) + δ - u, 3 * u⟩ := by
  intro u δ hu hδ
  have h := tail_core u δ (by push_cast at hu; exact hu) (by push_cast at hδ; exact hδ)
  have e : ((MPRAY : ℚ) : ℝ) = 197179 / 100000 := by unfold MPRAY; push_cast; norm_num
  rw [e]
  push_cast
  exact h

/-! ### segment cells -/

def segAq (i : Fin 2816) : ℚ := ((segCellG i).1 : ℚ) / 2 ^ 40
def segBq (i : Fin 2816) : ℚ := ((segCellG i).2.1 : ℚ) / 2 ^ 40
def segGq (i : Fin 2816) : ℚ := ((segCellG i).2.2 : ℚ) / 2 ^ 32

theorem seg_ab_thm : ∀ i, segAq i ≤ segBq i := by
  intro i
  have h := (seg_geom' i i.2).1
  unfold segAq segBq
  have : ((segCellG i).1 : ℚ) ≤ ((segCellG i).2.1 : ℚ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right this (by positivity)

theorem seg_ok_thm : ∀ i, ∀ x : ℝ, (segAq i : ℝ) ≤ x → x ≤ (segBq i : ℝ) →
    (segGq i : ℝ) ≤ Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, 0⟩ := by
  intro i x h1 h2
  have hg := seg_geom' i i.2
  have hb : ((segCellG i).2.1 : ℝ) ≤ 0 := by exact_mod_cast hg.2
  have hx1 : x ≤ 1 := by
    have : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40 := by
      have h2' := h2; unfold segBq at h2'; push_cast at h2'; exact h2'
    have : ((segCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb (by positivity)
    linarith
  rw [gfun_bridge_axis x hx1]
  have := seg_sound i i.2 x (by unfold segAq at h1; push_cast at h1; exact h1)
    (by unfold segBq at h2; push_cast at h2; exact h2)
  unfold segGq
  exact this

theorem seg_cover_thm : ∀ x : ℝ, -((7 / 50 : ℚ) : ℝ) ≤ x → x ≤ 0 →
    ∃ i : Fin 2816, (segAq i : ℝ) ≤ x ∧ x ≤ (segBq i : ℝ) := by
  intro x hx1 hx2
  have hc := cover_chain 2816 (fun i => ((segCellG i).1 : ℝ) / 2 ^ 40)
    (fun i => ((segCellG i).2.1 : ℝ) / 2 ^ 40) (-((7 / 50 : ℚ) : ℝ)) 0 (by norm_num)
    (by
      have h : (50 : ℝ) * ((segCellG 0).1 : ℝ) ≤ -7 * 2 ^ 40 := by exact_mod_cast seg_ends.1
      show ((segCellG 0).1 : ℝ) / 2 ^ 40 ≤ -((7 / 50 : ℚ) : ℝ)
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith)
    (by
      have h : (0 : ℝ) ≤ ((segCellG 2815).2.1 : ℝ) := by exact_mod_cast seg_ends.2
      show (0 : ℝ) ≤ ((segCellG (2816 - 1)).2.1 : ℝ) / 2 ^ 40
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
      min ((((segCellG i).2.2 : ℝ) / 2 ^ 32) - 197179 / 100000) 0
      = (fSeg i : ℝ) / (100000 * 2 ^ 72) := by
  unfold fSeg
  by_cases h : (segCellG i).2.2 * 100000 ≤ 197179 * 2 ^ 32
  · rw [if_pos h]
    have hr : ((segCellG i).2.2 : ℝ) * 100000 ≤ 197179 * 2 ^ 32 := by exact_mod_cast h
    have hm : (((segCellG i).2.2 : ℝ) / 2 ^ 32 - 197179 / 100000) ≤ 0 := by
      have : ((segCellG i).2.2 : ℝ) / 2 ^ 32 ≤ 197179 / 100000 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_left hm]
    push_cast
    field_simp
    ring
  · rw [if_neg h]
    have hr : (197179 : ℝ) * 2 ^ 32 < ((segCellG i).2.2 : ℝ) * 100000 := by exact_mod_cast not_le.mp h
    have hm : 0 ≤ (((segCellG i).2.2 : ℝ) / 2 ^ 32 - 197179 / 100000) := by
      have : 197179 / 100000 ≤ ((segCellG i).2.2 : ℝ) / 2 ^ 32 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_right hm]
    simp

lemma sacc_sum (n : ℕ) : ∑ i ∈ Finset.range n, (fSeg i : ℝ) / (100000 * 2 ^ 72) = (sacc n : ℝ) / (100000 * 2 ^ 72) := by
  induction n with
  | zero => simp [sacc]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [sacc]; push_cast; ring

def SCERT : ℚ := 2 * (SVAL : ℚ) / (100000 * 2 ^ 72)

theorem Scert_le_thm : (SCERT : ℝ) ≤ 2 * ∑ i : Fin 2816,
    ((segBq i : ℝ) - segAq i) * min ((segGq i : ℝ) - ((MPRAY : ℚ) : ℝ)) 0 := by
  have e : ∀ i : Fin 2816, ((segBq i : ℝ) - segAq i) * min ((segGq i : ℝ) - ((MPRAY : ℚ) : ℝ)) 0
      = (fSeg i : ℝ) / (100000 * 2 ^ 72) := by
    intro i
    rw [← segterm i]
    unfold segBq segAq segGq MPRAY
    push_cast
    rfl
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => (fSeg i : ℝ) / (100000 * 2 ^ 72)) 2816, sacc_sum, sacc_val]
  unfold SCERT
  push_cast
  apply le_of_eq
  ring

/-! ### line cells -/

def lineCellG (i : ℕ) : ℤ × ℤ × ℤ := realCell 32 LineMP (i / 32) (i % 32)

def lineCellsL : List (ℚ × ℚ) := (List.range 512).map (fun i =>
  (((lineCellG i).1 : ℚ) / 2 ^ 40, ((lineCellG i).2.1 : ℚ) / 2 ^ 40))

theorem line_sound (i : ℕ) (hi : i < 512) (x : ℝ) (h1 : ((lineCellG i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((lineCellG i).2.1 : ℝ) / 2 ^ 40) :
    (((-14645 / 10000 : ℚ) : ℚ) : ℝ) ≤ gfun sigmaS x 0 := by
  have := realMacro_sound false (-14645 / 10000 : ℚ) 32 LineMP (i / 32) (LineM_ok (i / 32) (by omega))
    (i % 32) (by omega) x h1 h2
  simpa [realThr] using this

def lineGeomCell (i : ℕ) : Bool :=
  decide ((lineCellG i).1 ≤ (lineCellG i).2.1 ∧ (lineCellG i).2.1 ≤ 2 ^ 40)

def lineChainCell (i : ℕ) : Bool :=
  decide (512 ≤ i + 1 ∨ (lineCellG (i + 1)).1 ≤ (lineCellG i).2.1)

theorem line_geom : (List.range 512).all lineGeomCell = true := by decide +kernel
theorem line_chain : (List.range 512).all lineChainCell = true := by decide +kernel
theorem line_ends : 64 * (lineCellG 0).1 ≤ -2 ^ 40 ∧ 2 ^ 40 ≤ (lineCellG 511).2.1 := by decide +kernel

theorem line_ok_thm : ∀ p ∈ lineCellsL, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ (p.2 : ℝ) →
    (((-14645 / 10000 : ℚ) : ℚ) : ℝ) ≤ Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, 0⟩ := by
  intro p hp x h1 h2
  simp only [lineCellsL, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hg := List.all_eq_true.mp line_geom i (List.mem_range.mpr hi)
  simp only [lineGeomCell, decide_eq_true_eq] at hg
  have hb : ((lineCellG i).2.1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hg.2
  push_cast at h1 h2
  have hx1 : x ≤ 1 := by
    have : ((lineCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  rw [gfun_bridge_axis x hx1]
  exact line_sound i hi x h1 h2

theorem line_cover_thm : ∀ x : ℝ, -(1 / 64 : ℝ) ≤ x → x ≤ 1 →
    ∃ p ∈ lineCellsL, (p.1 : ℝ) ≤ x ∧ x ≤ (p.2 : ℝ) := by
  intro x hx1 hx2
  have hc := cover_chain 512 (fun i => ((lineCellG i).1 : ℝ) / 2 ^ 40)
    (fun i => ((lineCellG i).2.1 : ℝ) / 2 ^ 40) (-(1 / 64 : ℝ)) 1 (by norm_num)
    (by
      have h : (64 : ℝ) * ((lineCellG 0).1 : ℝ) ≤ -2 ^ 40 := by exact_mod_cast line_ends.1
      show ((lineCellG 0).1 : ℝ) / 2 ^ 40 ≤ -(1 / 64 : ℝ)
      rw [div_le_iff₀ (by positivity)]
      linarith)
    (by
      have h : (2 : ℝ) ^ 40 ≤ ((lineCellG 511).2.1 : ℝ) := by exact_mod_cast line_ends.2
      show (1 : ℝ) ≤ ((lineCellG (512 - 1)).2.1 : ℝ) / 2 ^ 40
      rw [le_div_iff₀ (by positivity)]
      linarith)
    (by
      intro i hi
      have hh := List.all_eq_true.mp line_chain i (List.mem_range.mpr (by omega))
      simp only [lineChainCell, decide_eq_true_eq] at hh
      rcases hh with hh | hh
      · omega
      · have h' : ((lineCellG (i + 1)).1 : ℝ) ≤ ((lineCellG i).2.1 : ℝ) := by exact_mod_cast hh
        exact div_le_div_of_nonneg_right h' (by positivity))
    x hx1 hx2
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · push_cast; exact h1
  · push_cast; exact h2

/-! ### the packaged certificate -/

noncomputable def certFacts : Decay.CertFacts 300 (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS where
  r0 := 7 / 50
  W := 1 / 2 ^ 30
  umax := 3 / 2
  mprime := MPRAY
  gmin := -14645 / 10000
  Scert := SCERT
  Ibound := IBOUND
  Dcert := 31111 / 10000
  ccert := 68726 / 10000
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := mS_sum
  g_conj := g_conj_cert
  rayBoxes := rayBoxes
  ray_box_ok := ray_box_ok_thm
  ray_cover := ray_cover_thm
  ray_tail := ray_tail_thm
  nSeg := 2816
  segA := segAq
  segB := segBq
  segG := segGq
  seg_ab := seg_ab_thm
  seg_ok := seg_ok_thm
  seg_cover := seg_cover_thm
  Scert_le := Scert_le_thm
  lineCells := lineCellsL
  line_ok := line_ok_thm
  line_cover := line_cover_thm
  I_ok := I_ok
  Dcert_le := by
    unfold SCERT IBOUND MPRAY SVAL
    push_cast
    norm_num
  ccert_ge := by
    unfold MPRAY
    push_cast
    norm_num

#print axioms certFacts

end CatalanLambda.Cert
