module

public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LH0
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LH1
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LH2
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LH3
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.LH4
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.HBridge
public import CatalanLambda.Cert.Final

@[expose] public section

/-!
# Hybrid line cells on `[0, 1]` (640 cells, `g_h ≥ -16093/10000`)
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def LP : ℕ → ℕ
  | 0 => LH0P
  | 1 => LH1P
  | 2 => LH2P
  | 3 => LH3P
  | 4 => LH4P
  | _ => 0

theorem lAll : ∀ m < 5, ∀ j < 8, lMacroOK hybS (-16075 / 10000 : ℚ) 16 (LP m) j = true := by
  intro m hm
  interval_cases m
  exacts [LH0_ok, LH1_ok, LH2_ok, LH3_ok, LH4_ok]

def lineCellH (i : ℕ) : ℤ × ℤ × ℤ := realCell 16 (LP (i / 128)) ((i % 128) / 16) (i % 16)

theorem lineH_sound (i : ℕ) (hi : i < 640) (x : ℝ) (h1 : ((lineCellH i).1 : ℝ) / 2 ^ 40 ≤ x)
    (h2 : x ≤ ((lineCellH i).2.1 : ℝ) / 2 ^ 40) :
    (((-16075 / 10000 : ℚ)) : ℝ) ≤ gfun hybS x 0 - UexR x 0 :=
  lMacro_sound hybS (-16075 / 10000 : ℚ) 16 (LP (i / 128)) ((i % 128) / 16)
    (lAll (i / 128) (by omega) ((i % 128) / 16) (by omega)) (i % 16) (by omega) x h1 h2

def lineGeomH (i : ℕ) : Bool :=
  decide (0 ≤ (lineCellH i).1 ∧ (lineCellH i).1 ≤ (lineCellH i).2.1 ∧ (lineCellH i).2.1 ≤ 2 ^ 40)

def lineChainH (i : ℕ) : Bool :=
  decide (640 ≤ i + 1 ∨ (lineCellH (i + 1)).1 ≤ (lineCellH i).2.1)

theorem lineH_geom : (List.range 640).all lineGeomH = true := by decide +kernel
theorem lineH_chain : (List.range 640).all lineChainH = true := by decide +kernel
theorem lineH_ends : (lineCellH 0).1 ≤ 0 ∧ 2 ^ 40 ≤ (lineCellH 639).2.1 := by decide +kernel

def lineCellsH : List (ℚ × ℚ) := (List.range 640).map (fun i =>
  (((lineCellH i).1 : ℚ) / 2 ^ 40, ((lineCellH i).2.1 : ℚ) / 2 ^ 40))

theorem line_ok_H : ∀ p ∈ lineCellsH, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ (p.2 : ℝ) →
    (((-16075 / 10000 : ℚ)) : ℝ) ≤ gHyb ⟨x, 0⟩ := by
  intro p hp x h1 h2
  simp only [lineCellsH, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  have hg := List.all_eq_true.mp lineH_geom i (List.mem_range.mpr hi)
  simp only [lineGeomH, decide_eq_true_eq] at hg
  push_cast at h1 h2
  have hb0 : (0 : ℝ) ≤ ((lineCellH i).1 : ℝ) := by exact_mod_cast hg.1
  have hb : ((lineCellH i).2.1 : ℝ) ≤ 2 ^ 40 := by exact_mod_cast hg.2.2
  have hx0 : 0 ≤ x := by
    have : (0 : ℝ) ≤ ((lineCellH i).1 : ℝ) / 2 ^ 40 := by positivity
    linarith
  have hx1 : x ≤ 1 := by
    have : ((lineCellH i).2.1 : ℝ) / 2 ^ 40 ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hs := lineH_sound i hi x h1 h2
  rw [show gHyb ⟨x, 0⟩ = _ from gH_split_axis x hx0 hx1, gfun_bridge_axis x hx1]
  unfold gfun at hs ⊢
  rw [usig_hyb] at hs
  linarith

theorem line_cover_H : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ p ∈ lineCellsH, (p.1 : ℝ) ≤ x ∧ x ≤ (p.2 : ℝ) := by
  intro x hx1 hx2
  have hc := cover_chain 640 (fun i => ((lineCellH i).1 : ℝ) / 2 ^ 40)
    (fun i => ((lineCellH i).2.1 : ℝ) / 2 ^ 40) 0 1 (by norm_num)
    (by
      have h : ((lineCellH 0).1 : ℝ) ≤ 0 := by exact_mod_cast lineH_ends.1
      show ((lineCellH 0).1 : ℝ) / 2 ^ 40 ≤ 0
      exact div_nonpos_of_nonpos_of_nonneg h (by positivity))
    (by
      have h : (2 : ℝ) ^ 40 ≤ ((lineCellH 639).2.1 : ℝ) := by exact_mod_cast lineH_ends.2
      show (1 : ℝ) ≤ ((lineCellH (640 - 1)).2.1 : ℝ) / 2 ^ 40
      rw [le_div_iff₀ (by positivity)]
      linarith)
    (by
      intro i hi
      have hh := List.all_eq_true.mp lineH_chain i (List.mem_range.mpr (by omega))
      simp only [lineChainH, decide_eq_true_eq] at hh
      rcases hh with hh | hh
      · omega
      · have h' : ((lineCellH (i + 1)).1 : ℝ) ≤ ((lineCellH i).2.1 : ℝ) := by exact_mod_cast hh
        exact div_le_div_of_nonneg_right h' (by positivity))
    x hx1 hx2
  obtain ⟨i, hi, h1, h2⟩ := hc
  refine ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ?_, ?_⟩
  · push_cast; exact h1
  · push_cast; exact h2

end CatalanCore.Cert.SigmaHyb
