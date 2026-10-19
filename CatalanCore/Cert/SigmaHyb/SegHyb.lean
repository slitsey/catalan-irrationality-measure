module

public import CatalanCore.Cert.SigmaHyb.HS0
public import CatalanCore.Cert.SigmaHyb.HS1
public import CatalanCore.Cert.SigmaHyb.HS2
public import CatalanCore.Cert.SigmaHyb.HBridge
public import CatalanLambda.Cert.Final

@[expose] public section

/-!
# Hybrid segment cells on `[-r0, 0]`

The 2816 legacy cells (`segCellG i = (a, b, γ)`, `γ/2^32 ≤ g_sq`) are grouped 4 by 4 into coarse
cells (`HS*`, `704` cells, boxes `(a, b, 0, 0)`) with `γ'/2^32 ≤ h = U^λ - U^ex` on the coarse cell.
`segG i = γ_i/2^32 + γ'_{i/4}/2^32`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def SP : ℕ → ℕ
  | 0 => HS0P
  | 1 => HS1P
  | 2 => HS2P
  | _ => 0

theorem sAll : ∀ m < 3, ∀ j < 8, hMacroOK lamS 32 (SP m) j = true := by
  intro m hm
  interval_cases m
  exacts [HS0_ok, HS1_ok, HS2_ok]

def sBox (g : ℕ) : ℤ × ℤ × ℤ × ℤ := hCellBox 32 (SP (g / 256)) ((g % 256) / 32) (g % 32)
def sGam (g : ℕ) : ℤ := hCellGam 32 (SP (g / 256)) ((g % 256) / 32) (g % 32)

theorem sSound (g : ℕ) (hg : g < 768) (x y : ℝ)
    (h1 : ((sBox g).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((sBox g).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((sBox g).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((sBox g).2.2.2 : ℝ) / 2 ^ 40) :
    (((sGam g : ℤ) : ℝ) / 2 ^ 32) ≤ Usig lamS x y - UexR x y := by
  have := hMod_sound lamS 32 (SP (g / 256)) 8 (sAll (g / 256) (by omega)) ((g % 256) / 32)
    (by omega) (g % 32) (by omega) x y h1 h2 h3 h4
  simpa [sGam] using this

def segOK (i : ℕ) : Bool :=
  let j := i / 4
  decide ((sBox j).1 ≤ (segCellG i).1 ∧ (segCellG i).2.1 ≤ (sBox j).2.1 ∧
    (sBox j).2.2.1 = 0 ∧ (sBox j).2.2.2 = 0)

theorem seg_check : ∀ m < 4, (List.range 704).all (fun i => segOK (704 * m + i)) = true := by
  decide +kernel

lemma segOK' (i : ℕ) (hi : i < 2816) : (sBox (i / 4)).1 ≤ (segCellG i).1 ∧
    (segCellG i).2.1 ≤ (sBox (i / 4)).2.1 ∧ (sBox (i / 4)).2.2.1 = 0 ∧ (sBox (i / 4)).2.2.2 = 0 := by
  have h := List.all_eq_true.mp (seg_check (i / 704) (by omega)) (i % 704) (List.mem_range.mpr (by omega))
  have e : 704 * (i / 704) + i % 704 = i := by omega
  rw [e] at h
  simpa [segOK] using h

noncomputable def segGH (i : Fin 2816) : ℚ := segGq i + ((sGam (i / 4) : ℤ) : ℚ) / 2 ^ 32

theorem seg_ok_H : ∀ i : Fin 2816, ∀ x : ℝ, (segAq i : ℝ) ≤ x → x ≤ (segBq i : ℝ) →
    (segGH i : ℝ) ≤ gHyb ⟨x, 0⟩ := by
  intro i x h1 h2
  have hg := seg_geom' i i.2
  have hb : ((segCellG i).2.1 : ℝ) ≤ 0 := by exact_mod_cast hg.2
  have hx0 : x ≤ 0 := by
    have : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40 := by
      have h2' := h2; unfold segBq at h2'; push_cast at h2'; exact h2'
    have : ((segCellG i).2.1 : ℝ) / 2 ^ 40 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb (by positivity)
    linarith
  have hleg := seg_ok_thm i x h1 h2
  have hsplit : gHyb ⟨x, 0⟩ = CatalanLambda.Decay.gfun (1 / 1024 : ℝ) (1 / 1000 : ℝ) cS mS ⟨x, 0⟩
      + (Usig lamS x 0 - UexR x 0) := by
    rcases lt_or_ge x 0 with hx | hx
    · exact gH_split x 0 hx le_rfl
    · exact gH_split_axis x hx (by linarith)
  obtain ⟨c1, c2, c3, c4⟩ := segOK' i i.2
  have hj : (i : ℕ) / 4 < 768 := by have := i.2; omega
  have hh := sSound (i / 4) hj x 0
    (by
      have : ((sBox (i / 4)).1 : ℝ) ≤ ((segCellG i).1 : ℝ) := by exact_mod_cast c1
      have h1' : ((segCellG i).1 : ℝ) / 2 ^ 40 ≤ x := by
        have := h1; unfold segAq at this; push_cast at this; exact this
      have : ((sBox (i / 4)).1 : ℝ) / 2 ^ 40 ≤ ((segCellG i).1 : ℝ) / 2 ^ 40 :=
        div_le_div_of_nonneg_right this (by positivity)
      linarith)
    (by
      have : ((segCellG i).2.1 : ℝ) ≤ ((sBox (i / 4)).2.1 : ℝ) := by exact_mod_cast c2
      have h2' : x ≤ ((segCellG i).2.1 : ℝ) / 2 ^ 40 := by
        have := h2; unfold segBq at this; push_cast at this; exact this
      have : ((segCellG i).2.1 : ℝ) / 2 ^ 40 ≤ ((sBox (i / 4)).2.1 : ℝ) / 2 ^ 40 :=
        div_le_div_of_nonneg_right this (by positivity)
      linarith)
    (by rw [c3]; simp) (by rw [c4]; simp)
  rw [hsplit]
  unfold segGH
  push_cast
  have : (segGq i : ℝ) ≤ _ := hleg
  linarith

def fSegH (i : ℕ) : ℤ :=
  ((segCellG i).2.1 - (segCellG i).1) *
    (if ((segCellG i).2.2 + sGam (i / 4)) * 10000 ≤ 22147 * 2 ^ 32
      then ((segCellG i).2.2 + sGam (i / 4)) * 10000 - 22147 * 2 ^ 32 else 0)

def saccH : ℕ → ℤ
  | 0 => 0
  | n + 1 => saccH n + fSegH n

def SVALH : ℤ := -2884825129940100551555168

theorem saccH_val : saccH 2816 = SVALH := by decide +kernel

lemma segtermH (i : Fin 2816) :
    (((segCellG i).2.1 : ℝ) / 2 ^ 40 - ((segCellG i).1 : ℝ) / 2 ^ 40) *
      min ((segGH i : ℝ) - 22147 / 10000) 0 = (fSegH i : ℝ) / (10000 * 2 ^ 72) := by
  unfold fSegH segGH segGq
  have hs : (((segCellG i).2.2 : ℚ) / 2 ^ 32 + ((sGam (i / 4) : ℤ) : ℚ) / 2 ^ 32 : ℚ)
      = (((segCellG i).2.2 + sGam (i / 4) : ℤ) : ℚ) / 2 ^ 32 := by push_cast; ring
  push_cast
  set g : ℤ := (segCellG i).2.2 + sGam (i / 4) with hg
  have hgR : (((segCellG i).2.2 : ℝ) / 2 ^ 32 + ((sGam (i / 4) : ℤ) : ℝ) / 2 ^ 32) = (g : ℝ) / 2 ^ 32 := by
    rw [hg]; push_cast; ring
  rw [hgR]
  by_cases h : g * 10000 ≤ 22147 * 2 ^ 32
  · rw [if_pos (by simpa [hg] using h)]
    have hr : (g : ℝ) * 10000 ≤ 22147 * 2 ^ 32 := by exact_mod_cast h
    have hm : ((g : ℝ) / 2 ^ 32 - 22147 / 10000) ≤ 0 := by
      have : (g : ℝ) / 2 ^ 32 ≤ 22147 / 10000 := by
        rw [div_le_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_left hm]
    push_cast
    field_simp
    ring
  · rw [if_neg (by simpa [hg] using h)]
    have hr : (22147 : ℝ) * 2 ^ 32 < (g : ℝ) * 10000 := by exact_mod_cast not_le.mp h
    have hm : 0 ≤ ((g : ℝ) / 2 ^ 32 - 22147 / 10000) := by
      have : 22147 / 10000 ≤ (g : ℝ) / 2 ^ 32 := by
        rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    rw [min_eq_right hm]
    simp

lemma saccH_sum (n : ℕ) : ∑ i ∈ Finset.range n, (fSegH i : ℝ) / (10000 * 2 ^ 72)
    = (saccH n : ℝ) / (10000 * 2 ^ 72) := by
  induction n with
  | zero => simp [saccH]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp only [saccH]; push_cast; ring

def SbaseH : ℚ := (SVALH : ℚ) / (10000 * 2 ^ 72)

theorem Sbase_le_H : (SbaseH : ℝ) ≤ ∑ i : Fin 2816,
    ((segBq i : ℝ) - segAq i) * min ((segGH i : ℝ) - ((22147 / 10000 : ℚ) : ℝ)) 0 := by
  have e : ∀ i : Fin 2816, ((segBq i : ℝ) - segAq i) * min ((segGH i : ℝ) - ((22147 / 10000 : ℚ) : ℝ)) 0
      = (fSegH i : ℝ) / (10000 * 2 ^ 72) := by
    intro i
    rw [← segtermH i]
    unfold segBq segAq
    push_cast
    rfl
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun i => (fSegH i : ℝ) / (10000 * 2 ^ 72)) 2816, saccH_sum, saccH_val]
  unfold SbaseH
  push_cast
  apply le_of_eq
  ring

theorem seg_ab_H : ∀ i, segAq i ≤ segBq i := seg_ab_thm

end CatalanCore.Cert.SigmaHyb
