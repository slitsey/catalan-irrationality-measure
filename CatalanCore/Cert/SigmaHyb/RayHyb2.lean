module

public import CatalanCore.Cert.SigmaHyb.RayHyb

@[expose] public section

/-!
# Hybrid ray cells: soundness (`ray_box_ok`) and cover
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def rayBoxesH : List (ℚ × ℚ) :=
  (List.range NR).map (fun t => ((refY t : ℚ) / (3 * 2 ^ 40), (refY (t + 1) : ℚ) / (3 * 2 ^ 40))) ++
  (List.range 228).map (fun k => (((bBox k).2.2.1 : ℚ) / (3 * 2 ^ 40), ((bBox k).2.2.2 : ℚ) / (3 * 2 ^ 40)))

lemma NR_eq : NR = 25115 := rfl

theorem refOK_true (t : ℕ) (ht : t < NR) : refOK t = true := by
  have hlt : t < 25115 := by rw [NR_eq] at ht; exact ht
  have h := ref_check (t / 5100) (by omega)
  have h2 := List.all_eq_true.mp h (t % 5100) (List.mem_range.mpr (by omega))
  have e : 5100 * (t / 5100) + t % 5100 = t := by omega
  rw [e] at h2
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h2
  rcases h2 with h2 | h2
  · rw [NR_eq] at h2; omega
  · exact h2

theorem rayA_ok (t : ℕ) (ht : t < NR) (x y : ℝ)
    (hx1 : -(7 / 50 : ℝ) - (refY (t + 1) : ℝ) / (3 * 2 ^ 40) - 1 / 2 ^ 30 ≤ x)
    (hx2 : x ≤ -(7 / 50 : ℝ) - (refY t : ℝ) / (3 * 2 ^ 40) + 1 / 2 ^ 30)
    (hy1 : 3 * ((refY t : ℝ) / (3 * 2 ^ 40)) ≤ y) (hy2 : y ≤ 3 * ((refY (t + 1) : ℝ) / (3 * 2 ^ 40))) :
    (22147 / 10000 : ℝ) ≤ gHyb ⟨x, y⟩ := by
  have hok := refOK_true t ht
  unfold refOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hb01, hI, hJ⟩, hL1, hL2⟩, hC1, hC2, hC3, hC4⟩ := hok
  set I := u16 refI t with hIdef
  set J := u16 refJ t with hJdef
  set b0 := refY t with hb0
  set b1 := refY (t + 1) with hb1
  have hZ : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hW : (2 : ℝ) ^ 30 = 1073741824 := by norm_num
  rw [hZ] at hx1 hx2 hy1 hy2
  rw [hW] at hx1 hx2
  have hlg := ray_geom' I hI
  have hyl0 : (0 : ℤ) ≤ (rayCellG I).2.2.1 := hlg.2.1
  have hb0r : (0 : ℝ) ≤ b0 := by exact_mod_cast hyl0.trans hL1
  have hb01r : (b0 : ℝ) ≤ b1 := by exact_mod_cast hb01
  have hxneg : x < 0 := by
    have : (0 : ℝ) ≤ (b0 : ℝ) / (3 * 1099511627776) := by positivity
    linarith
  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ (b0 : ℝ) / (3 * 1099511627776) := by positivity
    linarith
  -- legacy part
  have hp : ((((rayCellG I).2.2.1 : ℚ) / (3 * 2 ^ 40), ((rayCellG I).2.2.2 : ℚ) / (3 * 2 ^ 40)) : ℚ × ℚ)
      ∈ CatalanLambda.Cert.rayBoxes := by
    simp only [CatalanLambda.Cert.rayBoxes, List.mem_map, List.mem_range]
    exact ⟨I, hI, rfl⟩
  have hL1r : ((rayCellG I).2.2.1 : ℝ) ≤ b0 := by exact_mod_cast hL1
  have hL2r : (b1 : ℝ) ≤ ((rayCellG I).2.2.2 : ℝ) := by exact_mod_cast hL2
  have hsq := CatalanLambda.Cert.ray_box_ok_thm _ hp x y
    (by push_cast; rw [hZ, hW]; have : (b1 : ℝ) / (3 * 1099511627776) ≤ ((rayCellG I).2.2.2 : ℝ) / (3 * 1099511627776) := by
          apply div_le_div_of_nonneg_right hL2r (by positivity)
        linarith)
    (by push_cast; rw [hZ, hW]; have : ((rayCellG I).2.2.1 : ℝ) / (3 * 1099511627776) ≤ (b0 : ℝ) / (3 * 1099511627776) := by
          apply div_le_div_of_nonneg_right hL1r (by positivity)
        linarith)
    (by push_cast; rw [hZ]; have : ((rayCellG I).2.2.1 : ℝ) / (3 * 1099511627776) ≤ (b0 : ℝ) / (3 * 1099511627776) := by
          apply div_le_div_of_nonneg_right hL1r (by positivity)
        linarith)
    (by push_cast; rw [hZ]; have : (b1 : ℝ) / (3 * 1099511627776) ≤ ((rayCellG I).2.2.2 : ℝ) / (3 * 1099511627776) := by
          apply div_le_div_of_nonneg_right hL2r (by positivity)
        linarith)
  -- h part
  have hJ' : J < 1024 := by omega
  have hc3 : (150 : ℝ) * (aBox J).1 ≤ -21 * 1099511627776 - 50 * b1 - 153600 := by
    have := (show ((150 * (aBox J).1 : ℤ) : ℝ) ≤ ((-21 * 2 ^ 40 - 50 * b1 - 153600 : ℤ) : ℝ) from by exact_mod_cast hC3)
    push_cast at this; rw [hZ] at this; linarith
  have hc4 : (-21 : ℝ) * 1099511627776 - 50 * b0 + 153600 ≤ 150 * (aBox J).2.1 := by
    have := (show ((-21 * 2 ^ 40 - 50 * b0 + 153600 : ℤ) : ℝ) ≤ ((150 * (aBox J).2.1 : ℤ) : ℝ) from by exact_mod_cast hC4)
    push_cast at this; rw [hZ] at this; linarith
  have hc1 : ((aBox J).2.2.1 : ℝ) ≤ b0 := by exact_mod_cast hC1
  have hc2 : (b1 : ℝ) ≤ ((aBox J).2.2.2 : ℝ) := by exact_mod_cast hC2
  have hh := aSound J hJ' x y
    (by rw [hZ, div_le_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, le_div_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, div_le_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, le_div_iff₀ (by norm_num)]; linarith)
  have hg := (List.all_eq_true.mp gam_check J (List.mem_range.mpr hJ))
  simp only [gamOK, decide_eq_true_eq] at hg
  have hg' : (197179 / 100000 : ℝ) + ((aGam J : ℤ) : ℝ) / 2 ^ 32 ≥ 22147 / 10000 := by
    have := (Rat.cast_le (K := ℝ)).2 hg
    push_cast at this; exact this
  have hs : ((MPRAY : ℚ) : ℝ) = 197179 / 100000 := by unfold MPRAY; push_cast; norm_num
  rw [show gHyb ⟨x, y⟩ = _ from gH_split x y hxneg hy0]
  rw [hs] at hsq
  linarith

theorem rayB_ok (k : ℕ) (hk : k < 228) (x y : ℝ)
    (hx1 : -(7 / 50 : ℝ) - ((bBox k).2.2.2 : ℝ) / (3 * 2 ^ 40) - 1 / 2 ^ 30 ≤ x)
    (hx2 : x ≤ -(7 / 50 : ℝ) - ((bBox k).2.2.1 : ℝ) / (3 * 2 ^ 40) + 1 / 2 ^ 30)
    (hy1 : 3 * (((bBox k).2.2.1 : ℝ) / (3 * 2 ^ 40)) ≤ y)
    (hy2 : y ≤ 3 * (((bBox k).2.2.2 : ℝ) / (3 * 2 ^ 40))) :
    (22147 / 10000 : ℝ) ≤ gHyb ⟨x, y⟩ := by
  have hok := List.all_eq_true.mp b_check k (List.mem_range.mpr hk)
  simp only [bOK, decide_eq_true_eq] at hok
  obtain ⟨hb0, hb01, hxh, hc3, hc4⟩ := hok
  set b0 := (bBox k).2.2.1 with hb0def
  set b1 := (bBox k).2.2.2 with hb1def
  have hZ : (2 : ℝ) ^ 40 = 1099511627776 := by norm_num
  have hW : (2 : ℝ) ^ 30 = 1073741824 := by norm_num
  rw [hZ] at hx1 hx2 hy1 hy2
  rw [hW] at hx1 hx2
  have hb0r : (0 : ℝ) ≤ b0 := by exact_mod_cast hb0
  have hxneg : x < 0 := by
    have : (0 : ℝ) ≤ (b0 : ℝ) / (3 * 1099511627776) := by positivity
    linarith
  have hy0 : 0 ≤ y := by
    have : (0 : ℝ) ≤ (b0 : ℝ) / (3 * 1099511627776) := by positivity
    linarith
  have hc3r : (150 : ℝ) * (bBox k).1 ≤ -21 * 1099511627776 - 50 * b1 - 153600 := by
    have := (show ((150 * (bBox k).1 : ℤ) : ℝ) ≤ ((-21 * 2 ^ 40 - 50 * b1 - 153600 : ℤ) : ℝ) from by exact_mod_cast hc3)
    push_cast at this; rw [hZ] at this; linarith
  have hc4r : (-21 : ℝ) * 1099511627776 - 50 * b0 + 153600 ≤ 150 * (bBox k).2.1 := by
    have := (show ((-21 * 2 ^ 40 - 50 * b0 + 153600 : ℤ) : ℝ) ≤ ((150 * (bBox k).2.1 : ℤ) : ℝ) from by exact_mod_cast hc4)
    push_cast at this; rw [hZ] at this; linarith
  have hh := bSound k (by omega) x y
    (by rw [hZ, div_le_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, le_div_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, div_le_iff₀ (by norm_num)]; linarith)
    (by rw [hZ, le_div_iff₀ (by norm_num)]; linarith)
  rw [show gHyb ⟨x, y⟩ = _ from gH_split x y hxneg hy0, gfun_bridge x y hxneg hy0]
  unfold gHR at hh
  unfold CatalanLambda.Cert.gfun at hh ⊢
  rw [usig_hyb] at hh
  push_cast at hh
  linarith

theorem ray_box_ok_H : ∀ p ∈ rayBoxesH, ∀ x y : ℝ,
    -((7 / 50 : ℚ) : ℝ) - p.2 - ((1 / 2 ^ 30 : ℚ) : ℝ) ≤ x →
    x ≤ -((7 / 50 : ℚ) : ℝ) - p.1 + ((1 / 2 ^ 30 : ℚ) : ℝ) →
    3 * (p.1 : ℝ) ≤ y → y ≤ 3 * (p.2 : ℝ) →
    (((22147 / 10000 : ℚ)) : ℝ) ≤ gHyb ⟨x, y⟩ := by
  intro p hp x y hx1 hx2 hy1 hy2
  simp only [rayBoxesH, List.mem_append, List.mem_map, List.mem_range] at hp
  rcases hp with ⟨t, ht, rfl⟩ | ⟨k, hk, rfl⟩
  · push_cast at hx1 hx2 hy1 hy2 ⊢
    exact rayA_ok t ht x y hx1 hx2 hy1 hy2
  · push_cast at hx1 hx2 hy1 hy2 ⊢
    exact rayB_ok k hk x y hx1 hx2 hy1 hy2

def aF (i : ℕ) : ℝ :=
  if i < NR then (refY i : ℝ) / (3 * 2 ^ 40) else (((bBox (i - NR)).2.2.1 : ℤ) : ℝ) / (3 * 2 ^ 40)
def bF (i : ℕ) : ℝ :=
  if i < NR then (refY (i + 1) : ℝ) / (3 * 2 ^ 40) else (((bBox (i - NR)).2.2.2 : ℤ) : ℝ) / (3 * 2 ^ 40)

theorem ray_cover_H : ∀ u : ℝ, 0 ≤ u → u ≤ ((3 / 2 : ℚ) : ℝ) →
    ∃ p ∈ rayBoxesH, (p.1 : ℝ) ≤ u ∧ u ≤ (p.2 : ℝ) := by
  intro u hu0 hu1
  have hc := cover_chain (NR + 228) aF bF 0 ((3 / 2 : ℚ) : ℝ) (by omega)
    (by
      have : refY 0 = 0 := ref_ends.1
      have hN : 0 < NR := by rw [NR_eq]; norm_num
      simp [aF, hN, this])
    (by
      have h := b_ends.2
      have h' : (9 : ℝ) * 2 ^ 40 ≤ 2 * (((bBox 227).2.2.2 : ℤ) : ℝ) := by exact_mod_cast h
      have e : NR + 228 - 1 = NR + 227 := by omega
      simp only [bF, e, lt_irrefl, if_false, show ¬ (NR + 227 < NR) by omega, Nat.add_sub_cancel_left]
      rw [le_div_iff₀ (by positivity)]
      push_cast
      norm_num
      linarith)
    (by
      intro i hi
      by_cases h1 : i + 1 < NR
      · have h0 : i < NR := by omega
        simp [aF, bF, h1, h0]
      · by_cases h2 : i < NR
        · have e : i + 1 = NR := by omega
          have hb := b_ends.1
          have hy : refY NR = (YENDR : ℤ) := ref_ends.2
          have hb' : (((bBox 0).2.2.1 : ℤ) : ℝ) ≤ ((YENDR : ℤ) : ℝ) := by exact_mod_cast hb
          simp only [aF, bF, h1, h2, if_false, if_true, e, Nat.sub_self, hy]
          exact div_le_div_of_nonneg_right hb' (by positivity)
        · have h3 : ¬ (i + 1 < NR) := h1
          have hk := List.all_eq_true.mp b_chain (i - NR) (List.mem_range.mpr (by omega))
          simp only [bChain, Bool.or_eq_true, decide_eq_true_eq] at hk
          rcases hk with hk | hk
          · omega
          · have e : i + 1 - NR = (i - NR) + 1 := by omega
            simp only [aF, bF, h1, h2, if_false, e]
            exact div_le_div_of_nonneg_right (by exact_mod_cast hk) (by positivity))
    u hu0 hu1
  obtain ⟨i, hi, h1, h2⟩ := hc
  by_cases hiN : i < NR
  · refine ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hiN, rfl⟩), ?_, ?_⟩
    · simpa [aF, hiN] using h1
    · simpa [bF, hiN] using h2
  · refine ⟨_, List.mem_append_right _ (List.mem_map.mpr ⟨i - NR, List.mem_range.mpr (by omega), rfl⟩), ?_, ?_⟩
    · simpa [aF, hiN] using h1
    · simpa [bF, hiN] using h2

end CatalanCore.Cert.SigmaHyb
