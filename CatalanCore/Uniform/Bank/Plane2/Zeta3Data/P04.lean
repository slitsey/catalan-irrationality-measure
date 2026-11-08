module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P04 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.019607843, 0.022033898]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P04_00 : ZCov 1 51 13 660 10 (39 : ℤ) (-240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 50 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_01 : ZCov 13 660 23 1160 10 (13 : ℤ) (1080 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 50 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_02 : ZCov 23 1160 19999999 1000000000 10 (59 : ℤ) (-1240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 50 7 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_03 : ZCov 19999999 1000000000 1 50 5 (18 : ℤ) (-40 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 7 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_04 : ZCov 1 50 20000001 1000000000 10 (33 : ℤ) (70 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 7 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_05 : ZCov 20000001 1000000000 23 1140 1 (1 : ℤ) (121 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 49 7 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_06 : ZCov 23 1140 13 640 5 (28 : ℤ) (-535 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 49 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_07 : ZCov 13 640 1 49 1 (3 : ℤ) (21 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 49 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_08 : ZCov 1 49 23 1120 1 (1 : ℤ) (119 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 48 7 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_09 : ZCov 23 1120 13 630 5 (28 : ℤ) (-525 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 48 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_10 : ZCov 13 630 1 48 1 (3 : ℤ) (21 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 48 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_11 : ZCov 1 48 23 1100 1 (1 : ℤ) (117 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 47 7 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_12 : ZCov 23 1100 13 620 5 (28 : ℤ) (-515 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 47 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_13 : ZCov 13 620 1 47 1 (3 : ℤ) (21 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 47 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_14 : ZCov 1 47 23 1080 1 (1 : ℤ) (115 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 46 7 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_15 : ZCov 23 1080 13 610 5 (28 : ℤ) (-505 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 46 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_16 : ZCov 13 610 149999993 7000000000 1 (3 : ℤ) (21 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 46 7 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_17 : ZCov 149999993 7000000000 3 140 10 (33 : ℤ) (70 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 7 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_18 : ZCov 3 140 150000007 7000000000 5 (18 : ℤ) (-35 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 6 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_19 : ZCov 150000007 7000000000 13 600 10 (39 : ℤ) (-210 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 46 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_20 : ZCov 13 600 23 1060 10 (13 : ℤ) (990 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 46 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_21 : ZCov 23 1060 1 46 10 (59 : ℤ) (-1130 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 46 6 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P04_22 : ZCov 1 46 13 590 10 (39 : ℤ) (-210 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 45 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P04 : List ZP := [
  ⟨1, 51, 13, 660, 10, (39 : ℤ), (-240 : ℤ), 200⟩,
  ⟨13, 660, 23, 1160, 10, (13 : ℤ), (1080 : ℤ), 200⟩,
  ⟨23, 1160, 19999999, 1000000000, 10, (59 : ℤ), (-1240 : ℤ), 200⟩,
  ⟨19999999, 1000000000, 1, 50, 5, (18 : ℤ), (-40 : ℤ), 100⟩,
  ⟨1, 50, 20000001, 1000000000, 10, (33 : ℤ), (70 : ℤ), 200⟩,
  ⟨20000001, 1000000000, 23, 1140, 1, (1 : ℤ), (121 : ℤ), 20⟩,
  ⟨23, 1140, 13, 640, 5, (28 : ℤ), (-535 : ℤ), 100⟩,
  ⟨13, 640, 1, 49, 1, (3 : ℤ), (21 : ℤ), 20⟩,
  ⟨1, 49, 23, 1120, 1, (1 : ℤ), (119 : ℤ), 20⟩,
  ⟨23, 1120, 13, 630, 5, (28 : ℤ), (-525 : ℤ), 100⟩,
  ⟨13, 630, 1, 48, 1, (3 : ℤ), (21 : ℤ), 20⟩,
  ⟨1, 48, 23, 1100, 1, (1 : ℤ), (117 : ℤ), 20⟩,
  ⟨23, 1100, 13, 620, 5, (28 : ℤ), (-515 : ℤ), 100⟩,
  ⟨13, 620, 1, 47, 1, (3 : ℤ), (21 : ℤ), 20⟩,
  ⟨1, 47, 23, 1080, 1, (1 : ℤ), (115 : ℤ), 20⟩,
  ⟨23, 1080, 13, 610, 5, (28 : ℤ), (-505 : ℤ), 100⟩,
  ⟨13, 610, 149999993, 7000000000, 1, (3 : ℤ), (21 : ℤ), 20⟩,
  ⟨149999993, 7000000000, 3, 140, 10, (33 : ℤ), (70 : ℤ), 200⟩,
  ⟨3, 140, 150000007, 7000000000, 5, (18 : ℤ), (-35 : ℤ), 100⟩,
  ⟨150000007, 7000000000, 13, 600, 10, (39 : ℤ), (-210 : ℤ), 200⟩,
  ⟨13, 600, 23, 1060, 10, (13 : ℤ), (990 : ℤ), 200⟩,
  ⟨23, 1060, 1, 46, 10, (59 : ℤ), (-1130 : ℤ), 200⟩,
  ⟨1, 46, 13, 590, 10, (39 : ℤ), (-210 : ℤ), 200⟩]

theorem zL_P04_cov : ZAllCov zL_P04 :=
  ⟨zp_P04_00, zp_P04_01, zp_P04_02, zp_P04_03, zp_P04_04, zp_P04_05, zp_P04_06, zp_P04_07, zp_P04_08, zp_P04_09, zp_P04_10, zp_P04_11, zp_P04_12, zp_P04_13, zp_P04_14, zp_P04_15, zp_P04_16, zp_P04_17, zp_P04_18, zp_P04_19, zp_P04_20, zp_P04_21, zp_P04_22, trivial⟩

theorem zL_P04_chain : zChain (1 / 51 : ℚ) zL_P04 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P04_end : zEnd (1 / 51 : ℚ) zL_P04 = (13 / 590 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P04_mass : zMass zL_P04 ≤ (4171061844817 / 500000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
