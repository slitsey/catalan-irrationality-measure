module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P03 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.017647060, 0.019607843]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P03_00 : ZCov 300000017 17000000000 23 1300 1 (1 : ℤ) (138 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 56 8 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_01 : ZCov 23 1300 13 730 5 (28 : ℤ) (-610 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 56 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_02 : ZCov 13 730 1 56 1 (3 : ℤ) (24 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 56 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_03 : ZCov 1 56 23 1280 1 (1 : ℤ) (136 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 55 8 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_04 : ZCov 23 1280 13 720 5 (28 : ℤ) (-600 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 55 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_05 : ZCov 13 720 1 55 1 (3 : ℤ) (24 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 55 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_06 : ZCov 1 55 23 1260 1 (1 : ℤ) (134 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 54 8 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_07 : ZCov 23 1260 13 710 5 (28 : ℤ) (-590 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 54 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_08 : ZCov 13 710 1 54 1 (3 : ℤ) (24 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 54 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_09 : ZCov 1 54 23 1240 1 (1 : ℤ) (132 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 53 8 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_10 : ZCov 23 1240 13 700 5 (28 : ℤ) (-580 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 53 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_11 : ZCov 13 700 18749999 1000000000 1 (3 : ℤ) (24 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 53 8 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_12 : ZCov 18749999 1000000000 3 160 10 (33 : ℤ) (80 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 8 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_13 : ZCov 3 160 18750001 1000000000 5 (18 : ℤ) (-40 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 7 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_14 : ZCov 18750001 1000000000 13 690 10 (39 : ℤ) (-240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 53 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_15 : ZCov 13 690 23 1220 10 (13 : ℤ) (1140 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 53 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_16 : ZCov 23 1220 1 53 10 (59 : ℤ) (-1300 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 53 7 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_17 : ZCov 1 53 13 680 10 (39 : ℤ) (-240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 52 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_18 : ZCov 13 680 23 1200 10 (13 : ℤ) (1120 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 52 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_19 : ZCov 23 1200 1 52 10 (59 : ℤ) (-1280 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 52 7 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_20 : ZCov 1 52 13 670 10 (39 : ℤ) (-240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 51 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_21 : ZCov 13 670 23 1180 10 (13 : ℤ) (1100 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 51 7 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P03_22 : ZCov 23 1180 1 51 10 (59 : ℤ) (-1260 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 51 7 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P03 : List ZP := [
  ⟨300000017, 17000000000, 23, 1300, 1, (1 : ℤ), (138 : ℤ), 20⟩,
  ⟨23, 1300, 13, 730, 5, (28 : ℤ), (-610 : ℤ), 100⟩,
  ⟨13, 730, 1, 56, 1, (3 : ℤ), (24 : ℤ), 20⟩,
  ⟨1, 56, 23, 1280, 1, (1 : ℤ), (136 : ℤ), 20⟩,
  ⟨23, 1280, 13, 720, 5, (28 : ℤ), (-600 : ℤ), 100⟩,
  ⟨13, 720, 1, 55, 1, (3 : ℤ), (24 : ℤ), 20⟩,
  ⟨1, 55, 23, 1260, 1, (1 : ℤ), (134 : ℤ), 20⟩,
  ⟨23, 1260, 13, 710, 5, (28 : ℤ), (-590 : ℤ), 100⟩,
  ⟨13, 710, 1, 54, 1, (3 : ℤ), (24 : ℤ), 20⟩,
  ⟨1, 54, 23, 1240, 1, (1 : ℤ), (132 : ℤ), 20⟩,
  ⟨23, 1240, 13, 700, 5, (28 : ℤ), (-580 : ℤ), 100⟩,
  ⟨13, 700, 18749999, 1000000000, 1, (3 : ℤ), (24 : ℤ), 20⟩,
  ⟨18749999, 1000000000, 3, 160, 10, (33 : ℤ), (80 : ℤ), 200⟩,
  ⟨3, 160, 18750001, 1000000000, 5, (18 : ℤ), (-40 : ℤ), 100⟩,
  ⟨18750001, 1000000000, 13, 690, 10, (39 : ℤ), (-240 : ℤ), 200⟩,
  ⟨13, 690, 23, 1220, 10, (13 : ℤ), (1140 : ℤ), 200⟩,
  ⟨23, 1220, 1, 53, 10, (59 : ℤ), (-1300 : ℤ), 200⟩,
  ⟨1, 53, 13, 680, 10, (39 : ℤ), (-240 : ℤ), 200⟩,
  ⟨13, 680, 23, 1200, 10, (13 : ℤ), (1120 : ℤ), 200⟩,
  ⟨23, 1200, 1, 52, 10, (59 : ℤ), (-1280 : ℤ), 200⟩,
  ⟨1, 52, 13, 670, 10, (39 : ℤ), (-240 : ℤ), 200⟩,
  ⟨13, 670, 23, 1180, 10, (13 : ℤ), (1100 : ℤ), 200⟩,
  ⟨23, 1180, 1, 51, 10, (59 : ℤ), (-1260 : ℤ), 200⟩]

theorem zL_P03_cov : ZAllCov zL_P03 :=
  ⟨zp_P03_00, zp_P03_01, zp_P03_02, zp_P03_03, zp_P03_04, zp_P03_05, zp_P03_06, zp_P03_07, zp_P03_08, zp_P03_09, zp_P03_10, zp_P03_11, zp_P03_12, zp_P03_13, zp_P03_14, zp_P03_15, zp_P03_16, zp_P03_17, zp_P03_18, zp_P03_19, zp_P03_20, zp_P03_21, zp_P03_22, trivial⟩

theorem zL_P03_chain : zChain (300000017 / 17000000000 : ℚ) zL_P03 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P03_end : zEnd (300000017 / 17000000000 : ℚ) zL_P03 = (1 / 51 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P03_mass : zMass zL_P03 ≤ (6746352057017 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
