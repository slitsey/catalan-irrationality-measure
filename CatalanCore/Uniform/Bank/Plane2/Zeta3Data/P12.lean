module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P12 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.162500000, 1.300000001]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P12_00 : ZCov 13 80 23 140 10 (13 : ℤ) (130 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 6 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_01 : ZCov 23 140 1 6 10 (59 : ℤ) (-150 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 6 0 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_02 : ZCov 1 6 13 70 10 (39 : ℤ) (-30 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 5 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_03 : ZCov 13 70 23 120 10 (13 : ℤ) (110 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 5 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_04 : ZCov 23 120 1 5 10 (59 : ℤ) (-130 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 5 0 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_05 : ZCov 1 5 13 60 10 (39 : ℤ) (-30 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 4 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_06 : ZCov 13 60 23 100 10 (13 : ℤ) (90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 4 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_07 : ZCov 23 100 1 4 10 (59 : ℤ) (-110 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 4 0 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_08 : ZCov 1 4 13 50 10 (39 : ℤ) (-30 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 3 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_09 : ZCov 13 50 23 80 10 (13 : ℤ) (70 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 3 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_10 : ZCov 23 80 299999999 1000000000 10 (59 : ℤ) (-90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 3 0 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_11 : ZCov 299999999 1000000000 3 10 5 (18 : ℤ) (-5 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 0 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_12 : ZCov 3 10 300000001 1000000000 10 (33 : ℤ) (0 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 0 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_13 : ZCov 300000001 1000000000 13 40 5 (28 : ℤ) (-40 : ℤ) 100 :=
  zc_E1 (by norm_num) (by norm_num) 3 0 0 2 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_14 : ZCov 13 40 1 3 1 (3 : ℤ) (0 : ℤ) 20 :=
  zc_E1 (by norm_num) (by norm_num) 3 0 0 2 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_15 : ZCov 1 3 23 60 1 (1 : ℤ) (6 : ℤ) 20 :=
  zc_E1 (by norm_num) (by norm_num) 2 2 2 0 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_16 : ZCov 23 60 13 30 5 (28 : ℤ) (-30 : ℤ) 100 :=
  zc_E1 (by norm_num) (by norm_num) 2 0 0 2 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_17 : ZCov 13 30 1 2 1 (3 : ℤ) (0 : ℤ) 20 :=
  zc_E1 (by norm_num) (by norm_num) 2 0 0 2 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_18 : ZCov 1 2 23 40 1 (1 : ℤ) (4 : ℤ) 20 :=
  zc_E1 (by norm_num) (by norm_num) 1 2 2 0 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_19 : ZCov 23 40 13 20 5 (28 : ℤ) (-20 : ℤ) 100 :=
  zc_E1 (by norm_num) (by norm_num) 1 0 0 2 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_20 : ZCov 13 20 1 1 10 (69 : ℤ) (-60 : ℤ) 200 :=
  zc_B2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h hpr; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_21 : ZCov 1 1 13 10 10 (39 : ℤ) (-30 : ℤ) 200 :=
  zc_B4 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h hpr; simp only [ZH, ZR0] at h; omega)

theorem zp_P12_22 : ZCov 13 10 1300000001 1000000000 1 (0 : ℤ) (0 : ℤ) 20 :=
  zc_B4 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h hpr; simp only [ZH, ZR0] at h; omega)

def zL_P12 : List ZP := [
  ⟨13, 80, 23, 140, 10, (13 : ℤ), (130 : ℤ), 200⟩,
  ⟨23, 140, 1, 6, 10, (59 : ℤ), (-150 : ℤ), 200⟩,
  ⟨1, 6, 13, 70, 10, (39 : ℤ), (-30 : ℤ), 200⟩,
  ⟨13, 70, 23, 120, 10, (13 : ℤ), (110 : ℤ), 200⟩,
  ⟨23, 120, 1, 5, 10, (59 : ℤ), (-130 : ℤ), 200⟩,
  ⟨1, 5, 13, 60, 10, (39 : ℤ), (-30 : ℤ), 200⟩,
  ⟨13, 60, 23, 100, 10, (13 : ℤ), (90 : ℤ), 200⟩,
  ⟨23, 100, 1, 4, 10, (59 : ℤ), (-110 : ℤ), 200⟩,
  ⟨1, 4, 13, 50, 10, (39 : ℤ), (-30 : ℤ), 200⟩,
  ⟨13, 50, 23, 80, 10, (13 : ℤ), (70 : ℤ), 200⟩,
  ⟨23, 80, 299999999, 1000000000, 10, (59 : ℤ), (-90 : ℤ), 200⟩,
  ⟨299999999, 1000000000, 3, 10, 5, (18 : ℤ), (-5 : ℤ), 100⟩,
  ⟨3, 10, 300000001, 1000000000, 10, (33 : ℤ), (0 : ℤ), 200⟩,
  ⟨300000001, 1000000000, 13, 40, 5, (28 : ℤ), (-40 : ℤ), 100⟩,
  ⟨13, 40, 1, 3, 1, (3 : ℤ), (0 : ℤ), 20⟩,
  ⟨1, 3, 23, 60, 1, (1 : ℤ), (6 : ℤ), 20⟩,
  ⟨23, 60, 13, 30, 5, (28 : ℤ), (-30 : ℤ), 100⟩,
  ⟨13, 30, 1, 2, 1, (3 : ℤ), (0 : ℤ), 20⟩,
  ⟨1, 2, 23, 40, 1, (1 : ℤ), (4 : ℤ), 20⟩,
  ⟨23, 40, 13, 20, 5, (28 : ℤ), (-20 : ℤ), 100⟩,
  ⟨13, 20, 1, 1, 10, (69 : ℤ), (-60 : ℤ), 200⟩,
  ⟨1, 1, 13, 10, 10, (39 : ℤ), (-30 : ℤ), 200⟩,
  ⟨13, 10, 1300000001, 1000000000, 1, (0 : ℤ), (0 : ℤ), 20⟩]

theorem zL_P12_cov : ZAllCov zL_P12 :=
  ⟨zp_P12_00, zp_P12_01, zp_P12_02, zp_P12_03, zp_P12_04, zp_P12_05, zp_P12_06, zp_P12_07, zp_P12_08, zp_P12_09, zp_P12_10, zp_P12_11, zp_P12_12, zp_P12_13, zp_P12_14, zp_P12_15, zp_P12_16, zp_P12_17, zp_P12_18, zp_P12_19, zp_P12_20, zp_P12_21, zp_P12_22, trivial⟩

theorem zL_P12_chain : zChain (13 / 80 : ℚ) zL_P12 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P12_end : zEnd (13 / 80 : ℚ) zL_P12 = (1300000001 / 1000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P12_mass : zMass zL_P12 ≤ (2358430803771429 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
