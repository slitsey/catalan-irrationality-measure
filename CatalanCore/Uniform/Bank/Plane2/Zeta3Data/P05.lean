module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P05 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.022033898, 0.025000001]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P05_00 : ZCov 13 590 23 1040 10 (13 : ℤ) (970 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 45 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_01 : ZCov 23 1040 1 45 10 (59 : ℤ) (-1110 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 45 6 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_02 : ZCov 1 45 13 580 10 (39 : ℤ) (-210 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 44 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_03 : ZCov 13 580 23 1020 10 (13 : ℤ) (950 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 44 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_04 : ZCov 23 1020 1 44 10 (59 : ℤ) (-1090 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 44 6 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_05 : ZCov 1 44 13 570 10 (39 : ℤ) (-210 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 43 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_06 : ZCov 13 570 23 1000 10 (13 : ℤ) (930 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 43 6 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_07 : ZCov 23 1000 299999987 13000000000 10 (59 : ℤ) (-1070 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 43 6 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_08 : ZCov 299999987 13000000000 3 130 5 (18 : ℤ) (-35 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 6 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_09 : ZCov 3 130 300000013 13000000000 10 (33 : ℤ) (60 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 6 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_10 : ZCov 300000013 13000000000 13 560 5 (28 : ℤ) (-470 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 43 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_11 : ZCov 13 560 1 43 1 (3 : ℤ) (18 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 43 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_12 : ZCov 1 43 23 980 1 (1 : ℤ) (104 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 42 6 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_13 : ZCov 23 980 13 550 5 (28 : ℤ) (-460 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 42 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_14 : ZCov 13 550 1 42 1 (3 : ℤ) (18 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 42 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_15 : ZCov 1 42 23 960 1 (1 : ℤ) (102 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 41 6 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_16 : ZCov 23 960 13 540 5 (28 : ℤ) (-450 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 41 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_17 : ZCov 13 540 1 41 1 (3 : ℤ) (18 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 41 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_18 : ZCov 1 41 23 940 1 (1 : ℤ) (100 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 40 6 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_19 : ZCov 23 940 13 530 5 (28 : ℤ) (-440 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 40 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_20 : ZCov 13 530 24999999 1000000000 1 (3 : ℤ) (18 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 40 6 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_21 : ZCov 24999999 1000000000 1 40 10 (33 : ℤ) (60 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 6 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P05_22 : ZCov 1 40 25000001 1000000000 5 (18 : ℤ) (-30 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 5 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

def zL_P05 : List ZP := [
  ⟨13, 590, 23, 1040, 10, (13 : ℤ), (970 : ℤ), 200⟩,
  ⟨23, 1040, 1, 45, 10, (59 : ℤ), (-1110 : ℤ), 200⟩,
  ⟨1, 45, 13, 580, 10, (39 : ℤ), (-210 : ℤ), 200⟩,
  ⟨13, 580, 23, 1020, 10, (13 : ℤ), (950 : ℤ), 200⟩,
  ⟨23, 1020, 1, 44, 10, (59 : ℤ), (-1090 : ℤ), 200⟩,
  ⟨1, 44, 13, 570, 10, (39 : ℤ), (-210 : ℤ), 200⟩,
  ⟨13, 570, 23, 1000, 10, (13 : ℤ), (930 : ℤ), 200⟩,
  ⟨23, 1000, 299999987, 13000000000, 10, (59 : ℤ), (-1070 : ℤ), 200⟩,
  ⟨299999987, 13000000000, 3, 130, 5, (18 : ℤ), (-35 : ℤ), 100⟩,
  ⟨3, 130, 300000013, 13000000000, 10, (33 : ℤ), (60 : ℤ), 200⟩,
  ⟨300000013, 13000000000, 13, 560, 5, (28 : ℤ), (-470 : ℤ), 100⟩,
  ⟨13, 560, 1, 43, 1, (3 : ℤ), (18 : ℤ), 20⟩,
  ⟨1, 43, 23, 980, 1, (1 : ℤ), (104 : ℤ), 20⟩,
  ⟨23, 980, 13, 550, 5, (28 : ℤ), (-460 : ℤ), 100⟩,
  ⟨13, 550, 1, 42, 1, (3 : ℤ), (18 : ℤ), 20⟩,
  ⟨1, 42, 23, 960, 1, (1 : ℤ), (102 : ℤ), 20⟩,
  ⟨23, 960, 13, 540, 5, (28 : ℤ), (-450 : ℤ), 100⟩,
  ⟨13, 540, 1, 41, 1, (3 : ℤ), (18 : ℤ), 20⟩,
  ⟨1, 41, 23, 940, 1, (1 : ℤ), (100 : ℤ), 20⟩,
  ⟨23, 940, 13, 530, 5, (28 : ℤ), (-440 : ℤ), 100⟩,
  ⟨13, 530, 24999999, 1000000000, 1, (3 : ℤ), (18 : ℤ), 20⟩,
  ⟨24999999, 1000000000, 1, 40, 10, (33 : ℤ), (60 : ℤ), 200⟩,
  ⟨1, 40, 25000001, 1000000000, 5, (18 : ℤ), (-30 : ℤ), 100⟩]

theorem zL_P05_cov : ZAllCov zL_P05 :=
  ⟨zp_P05_00, zp_P05_01, zp_P05_02, zp_P05_03, zp_P05_04, zp_P05_05, zp_P05_06, zp_P05_07, zp_P05_08, zp_P05_09, zp_P05_10, zp_P05_11, zp_P05_12, zp_P05_13, zp_P05_14, zp_P05_15, zp_P05_16, zp_P05_17, zp_P05_18, zp_P05_19, zp_P05_20, zp_P05_21, zp_P05_22, trivial⟩

theorem zL_P05_chain : zChain (13 / 590 : ℚ) zL_P05 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P05_end : zEnd (13 / 590 : ℚ) zL_P05 = (25000001 / 1000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P05_mass : zMass zL_P05 ≤ (5094329408031 / 500000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
