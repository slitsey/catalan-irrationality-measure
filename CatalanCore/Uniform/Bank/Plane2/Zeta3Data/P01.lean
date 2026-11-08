module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P01 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.006000000, 0.011111111]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P01_00 : ZCov 3 500 3 490 5 (18 : ℤ) (-125 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 24 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_01 : ZCov 3 490 1 160 10 (33 : ℤ) (240 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 24 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_02 : ZCov 1 160 3 470 5 (18 : ℤ) (-120 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 23 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_03 : ZCov 3 470 3 460 10 (33 : ℤ) (230 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 23 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_04 : ZCov 3 460 1 150 5 (18 : ℤ) (-115 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 22 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_05 : ZCov 1 150 3 440 10 (33 : ℤ) (220 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 22 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_06 : ZCov 3 440 3 430 5 (18 : ℤ) (-110 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 21 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_07 : ZCov 3 430 1 140 10 (33 : ℤ) (210 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 21 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_08 : ZCov 1 140 3 410 5 (18 : ℤ) (-105 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 20 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_09 : ZCov 3 410 3 400 10 (33 : ℤ) (200 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 20 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_10 : ZCov 3 400 1 130 5 (18 : ℤ) (-100 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 19 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_11 : ZCov 1 130 3 380 10 (33 : ℤ) (190 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 19 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_12 : ZCov 3 380 3 370 5 (18 : ℤ) (-95 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 18 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_13 : ZCov 3 370 1 120 10 (33 : ℤ) (180 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 18 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_14 : ZCov 1 120 3 350 5 (18 : ℤ) (-90 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 17 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_15 : ZCov 3 350 3 340 10 (33 : ℤ) (170 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 17 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_16 : ZCov 3 340 1 110 5 (18 : ℤ) (-85 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 16 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_17 : ZCov 1 110 3 320 10 (33 : ℤ) (160 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 16 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_18 : ZCov 3 320 3 310 5 (18 : ℤ) (-80 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 15 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_19 : ZCov 3 310 1 100 10 (33 : ℤ) (150 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 15 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_20 : ZCov 1 100 3 290 5 (18 : ℤ) (-75 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 14 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_21 : ZCov 3 290 3 280 10 (33 : ℤ) (140 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 14 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P01_22 : ZCov 3 280 1 90 5 (18 : ℤ) (-70 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 13 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

def zL_P01 : List ZP := [
  ⟨3, 500, 3, 490, 5, (18 : ℤ), (-125 : ℤ), 100⟩,
  ⟨3, 490, 1, 160, 10, (33 : ℤ), (240 : ℤ), 200⟩,
  ⟨1, 160, 3, 470, 5, (18 : ℤ), (-120 : ℤ), 100⟩,
  ⟨3, 470, 3, 460, 10, (33 : ℤ), (230 : ℤ), 200⟩,
  ⟨3, 460, 1, 150, 5, (18 : ℤ), (-115 : ℤ), 100⟩,
  ⟨1, 150, 3, 440, 10, (33 : ℤ), (220 : ℤ), 200⟩,
  ⟨3, 440, 3, 430, 5, (18 : ℤ), (-110 : ℤ), 100⟩,
  ⟨3, 430, 1, 140, 10, (33 : ℤ), (210 : ℤ), 200⟩,
  ⟨1, 140, 3, 410, 5, (18 : ℤ), (-105 : ℤ), 100⟩,
  ⟨3, 410, 3, 400, 10, (33 : ℤ), (200 : ℤ), 200⟩,
  ⟨3, 400, 1, 130, 5, (18 : ℤ), (-100 : ℤ), 100⟩,
  ⟨1, 130, 3, 380, 10, (33 : ℤ), (190 : ℤ), 200⟩,
  ⟨3, 380, 3, 370, 5, (18 : ℤ), (-95 : ℤ), 100⟩,
  ⟨3, 370, 1, 120, 10, (33 : ℤ), (180 : ℤ), 200⟩,
  ⟨1, 120, 3, 350, 5, (18 : ℤ), (-90 : ℤ), 100⟩,
  ⟨3, 350, 3, 340, 10, (33 : ℤ), (170 : ℤ), 200⟩,
  ⟨3, 340, 1, 110, 5, (18 : ℤ), (-85 : ℤ), 100⟩,
  ⟨1, 110, 3, 320, 10, (33 : ℤ), (160 : ℤ), 200⟩,
  ⟨3, 320, 3, 310, 5, (18 : ℤ), (-80 : ℤ), 100⟩,
  ⟨3, 310, 1, 100, 10, (33 : ℤ), (150 : ℤ), 200⟩,
  ⟨1, 100, 3, 290, 5, (18 : ℤ), (-75 : ℤ), 100⟩,
  ⟨3, 290, 3, 280, 10, (33 : ℤ), (140 : ℤ), 200⟩,
  ⟨3, 280, 1, 90, 5, (18 : ℤ), (-70 : ℤ), 100⟩]

theorem zL_P01_cov : ZAllCov zL_P01 :=
  ⟨zp_P01_00, zp_P01_01, zp_P01_02, zp_P01_03, zp_P01_04, zp_P01_05, zp_P01_06, zp_P01_07, zp_P01_08, zp_P01_09, zp_P01_10, zp_P01_11, zp_P01_12, zp_P01_13, zp_P01_14, zp_P01_15, zp_P01_16, zp_P01_17, zp_P01_18, zp_P01_19, zp_P01_20, zp_P01_21, zp_P01_22, trivial⟩

theorem zL_P01_chain : zChain (3 / 500 : ℚ) zL_P01 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P01_end : zEnd (3 / 500 : ℚ) zL_P01 = (1 / 90 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P01_mass : zMass zL_P01 ≤ (1101399361233 / 62500000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
