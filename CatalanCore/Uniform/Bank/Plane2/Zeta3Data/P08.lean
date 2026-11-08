module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P08 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.035135135, 0.042857144]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P08_00 : ZCov 13 370 1 28 1 (3 : ℤ) (12 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 28 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_01 : ZCov 1 28 23 640 1 (1 : ℤ) (68 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 27 4 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_02 : ZCov 23 640 13 360 5 (28 : ℤ) (-300 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 27 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_03 : ZCov 13 360 1 27 1 (3 : ℤ) (12 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 27 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_04 : ZCov 1 27 23 620 1 (1 : ℤ) (66 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 26 4 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_05 : ZCov 23 620 13 350 5 (28 : ℤ) (-290 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 26 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_06 : ZCov 13 350 37499999 1000000000 1 (3 : ℤ) (12 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 26 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_07 : ZCov 37499999 1000000000 3 80 10 (33 : ℤ) (40 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 4 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_08 : ZCov 3 80 37500001 1000000000 5 (18 : ℤ) (-20 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 3 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_09 : ZCov 37500001 1000000000 13 340 10 (39 : ℤ) (-120 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 26 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_10 : ZCov 13 340 23 600 10 (13 : ℤ) (560 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 26 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_11 : ZCov 23 600 1 26 10 (59 : ℤ) (-640 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 26 3 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_12 : ZCov 1 26 13 330 10 (39 : ℤ) (-120 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 25 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_13 : ZCov 13 330 23 580 10 (13 : ℤ) (540 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 25 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_14 : ZCov 23 580 1 25 10 (59 : ℤ) (-620 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 25 3 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_15 : ZCov 1 25 13 320 10 (39 : ℤ) (-120 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 24 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_16 : ZCov 13 320 23 560 10 (13 : ℤ) (520 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 24 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_17 : ZCov 23 560 1 24 10 (59 : ℤ) (-600 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 24 3 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_18 : ZCov 1 24 13 310 10 (39 : ℤ) (-120 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 23 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_19 : ZCov 13 310 23 540 10 (13 : ℤ) (500 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 23 3 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_20 : ZCov 23 540 299999993 7000000000 10 (59 : ℤ) (-580 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 23 3 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_21 : ZCov 299999993 7000000000 3 70 5 (18 : ℤ) (-20 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 3 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P08_22 : ZCov 3 70 300000007 7000000000 10 (33 : ℤ) (30 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 3 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

def zL_P08 : List ZP := [
  ⟨13, 370, 1, 28, 1, (3 : ℤ), (12 : ℤ), 20⟩,
  ⟨1, 28, 23, 640, 1, (1 : ℤ), (68 : ℤ), 20⟩,
  ⟨23, 640, 13, 360, 5, (28 : ℤ), (-300 : ℤ), 100⟩,
  ⟨13, 360, 1, 27, 1, (3 : ℤ), (12 : ℤ), 20⟩,
  ⟨1, 27, 23, 620, 1, (1 : ℤ), (66 : ℤ), 20⟩,
  ⟨23, 620, 13, 350, 5, (28 : ℤ), (-290 : ℤ), 100⟩,
  ⟨13, 350, 37499999, 1000000000, 1, (3 : ℤ), (12 : ℤ), 20⟩,
  ⟨37499999, 1000000000, 3, 80, 10, (33 : ℤ), (40 : ℤ), 200⟩,
  ⟨3, 80, 37500001, 1000000000, 5, (18 : ℤ), (-20 : ℤ), 100⟩,
  ⟨37500001, 1000000000, 13, 340, 10, (39 : ℤ), (-120 : ℤ), 200⟩,
  ⟨13, 340, 23, 600, 10, (13 : ℤ), (560 : ℤ), 200⟩,
  ⟨23, 600, 1, 26, 10, (59 : ℤ), (-640 : ℤ), 200⟩,
  ⟨1, 26, 13, 330, 10, (39 : ℤ), (-120 : ℤ), 200⟩,
  ⟨13, 330, 23, 580, 10, (13 : ℤ), (540 : ℤ), 200⟩,
  ⟨23, 580, 1, 25, 10, (59 : ℤ), (-620 : ℤ), 200⟩,
  ⟨1, 25, 13, 320, 10, (39 : ℤ), (-120 : ℤ), 200⟩,
  ⟨13, 320, 23, 560, 10, (13 : ℤ), (520 : ℤ), 200⟩,
  ⟨23, 560, 1, 24, 10, (59 : ℤ), (-600 : ℤ), 200⟩,
  ⟨1, 24, 13, 310, 10, (39 : ℤ), (-120 : ℤ), 200⟩,
  ⟨13, 310, 23, 540, 10, (13 : ℤ), (500 : ℤ), 200⟩,
  ⟨23, 540, 299999993, 7000000000, 10, (59 : ℤ), (-580 : ℤ), 200⟩,
  ⟨299999993, 7000000000, 3, 70, 5, (18 : ℤ), (-20 : ℤ), 100⟩,
  ⟨3, 70, 300000007, 7000000000, 10, (33 : ℤ), (30 : ℤ), 200⟩]

theorem zL_P08_cov : ZAllCov zL_P08 :=
  ⟨zp_P08_00, zp_P08_01, zp_P08_02, zp_P08_03, zp_P08_04, zp_P08_05, zp_P08_06, zp_P08_07, zp_P08_08, zp_P08_09, zp_P08_10, zp_P08_11, zp_P08_12, zp_P08_13, zp_P08_14, zp_P08_15, zp_P08_16, zp_P08_17, zp_P08_18, zp_P08_19, zp_P08_20, zp_P08_21, zp_P08_22, trivial⟩

theorem zL_P08_chain : zChain (13 / 370 : ℚ) zL_P08 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P08_end : zEnd (13 / 370 : ℚ) zL_P08 = (300000007 / 7000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P08_mass : zMass zL_P08 ≤ (26481245112567 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
