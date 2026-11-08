module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P02 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.011111111, 0.017647060]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P02_00 : ZCov 1 90 3 260 10 (33 : ℤ) (130 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 13 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_01 : ZCov 3 260 3 250 5 (18 : ℤ) (-65 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 12 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_02 : ZCov 3 250 1 80 10 (33 : ℤ) (120 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 12 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_03 : ZCov 1 80 3 230 5 (18 : ℤ) (-60 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 11 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_04 : ZCov 3 230 3 220 10 (33 : ℤ) (110 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 11 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_05 : ZCov 3 220 1 70 5 (18 : ℤ) (-55 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 10 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_06 : ZCov 1 70 3 200 10 (33 : ℤ) (100 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 10 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_07 : ZCov 3 200 3 190 5 (18 : ℤ) (-50 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 9 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_08 : ZCov 3 190 1 60 10 (33 : ℤ) (90 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 9 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_09 : ZCov 1 60 50000003 3000000000 5 (18 : ℤ) (-45 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 8 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_10 : ZCov 50000003 3000000000 13 770 10 (39 : ℤ) (-270 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 59 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_11 : ZCov 13 770 23 1360 10 (13 : ℤ) (1270 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 59 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_12 : ZCov 23 1360 1 59 10 (59 : ℤ) (-1450 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 59 8 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_13 : ZCov 1 59 13 760 10 (39 : ℤ) (-270 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 58 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_14 : ZCov 13 760 23 1340 10 (13 : ℤ) (1250 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 58 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_15 : ZCov 23 1340 1 58 10 (59 : ℤ) (-1430 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 58 8 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_16 : ZCov 1 58 13 750 10 (39 : ℤ) (-270 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 57 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_17 : ZCov 13 750 23 1320 10 (13 : ℤ) (1230 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 57 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_18 : ZCov 23 1320 1 57 10 (59 : ℤ) (-1410 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 57 8 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_19 : ZCov 1 57 13 740 10 (39 : ℤ) (-270 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 56 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_20 : ZCov 13 740 299999983 17000000000 10 (13 : ℤ) (1210 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 56 8 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_21 : ZCov 299999983 17000000000 3 170 5 (18 : ℤ) (-45 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 8 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P02_22 : ZCov 3 170 300000017 17000000000 10 (33 : ℤ) (80 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 8 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

def zL_P02 : List ZP := [
  ⟨1, 90, 3, 260, 10, (33 : ℤ), (130 : ℤ), 200⟩,
  ⟨3, 260, 3, 250, 5, (18 : ℤ), (-65 : ℤ), 100⟩,
  ⟨3, 250, 1, 80, 10, (33 : ℤ), (120 : ℤ), 200⟩,
  ⟨1, 80, 3, 230, 5, (18 : ℤ), (-60 : ℤ), 100⟩,
  ⟨3, 230, 3, 220, 10, (33 : ℤ), (110 : ℤ), 200⟩,
  ⟨3, 220, 1, 70, 5, (18 : ℤ), (-55 : ℤ), 100⟩,
  ⟨1, 70, 3, 200, 10, (33 : ℤ), (100 : ℤ), 200⟩,
  ⟨3, 200, 3, 190, 5, (18 : ℤ), (-50 : ℤ), 100⟩,
  ⟨3, 190, 1, 60, 10, (33 : ℤ), (90 : ℤ), 200⟩,
  ⟨1, 60, 50000003, 3000000000, 5, (18 : ℤ), (-45 : ℤ), 100⟩,
  ⟨50000003, 3000000000, 13, 770, 10, (39 : ℤ), (-270 : ℤ), 200⟩,
  ⟨13, 770, 23, 1360, 10, (13 : ℤ), (1270 : ℤ), 200⟩,
  ⟨23, 1360, 1, 59, 10, (59 : ℤ), (-1450 : ℤ), 200⟩,
  ⟨1, 59, 13, 760, 10, (39 : ℤ), (-270 : ℤ), 200⟩,
  ⟨13, 760, 23, 1340, 10, (13 : ℤ), (1250 : ℤ), 200⟩,
  ⟨23, 1340, 1, 58, 10, (59 : ℤ), (-1430 : ℤ), 200⟩,
  ⟨1, 58, 13, 750, 10, (39 : ℤ), (-270 : ℤ), 200⟩,
  ⟨13, 750, 23, 1320, 10, (13 : ℤ), (1230 : ℤ), 200⟩,
  ⟨23, 1320, 1, 57, 10, (59 : ℤ), (-1410 : ℤ), 200⟩,
  ⟨1, 57, 13, 740, 10, (39 : ℤ), (-270 : ℤ), 200⟩,
  ⟨13, 740, 299999983, 17000000000, 10, (13 : ℤ), (1210 : ℤ), 200⟩,
  ⟨299999983, 17000000000, 3, 170, 5, (18 : ℤ), (-45 : ℤ), 100⟩,
  ⟨3, 170, 300000017, 17000000000, 10, (33 : ℤ), (80 : ℤ), 200⟩]

theorem zL_P02_cov : ZAllCov zL_P02 :=
  ⟨zp_P02_00, zp_P02_01, zp_P02_02, zp_P02_03, zp_P02_04, zp_P02_05, zp_P02_06, zp_P02_07, zp_P02_08, zp_P02_09, zp_P02_10, zp_P02_11, zp_P02_12, zp_P02_13, zp_P02_14, zp_P02_15, zp_P02_16, zp_P02_17, zp_P02_18, zp_P02_19, zp_P02_20, zp_P02_21, zp_P02_22, trivial⟩

theorem zL_P02_chain : zChain (1 / 90 : ℚ) zL_P02 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P02_end : zEnd (1 / 90 : ℚ) zL_P02 = (300000017 / 17000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P02_mass : zMass zL_P02 ≤ (11259739555071 / 500000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
