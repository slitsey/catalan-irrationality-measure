module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P10 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.059090909, 0.083333333]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P10_00 : ZCov 13 220 59999999 1000000000 10 (13 : ℤ) (350 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 16 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_01 : ZCov 59999999 1000000000 3 50 5 (18 : ℤ) (-15 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 2 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_02 : ZCov 3 50 60000001 1000000000 10 (33 : ℤ) (20 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 2 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_03 : ZCov 60000001 1000000000 23 380 1 (1 : ℤ) (40 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 16 2 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_04 : ZCov 23 380 13 210 5 (28 : ℤ) (-180 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 16 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_05 : ZCov 13 210 1 16 1 (3 : ℤ) (6 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 16 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_06 : ZCov 1 16 23 360 1 (1 : ℤ) (38 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 15 2 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_07 : ZCov 23 360 13 200 5 (28 : ℤ) (-170 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 15 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_08 : ZCov 13 200 1 15 1 (3 : ℤ) (6 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 15 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_09 : ZCov 1 15 23 340 1 (1 : ℤ) (36 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 14 2 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_10 : ZCov 23 340 13 190 5 (28 : ℤ) (-160 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 14 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_11 : ZCov 13 190 1 14 1 (3 : ℤ) (6 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 14 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_12 : ZCov 1 14 23 320 1 (1 : ℤ) (34 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 13 2 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_13 : ZCov 23 320 13 180 5 (28 : ℤ) (-150 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 13 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_14 : ZCov 13 180 74999999 1000000000 1 (3 : ℤ) (6 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 13 2 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_15 : ZCov 74999999 1000000000 3 40 10 (33 : ℤ) (20 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 2 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_16 : ZCov 3 40 75000001 1000000000 5 (18 : ℤ) (-10 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 1 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_17 : ZCov 75000001 1000000000 13 170 10 (39 : ℤ) (-60 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 13 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_18 : ZCov 13 170 23 300 10 (13 : ℤ) (280 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 13 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_19 : ZCov 23 300 1 13 10 (59 : ℤ) (-320 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 13 1 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_20 : ZCov 1 13 13 160 10 (39 : ℤ) (-60 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 12 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_21 : ZCov 13 160 23 280 10 (13 : ℤ) (260 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 12 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P10_22 : ZCov 23 280 1 12 10 (59 : ℤ) (-300 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 12 1 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P10 : List ZP := [
  ⟨13, 220, 59999999, 1000000000, 10, (13 : ℤ), (350 : ℤ), 200⟩,
  ⟨59999999, 1000000000, 3, 50, 5, (18 : ℤ), (-15 : ℤ), 100⟩,
  ⟨3, 50, 60000001, 1000000000, 10, (33 : ℤ), (20 : ℤ), 200⟩,
  ⟨60000001, 1000000000, 23, 380, 1, (1 : ℤ), (40 : ℤ), 20⟩,
  ⟨23, 380, 13, 210, 5, (28 : ℤ), (-180 : ℤ), 100⟩,
  ⟨13, 210, 1, 16, 1, (3 : ℤ), (6 : ℤ), 20⟩,
  ⟨1, 16, 23, 360, 1, (1 : ℤ), (38 : ℤ), 20⟩,
  ⟨23, 360, 13, 200, 5, (28 : ℤ), (-170 : ℤ), 100⟩,
  ⟨13, 200, 1, 15, 1, (3 : ℤ), (6 : ℤ), 20⟩,
  ⟨1, 15, 23, 340, 1, (1 : ℤ), (36 : ℤ), 20⟩,
  ⟨23, 340, 13, 190, 5, (28 : ℤ), (-160 : ℤ), 100⟩,
  ⟨13, 190, 1, 14, 1, (3 : ℤ), (6 : ℤ), 20⟩,
  ⟨1, 14, 23, 320, 1, (1 : ℤ), (34 : ℤ), 20⟩,
  ⟨23, 320, 13, 180, 5, (28 : ℤ), (-150 : ℤ), 100⟩,
  ⟨13, 180, 74999999, 1000000000, 1, (3 : ℤ), (6 : ℤ), 20⟩,
  ⟨74999999, 1000000000, 3, 40, 10, (33 : ℤ), (20 : ℤ), 200⟩,
  ⟨3, 40, 75000001, 1000000000, 5, (18 : ℤ), (-10 : ℤ), 100⟩,
  ⟨75000001, 1000000000, 13, 170, 10, (39 : ℤ), (-60 : ℤ), 200⟩,
  ⟨13, 170, 23, 300, 10, (13 : ℤ), (280 : ℤ), 200⟩,
  ⟨23, 300, 1, 13, 10, (59 : ℤ), (-320 : ℤ), 200⟩,
  ⟨1, 13, 13, 160, 10, (39 : ℤ), (-60 : ℤ), 200⟩,
  ⟨13, 160, 23, 280, 10, (13 : ℤ), (260 : ℤ), 200⟩,
  ⟨23, 280, 1, 12, 10, (59 : ℤ), (-300 : ℤ), 200⟩]

theorem zL_P10_cov : ZAllCov zL_P10 :=
  ⟨zp_P10_00, zp_P10_01, zp_P10_02, zp_P10_03, zp_P10_04, zp_P10_05, zp_P10_06, zp_P10_07, zp_P10_08, zp_P10_09, zp_P10_10, zp_P10_11, zp_P10_12, zp_P10_13, zp_P10_14, zp_P10_15, zp_P10_16, zp_P10_17, zp_P10_18, zp_P10_19, zp_P10_20, zp_P10_21, zp_P10_22, trivial⟩

theorem zL_P10_chain : zChain (13 / 220 : ℚ) zL_P10 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P10_end : zEnd (13 / 220 : ℚ) zL_P10 = (1 / 12 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P10_mass : zMass zL_P10 ≤ (16575272603013 / 200000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
