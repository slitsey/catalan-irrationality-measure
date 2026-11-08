module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P09 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.042857144, 0.059090909]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P09_00 : ZCov 300000007 7000000000 13 300 5 (28 : ℤ) (-255 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 23 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_01 : ZCov 13 300 1 23 1 (3 : ℤ) (9 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 23 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_02 : ZCov 1 23 23 520 1 (1 : ℤ) (55 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 22 3 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_03 : ZCov 23 520 13 290 5 (28 : ℤ) (-245 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 22 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_04 : ZCov 13 290 1 22 1 (3 : ℤ) (9 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 22 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_05 : ZCov 1 22 23 500 1 (1 : ℤ) (53 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 21 3 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_06 : ZCov 23 500 13 280 5 (28 : ℤ) (-235 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 21 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_07 : ZCov 13 280 1 21 1 (3 : ℤ) (9 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 21 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_08 : ZCov 1 21 23 480 1 (1 : ℤ) (51 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 20 3 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_09 : ZCov 23 480 13 270 5 (28 : ℤ) (-225 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 20 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_10 : ZCov 13 270 49999999 1000000000 1 (3 : ℤ) (9 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 20 3 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_11 : ZCov 49999999 1000000000 1 20 10 (33 : ℤ) (30 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 3 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_12 : ZCov 1 20 50000001 1000000000 5 (18 : ℤ) (-15 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 2 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_13 : ZCov 50000001 1000000000 13 250 10 (39 : ℤ) (-90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 19 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_14 : ZCov 13 250 23 440 10 (13 : ℤ) (410 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 19 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_15 : ZCov 23 440 1 19 10 (59 : ℤ) (-470 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 19 2 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_16 : ZCov 1 19 13 240 10 (39 : ℤ) (-90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 18 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_17 : ZCov 13 240 23 420 10 (13 : ℤ) (390 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 18 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_18 : ZCov 23 420 1 18 10 (59 : ℤ) (-450 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 18 2 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_19 : ZCov 1 18 13 230 10 (39 : ℤ) (-90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 17 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_20 : ZCov 13 230 23 400 10 (13 : ℤ) (370 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 17 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_21 : ZCov 23 400 1 17 10 (59 : ℤ) (-430 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 17 2 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P09_22 : ZCov 1 17 13 220 10 (39 : ℤ) (-90 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 16 2 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P09 : List ZP := [
  ⟨300000007, 7000000000, 13, 300, 5, (28 : ℤ), (-255 : ℤ), 100⟩,
  ⟨13, 300, 1, 23, 1, (3 : ℤ), (9 : ℤ), 20⟩,
  ⟨1, 23, 23, 520, 1, (1 : ℤ), (55 : ℤ), 20⟩,
  ⟨23, 520, 13, 290, 5, (28 : ℤ), (-245 : ℤ), 100⟩,
  ⟨13, 290, 1, 22, 1, (3 : ℤ), (9 : ℤ), 20⟩,
  ⟨1, 22, 23, 500, 1, (1 : ℤ), (53 : ℤ), 20⟩,
  ⟨23, 500, 13, 280, 5, (28 : ℤ), (-235 : ℤ), 100⟩,
  ⟨13, 280, 1, 21, 1, (3 : ℤ), (9 : ℤ), 20⟩,
  ⟨1, 21, 23, 480, 1, (1 : ℤ), (51 : ℤ), 20⟩,
  ⟨23, 480, 13, 270, 5, (28 : ℤ), (-225 : ℤ), 100⟩,
  ⟨13, 270, 49999999, 1000000000, 1, (3 : ℤ), (9 : ℤ), 20⟩,
  ⟨49999999, 1000000000, 1, 20, 10, (33 : ℤ), (30 : ℤ), 200⟩,
  ⟨1, 20, 50000001, 1000000000, 5, (18 : ℤ), (-15 : ℤ), 100⟩,
  ⟨50000001, 1000000000, 13, 250, 10, (39 : ℤ), (-90 : ℤ), 200⟩,
  ⟨13, 250, 23, 440, 10, (13 : ℤ), (410 : ℤ), 200⟩,
  ⟨23, 440, 1, 19, 10, (59 : ℤ), (-470 : ℤ), 200⟩,
  ⟨1, 19, 13, 240, 10, (39 : ℤ), (-90 : ℤ), 200⟩,
  ⟨13, 240, 23, 420, 10, (13 : ℤ), (390 : ℤ), 200⟩,
  ⟨23, 420, 1, 18, 10, (59 : ℤ), (-450 : ℤ), 200⟩,
  ⟨1, 18, 13, 230, 10, (39 : ℤ), (-90 : ℤ), 200⟩,
  ⟨13, 230, 23, 400, 10, (13 : ℤ), (370 : ℤ), 200⟩,
  ⟨23, 400, 1, 17, 10, (59 : ℤ), (-430 : ℤ), 200⟩,
  ⟨1, 17, 13, 220, 10, (39 : ℤ), (-90 : ℤ), 200⟩]

theorem zL_P09_cov : ZAllCov zL_P09 :=
  ⟨zp_P09_00, zp_P09_01, zp_P09_02, zp_P09_03, zp_P09_04, zp_P09_05, zp_P09_06, zp_P09_07, zp_P09_08, zp_P09_09, zp_P09_10, zp_P09_11, zp_P09_12, zp_P09_13, zp_P09_14, zp_P09_15, zp_P09_16, zp_P09_17, zp_P09_18, zp_P09_19, zp_P09_20, zp_P09_21, zp_P09_22, trivial⟩

theorem zL_P09_chain : zChain (300000007 / 7000000000 : ℚ) zL_P09 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P09_end : zEnd (300000007 / 7000000000 : ℚ) zL_P09 = (13 / 220 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P09_mass : zMass zL_P09 ≤ (55526086819139 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
