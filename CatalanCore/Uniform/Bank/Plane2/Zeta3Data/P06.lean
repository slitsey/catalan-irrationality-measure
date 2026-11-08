module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P06 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.025000001, 0.029487179]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P06_00 : ZCov 25000001 1000000000 13 510 10 (39 : ℤ) (-180 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 39 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_01 : ZCov 13 510 23 900 10 (13 : ℤ) (840 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 39 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_02 : ZCov 23 900 1 39 10 (59 : ℤ) (-960 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 39 5 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_03 : ZCov 1 39 13 500 10 (39 : ℤ) (-180 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 38 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_04 : ZCov 13 500 23 880 10 (13 : ℤ) (820 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 38 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_05 : ZCov 23 880 1 38 10 (59 : ℤ) (-940 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 38 5 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_06 : ZCov 1 38 13 490 10 (39 : ℤ) (-180 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 37 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_07 : ZCov 13 490 23 860 10 (13 : ℤ) (800 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 37 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_08 : ZCov 23 860 1 37 10 (59 : ℤ) (-920 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 37 5 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_09 : ZCov 1 37 13 480 10 (39 : ℤ) (-180 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 36 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_10 : ZCov 13 480 299999989 11000000000 10 (13 : ℤ) (780 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 36 5 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_11 : ZCov 299999989 11000000000 3 110 5 (18 : ℤ) (-30 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 5 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_12 : ZCov 3 110 300000011 11000000000 10 (33 : ℤ) (50 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 5 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_13 : ZCov 300000011 11000000000 23 840 1 (1 : ℤ) (89 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 36 5 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_14 : ZCov 23 840 13 470 5 (28 : ℤ) (-395 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 36 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_15 : ZCov 13 470 1 36 1 (3 : ℤ) (15 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 36 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_16 : ZCov 1 36 23 820 1 (1 : ℤ) (87 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 35 5 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_17 : ZCov 23 820 13 460 5 (28 : ℤ) (-385 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 35 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_18 : ZCov 13 460 1 35 1 (3 : ℤ) (15 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 35 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_19 : ZCov 1 35 23 800 1 (1 : ℤ) (85 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 34 5 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_20 : ZCov 23 800 13 450 5 (28 : ℤ) (-375 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 34 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_21 : ZCov 13 450 1 34 1 (3 : ℤ) (15 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 34 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P06_22 : ZCov 1 34 23 780 1 (1 : ℤ) (83 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 33 5 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P06 : List ZP := [
  ⟨25000001, 1000000000, 13, 510, 10, (39 : ℤ), (-180 : ℤ), 200⟩,
  ⟨13, 510, 23, 900, 10, (13 : ℤ), (840 : ℤ), 200⟩,
  ⟨23, 900, 1, 39, 10, (59 : ℤ), (-960 : ℤ), 200⟩,
  ⟨1, 39, 13, 500, 10, (39 : ℤ), (-180 : ℤ), 200⟩,
  ⟨13, 500, 23, 880, 10, (13 : ℤ), (820 : ℤ), 200⟩,
  ⟨23, 880, 1, 38, 10, (59 : ℤ), (-940 : ℤ), 200⟩,
  ⟨1, 38, 13, 490, 10, (39 : ℤ), (-180 : ℤ), 200⟩,
  ⟨13, 490, 23, 860, 10, (13 : ℤ), (800 : ℤ), 200⟩,
  ⟨23, 860, 1, 37, 10, (59 : ℤ), (-920 : ℤ), 200⟩,
  ⟨1, 37, 13, 480, 10, (39 : ℤ), (-180 : ℤ), 200⟩,
  ⟨13, 480, 299999989, 11000000000, 10, (13 : ℤ), (780 : ℤ), 200⟩,
  ⟨299999989, 11000000000, 3, 110, 5, (18 : ℤ), (-30 : ℤ), 100⟩,
  ⟨3, 110, 300000011, 11000000000, 10, (33 : ℤ), (50 : ℤ), 200⟩,
  ⟨300000011, 11000000000, 23, 840, 1, (1 : ℤ), (89 : ℤ), 20⟩,
  ⟨23, 840, 13, 470, 5, (28 : ℤ), (-395 : ℤ), 100⟩,
  ⟨13, 470, 1, 36, 1, (3 : ℤ), (15 : ℤ), 20⟩,
  ⟨1, 36, 23, 820, 1, (1 : ℤ), (87 : ℤ), 20⟩,
  ⟨23, 820, 13, 460, 5, (28 : ℤ), (-385 : ℤ), 100⟩,
  ⟨13, 460, 1, 35, 1, (3 : ℤ), (15 : ℤ), 20⟩,
  ⟨1, 35, 23, 800, 1, (1 : ℤ), (85 : ℤ), 20⟩,
  ⟨23, 800, 13, 450, 5, (28 : ℤ), (-375 : ℤ), 100⟩,
  ⟨13, 450, 1, 34, 1, (3 : ℤ), (15 : ℤ), 20⟩,
  ⟨1, 34, 23, 780, 1, (1 : ℤ), (83 : ℤ), 20⟩]

theorem zL_P06_cov : ZAllCov zL_P06 :=
  ⟨zp_P06_00, zp_P06_01, zp_P06_02, zp_P06_03, zp_P06_04, zp_P06_05, zp_P06_06, zp_P06_07, zp_P06_08, zp_P06_09, zp_P06_10, zp_P06_11, zp_P06_12, zp_P06_13, zp_P06_14, zp_P06_15, zp_P06_16, zp_P06_17, zp_P06_18, zp_P06_19, zp_P06_20, zp_P06_21, zp_P06_22, trivial⟩

theorem zL_P06_chain : zChain (25000001 / 1000000000 : ℚ) zL_P06 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P06_end : zEnd (25000001 / 1000000000 : ℚ) zL_P06 = (23 / 780 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P06_mass : zMass zL_P06 ≤ (15402978444603 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
