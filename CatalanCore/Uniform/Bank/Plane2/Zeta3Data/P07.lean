module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P07 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.029487179, 0.035135135]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P07_00 : ZCov 23 780 13 440 5 (28 : ℤ) (-365 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 33 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_01 : ZCov 13 440 29999999 1000000000 1 (3 : ℤ) (15 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 33 5 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_02 : ZCov 29999999 1000000000 3 100 10 (33 : ℤ) (50 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 5 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_03 : ZCov 3 100 30000001 1000000000 5 (18 : ℤ) (-25 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 4 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_04 : ZCov 30000001 1000000000 13 430 10 (39 : ℤ) (-150 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 33 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_05 : ZCov 13 430 23 760 10 (13 : ℤ) (710 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 33 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_06 : ZCov 23 760 1 33 10 (59 : ℤ) (-810 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 33 4 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_07 : ZCov 1 33 13 420 10 (39 : ℤ) (-150 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 32 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_08 : ZCov 13 420 23 740 10 (13 : ℤ) (690 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 32 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_09 : ZCov 23 740 1 32 10 (59 : ℤ) (-790 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 32 4 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_10 : ZCov 1 32 13 410 10 (39 : ℤ) (-150 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 31 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_11 : ZCov 13 410 23 720 10 (13 : ℤ) (670 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 31 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_12 : ZCov 23 720 1 31 10 (59 : ℤ) (-770 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 31 4 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_13 : ZCov 1 31 13 400 10 (39 : ℤ) (-150 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 30 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_14 : ZCov 13 400 23 700 10 (13 : ℤ) (650 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 30 4 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_15 : ZCov 23 700 99999997 3000000000 10 (59 : ℤ) (-750 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 30 4 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_16 : ZCov 99999997 3000000000 1 30 5 (18 : ℤ) (-25 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 4 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_17 : ZCov 1 30 100000003 3000000000 10 (33 : ℤ) (40 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 4 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_18 : ZCov 100000003 3000000000 23 680 1 (1 : ℤ) (72 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 29 4 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_19 : ZCov 23 680 13 380 5 (28 : ℤ) (-320 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 29 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_20 : ZCov 13 380 1 29 1 (3 : ℤ) (12 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 29 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_21 : ZCov 1 29 23 660 1 (1 : ℤ) (70 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 28 4 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P07_22 : ZCov 23 660 13 370 5 (28 : ℤ) (-310 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 28 4 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P07 : List ZP := [
  ⟨23, 780, 13, 440, 5, (28 : ℤ), (-365 : ℤ), 100⟩,
  ⟨13, 440, 29999999, 1000000000, 1, (3 : ℤ), (15 : ℤ), 20⟩,
  ⟨29999999, 1000000000, 3, 100, 10, (33 : ℤ), (50 : ℤ), 200⟩,
  ⟨3, 100, 30000001, 1000000000, 5, (18 : ℤ), (-25 : ℤ), 100⟩,
  ⟨30000001, 1000000000, 13, 430, 10, (39 : ℤ), (-150 : ℤ), 200⟩,
  ⟨13, 430, 23, 760, 10, (13 : ℤ), (710 : ℤ), 200⟩,
  ⟨23, 760, 1, 33, 10, (59 : ℤ), (-810 : ℤ), 200⟩,
  ⟨1, 33, 13, 420, 10, (39 : ℤ), (-150 : ℤ), 200⟩,
  ⟨13, 420, 23, 740, 10, (13 : ℤ), (690 : ℤ), 200⟩,
  ⟨23, 740, 1, 32, 10, (59 : ℤ), (-790 : ℤ), 200⟩,
  ⟨1, 32, 13, 410, 10, (39 : ℤ), (-150 : ℤ), 200⟩,
  ⟨13, 410, 23, 720, 10, (13 : ℤ), (670 : ℤ), 200⟩,
  ⟨23, 720, 1, 31, 10, (59 : ℤ), (-770 : ℤ), 200⟩,
  ⟨1, 31, 13, 400, 10, (39 : ℤ), (-150 : ℤ), 200⟩,
  ⟨13, 400, 23, 700, 10, (13 : ℤ), (650 : ℤ), 200⟩,
  ⟨23, 700, 99999997, 3000000000, 10, (59 : ℤ), (-750 : ℤ), 200⟩,
  ⟨99999997, 3000000000, 1, 30, 5, (18 : ℤ), (-25 : ℤ), 100⟩,
  ⟨1, 30, 100000003, 3000000000, 10, (33 : ℤ), (40 : ℤ), 200⟩,
  ⟨100000003, 3000000000, 23, 680, 1, (1 : ℤ), (72 : ℤ), 20⟩,
  ⟨23, 680, 13, 380, 5, (28 : ℤ), (-320 : ℤ), 100⟩,
  ⟨13, 380, 1, 29, 1, (3 : ℤ), (12 : ℤ), 20⟩,
  ⟨1, 29, 23, 660, 1, (1 : ℤ), (70 : ℤ), 20⟩,
  ⟨23, 660, 13, 370, 5, (28 : ℤ), (-310 : ℤ), 100⟩]

theorem zL_P07_cov : ZAllCov zL_P07 :=
  ⟨zp_P07_00, zp_P07_01, zp_P07_02, zp_P07_03, zp_P07_04, zp_P07_05, zp_P07_06, zp_P07_07, zp_P07_08, zp_P07_09, zp_P07_10, zp_P07_11, zp_P07_12, zp_P07_13, zp_P07_14, zp_P07_15, zp_P07_16, zp_P07_17, zp_P07_18, zp_P07_19, zp_P07_20, zp_P07_21, zp_P07_22, trivial⟩

theorem zL_P07_chain : zChain (23 / 780 : ℚ) zL_P07 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P07_end : zEnd (23 / 780 : ℚ) zL_P07 = (13 / 370 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P07_mass : zMass zL_P07 ≤ (19368459374451 / 1000000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
