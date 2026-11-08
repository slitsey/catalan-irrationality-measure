module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Content

@[expose] public section
set_option Elab.async false

/-! # ζ(3) content cover, chunk P11 (lane H, wave Z2): 23 pieces of the chain, `θ ∈ (0.083333333, 0.162500000]`.
Each piece is a linear implication over the integers closed by `omega` after one sweep row (`Zeta3Content`). -/

namespace CatalanCore.Uniform.Bank.Plane2

theorem zp_P11_00 : ZCov 1 12 13 150 10 (39 : ℤ) (-60 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 11 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_01 : ZCov 13 150 23 260 10 (13 : ℤ) (240 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 11 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_02 : ZCov 23 260 1 11 10 (59 : ℤ) (-280 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 11 1 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_03 : ZCov 1 11 13 140 10 (39 : ℤ) (-60 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 10 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_04 : ZCov 13 140 23 240 10 (13 : ℤ) (220 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 10 1 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_05 : ZCov 23 240 99999999 1000000000 10 (59 : ℤ) (-260 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 10 1 0 2 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_06 : ZCov 99999999 1000000000 1 10 5 (18 : ℤ) (-10 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 1 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_07 : ZCov 1 10 100000001 1000000000 10 (33 : ℤ) (10 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 1 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_08 : ZCov 100000001 1000000000 23 220 1 (1 : ℤ) (23 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 9 1 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_09 : ZCov 23 220 13 120 5 (28 : ℤ) (-105 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 9 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_10 : ZCov 13 120 1 9 1 (3 : ℤ) (3 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 9 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_11 : ZCov 1 9 23 200 1 (1 : ℤ) (21 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 8 1 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_12 : ZCov 23 200 13 110 5 (28 : ℤ) (-95 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 8 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_13 : ZCov 13 110 1 8 1 (3 : ℤ) (3 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 8 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_14 : ZCov 1 8 23 180 1 (1 : ℤ) (19 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 7 1 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_15 : ZCov 23 180 13 100 5 (28 : ℤ) (-85 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 7 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_16 : ZCov 13 100 1 7 1 (3 : ℤ) (3 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 7 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_17 : ZCov 1 7 23 160 1 (1 : ℤ) (17 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 6 1 2 0 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_18 : ZCov 23 160 13 90 5 (28 : ℤ) (-75 : ℤ) 100 :=
  zc_P1e0 (by norm_num) (by norm_num) 6 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_19 : ZCov 13 90 149999999 1000000000 1 (3 : ℤ) (3 : ℤ) 20 :=
  zc_P1e0 (by norm_num) (by norm_num) 6 1 0 2 (by norm_num) (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_20 : ZCov 149999999 1000000000 3 20 10 (33 : ℤ) (10 : ℤ) 200 :=
  zc_S (by norm_num) (by norm_num) 1 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_21 : ZCov 3 20 150000001 1000000000 5 (18 : ℤ) (-5 : ℤ) 100 :=
  zc_S (by norm_num) (by norm_num) 0 (by intro r p m d h hd hdm; simp only [ZH, ZR0] at h; omega)

theorem zp_P11_22 : ZCov 150000001 1000000000 13 80 10 (39 : ℤ) (-30 : ℤ) 200 :=
  zc_P1e1 (by norm_num) (by norm_num) 6 0 2 0 (by norm_num) (by intro r p m h; simp only [ZH, ZR0] at h; omega) (by intro r p m h h1 h2 h3 h4; simp only [ZH, ZR0] at h; omega)

def zL_P11 : List ZP := [
  ⟨1, 12, 13, 150, 10, (39 : ℤ), (-60 : ℤ), 200⟩,
  ⟨13, 150, 23, 260, 10, (13 : ℤ), (240 : ℤ), 200⟩,
  ⟨23, 260, 1, 11, 10, (59 : ℤ), (-280 : ℤ), 200⟩,
  ⟨1, 11, 13, 140, 10, (39 : ℤ), (-60 : ℤ), 200⟩,
  ⟨13, 140, 23, 240, 10, (13 : ℤ), (220 : ℤ), 200⟩,
  ⟨23, 240, 99999999, 1000000000, 10, (59 : ℤ), (-260 : ℤ), 200⟩,
  ⟨99999999, 1000000000, 1, 10, 5, (18 : ℤ), (-10 : ℤ), 100⟩,
  ⟨1, 10, 100000001, 1000000000, 10, (33 : ℤ), (10 : ℤ), 200⟩,
  ⟨100000001, 1000000000, 23, 220, 1, (1 : ℤ), (23 : ℤ), 20⟩,
  ⟨23, 220, 13, 120, 5, (28 : ℤ), (-105 : ℤ), 100⟩,
  ⟨13, 120, 1, 9, 1, (3 : ℤ), (3 : ℤ), 20⟩,
  ⟨1, 9, 23, 200, 1, (1 : ℤ), (21 : ℤ), 20⟩,
  ⟨23, 200, 13, 110, 5, (28 : ℤ), (-95 : ℤ), 100⟩,
  ⟨13, 110, 1, 8, 1, (3 : ℤ), (3 : ℤ), 20⟩,
  ⟨1, 8, 23, 180, 1, (1 : ℤ), (19 : ℤ), 20⟩,
  ⟨23, 180, 13, 100, 5, (28 : ℤ), (-85 : ℤ), 100⟩,
  ⟨13, 100, 1, 7, 1, (3 : ℤ), (3 : ℤ), 20⟩,
  ⟨1, 7, 23, 160, 1, (1 : ℤ), (17 : ℤ), 20⟩,
  ⟨23, 160, 13, 90, 5, (28 : ℤ), (-75 : ℤ), 100⟩,
  ⟨13, 90, 149999999, 1000000000, 1, (3 : ℤ), (3 : ℤ), 20⟩,
  ⟨149999999, 1000000000, 3, 20, 10, (33 : ℤ), (10 : ℤ), 200⟩,
  ⟨3, 20, 150000001, 1000000000, 5, (18 : ℤ), (-5 : ℤ), 100⟩,
  ⟨150000001, 1000000000, 13, 80, 10, (39 : ℤ), (-30 : ℤ), 200⟩]

theorem zL_P11_cov : ZAllCov zL_P11 :=
  ⟨zp_P11_00, zp_P11_01, zp_P11_02, zp_P11_03, zp_P11_04, zp_P11_05, zp_P11_06, zp_P11_07, zp_P11_08, zp_P11_09, zp_P11_10, zp_P11_11, zp_P11_12, zp_P11_13, zp_P11_14, zp_P11_15, zp_P11_16, zp_P11_17, zp_P11_18, zp_P11_19, zp_P11_20, zp_P11_21, zp_P11_22, trivial⟩

theorem zL_P11_chain : zChain (1 / 12 : ℚ) zL_P11 = true := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P11_end : zEnd (1 / 12 : ℚ) zL_P11 = (13 / 80 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

theorem zL_P11_mass : zMass zL_P11 ≤ (134316545533733 / 500000000000000 : ℚ) := by
  -- kcost: 0.4 s measured (23 pieces, about 12 Rat ops each)
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2
