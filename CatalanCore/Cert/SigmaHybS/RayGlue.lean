module

public import CatalanCore.Cert.SigmaHybS.RayM0
public import CatalanCore.Cert.SigmaHybS.RayM1
public import CatalanCore.Cert.SigmaHybS.RayM2
public import CatalanCore.Cert.SigmaHybS.RayM3
public import CatalanCore.Cert.SigmaHybS.RayM4
public import CatalanCore.Cert.SigmaHybS.RayM5
public import CatalanCore.Cert.SigmaHybS.RayM6
public import CatalanCore.Cert.SigmaHybS.RayM7
public import CatalanCore.Cert.SigmaHybS.RayM8
public import CatalanCore.Cert.SigmaHybS.RayM9
public import CatalanCore.Cert.SigmaHybS.RayM10
public import CatalanCore.Cert.SigmaHybS.RayM11
public import CatalanCore.Cert.SigmaHybS.RayM12
public import CatalanCore.Cert.SigmaHybS.RayM13
public import CatalanCore.Cert.SigmaHybS.RayM14
public import CatalanCore.Cert.SigmaHybS.RayM15
public import CatalanCore.Cert.SigmaHybS.RayM16
public import CatalanCore.Cert.SigmaHybS.RayM17
public import CatalanCore.Cert.SigmaHybS.RayM18
public import CatalanCore.Cert.SigmaHybS.RayM19
public import CatalanCore.Cert.SigmaHybS.RayM20
public import CatalanCore.Cert.SigmaHybS.RayM21
public import CatalanCore.Cert.SigmaHybS.RayM22
public import CatalanCore.Cert.SigmaHybS.RayM23
public import CatalanCore.Cert.SigmaHybS.RayM24
public import CatalanCore.Cert.SigmaHybS.RayM25
public import CatalanCore.Cert.SigmaHybS.RayM26
public import CatalanCore.Cert.SigmaHybS.RayM27
public import CatalanCore.Cert.SigmaHybS.RayM28
public import CatalanCore.Cert.SigmaHybS.RayM29
public import CatalanCore.Cert.SigmaHybS.RayM30
public import CatalanCore.Cert.SigmaHybS.RayM31
public import CatalanCore.Cert.SigmaHybS.RayM32
public import CatalanCore.Cert.SigmaHybS.RayM33
public import CatalanCore.Cert.SigmaHybS.RayM34
public import CatalanCore.Cert.SigmaHybS.RayM35
public import CatalanCore.Cert.SigmaHybS.RayM36
public import CatalanCore.Cert.SigmaHybS.RayM37
public import CatalanCore.Cert.SigmaHybS.RayM38
public import CatalanCore.Cert.SigmaHybS.RayM39
public import CatalanCore.Cert.SigmaHybS.RayM40
public import CatalanCore.Cert.SigmaHybS.RayM41
public import CatalanCore.Cert.SigmaHybS.RayM42
public import CatalanCore.Cert.SigmaHybS.RayM43
public import CatalanCore.Cert.SigmaHybS.RayM44
public import CatalanCore.Cert.SigmaHybS.RayM45
public import CatalanCore.Cert.SigmaHybS.RayM46
public import CatalanCore.Cert.SigmaHybS.RayM47
public import CatalanCore.Cert.SigmaHybS.RayM48
public import CatalanCore.Cert.SigmaHybS.RayM49
public import CatalanCore.Cert.SigmaHybS.RayM50
public import CatalanCore.Cert.SigmaHybS.RayM51
public import CatalanCore.Cert.SigmaHybS.RayM52
public import CatalanCore.Cert.SigmaHybS.RayM53
public import CatalanCore.Cert.SigmaHybS.RayM54
public import CatalanCore.Cert.SigmaHybS.RayM55
public import CatalanCore.Cert.SigmaHybS.RayM56
public import CatalanCore.Cert.SigmaHybS.RayM57
public import CatalanCore.Cert.SigmaHybS.RayM58
public import CatalanCore.Cert.SigmaHybS.RayM59
public import CatalanCore.Cert.SigmaHybS.RayM60
public import CatalanCore.Cert.SigmaHybS.RayM61
public import CatalanCore.Cert.SigmaHybS.RayM62
public import CatalanCore.Cert.SigmaHybS.RayM63
public import CatalanCore.Cert.SigmaHybS.RayM64
public import CatalanCore.Cert.SigmaHybS.RayM65
public import CatalanCore.Cert.SigmaHybS.RayM66
public import CatalanCore.Cert.SigmaHybS.RayM67
public import CatalanCore.Cert.SigmaHybS.Bridge

@[expose] public section

/-!
# Glue for the ray cells: global indexing of the 68 modules (69632 cells), geometry (the cell box contains the tube of its `u`-interval), chain (cover of `[0,3/2]`).
-/

open Real

namespace CatalanCore.Cert.SigmaHybS

set_option maxRecDepth 100000

def rayM : ℕ → ℕ
  | 0 => 64
  | 1 => 64
  | 2 => 64
  | 3 => 64
  | 4 => 64
  | 5 => 64
  | 6 => 64
  | 7 => 64
  | 8 => 64
  | 9 => 64
  | 10 => 64
  | 11 => 64
  | 12 => 64
  | 13 => 64
  | 14 => 64
  | 15 => 64
  | 16 => 64
  | 17 => 64
  | 18 => 64
  | 19 => 64
  | 20 => 64
  | 21 => 64
  | 22 => 64
  | 23 => 64
  | 24 => 64
  | 25 => 64
  | 26 => 64
  | 27 => 64
  | 28 => 64
  | 29 => 64
  | 30 => 64
  | 31 => 64
  | 32 => 64
  | 33 => 64
  | 34 => 64
  | 35 => 64
  | 36 => 64
  | 37 => 64
  | 38 => 64
  | 39 => 64
  | 40 => 64
  | 41 => 64
  | 42 => 64
  | 43 => 64
  | 44 => 64
  | 45 => 64
  | 46 => 64
  | 47 => 64
  | 48 => 64
  | 49 => 64
  | 50 => 64
  | 51 => 64
  | 52 => 64
  | 53 => 64
  | 54 => 64
  | 55 => 64
  | 56 => 64
  | 57 => 64
  | 58 => 64
  | 59 => 64
  | 60 => 64
  | 61 => 64
  | 62 => 64
  | 63 => 64
  | 64 => 16
  | 65 => 64
  | 66 => 64
  | 67 => 64
  | _ => 1

def rayP : ℕ → ℕ
  | 0 => RayM0P
  | 1 => RayM1P
  | 2 => RayM2P
  | 3 => RayM3P
  | 4 => RayM4P
  | 5 => RayM5P
  | 6 => RayM6P
  | 7 => RayM7P
  | 8 => RayM8P
  | 9 => RayM9P
  | 10 => RayM10P
  | 11 => RayM11P
  | 12 => RayM12P
  | 13 => RayM13P
  | 14 => RayM14P
  | 15 => RayM15P
  | 16 => RayM16P
  | 17 => RayM17P
  | 18 => RayM18P
  | 19 => RayM19P
  | 20 => RayM20P
  | 21 => RayM21P
  | 22 => RayM22P
  | 23 => RayM23P
  | 24 => RayM24P
  | 25 => RayM25P
  | 26 => RayM26P
  | 27 => RayM27P
  | 28 => RayM28P
  | 29 => RayM29P
  | 30 => RayM30P
  | 31 => RayM31P
  | 32 => RayM32P
  | 33 => RayM33P
  | 34 => RayM34P
  | 35 => RayM35P
  | 36 => RayM36P
  | 37 => RayM37P
  | 38 => RayM38P
  | 39 => RayM39P
  | 40 => RayM40P
  | 41 => RayM41P
  | 42 => RayM42P
  | 43 => RayM43P
  | 44 => RayM44P
  | 45 => RayM45P
  | 46 => RayM46P
  | 47 => RayM47P
  | 48 => RayM48P
  | 49 => RayM49P
  | 50 => RayM50P
  | 51 => RayM51P
  | 52 => RayM52P
  | 53 => RayM53P
  | 54 => RayM54P
  | 55 => RayM55P
  | 56 => RayM56P
  | 57 => RayM57P
  | 58 => RayM58P
  | 59 => RayM59P
  | 60 => RayM60P
  | 61 => RayM61P
  | 62 => RayM62P
  | 63 => RayM63P
  | 64 => RayM64P
  | 65 => RayM65P
  | 66 => RayM66P
  | 67 => RayM67P
  | _ => 0

theorem rayAll_ok : ∀ m < 68, ∀ j < 1024 / rayM m, gMacroOK sigH MPRAY (rayM m) (rayP m) j = true := by
  intro m hm
  interval_cases m
  exacts [RayM0_ok, RayM1_ok, RayM2_ok, RayM3_ok, RayM4_ok, RayM5_ok, RayM6_ok, RayM7_ok, RayM8_ok, RayM9_ok, RayM10_ok, RayM11_ok, RayM12_ok, RayM13_ok, RayM14_ok, RayM15_ok, RayM16_ok, RayM17_ok, RayM18_ok, RayM19_ok, RayM20_ok, RayM21_ok, RayM22_ok, RayM23_ok, RayM24_ok, RayM25_ok, RayM26_ok, RayM27_ok, RayM28_ok, RayM29_ok, RayM30_ok, RayM31_ok, RayM32_ok, RayM33_ok, RayM34_ok, RayM35_ok, RayM36_ok, RayM37_ok, RayM38_ok, RayM39_ok, RayM40_ok, RayM41_ok, RayM42_ok, RayM43_ok, RayM44_ok, RayM45_ok, RayM46_ok, RayM47_ok, RayM48_ok, RayM49_ok, RayM50_ok, RayM51_ok, RayM52_ok, RayM53_ok, RayM54_ok, RayM55_ok, RayM56_ok, RayM57_ok, RayM58_ok, RayM59_ok, RayM60_ok, RayM61_ok, RayM62_ok, RayM63_ok, RayM64_ok, RayM65_ok, RayM66_ok, RayM67_ok]

theorem rayM_pos (m : ℕ) : 0 < rayM m := by
  unfold rayM; split <;> norm_num

theorem rayM_dvd (m : ℕ) (hm : m < 68) : rayM m ∣ 1024 := by
  interval_cases m <;> decide

def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  cellBox (rayM (i / 1024)) (rayP (i / 1024)) ((i % 1024) / rayM (i / 1024)) (i % rayM (i / 1024))

theorem ray_sound (i : ℕ) (hi : i < 69632) (x y : ℝ)
    (h1 : ((rayCellG i).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((rayCellG i).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((rayCellG i).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((rayCellG i).2.2.2 : ℝ) / 2 ^ 40) :
    (MPRAY : ℝ) ≤ gHR sigH x y :=
  gMod_sound sigH MPRAY (rayM (i / 1024)) (rayP (i / 1024)) (1024 / rayM (i / 1024)) (rayAll_ok (i / 1024) (by omega))
    ((i % 1024) / rayM (i / 1024))
    (Nat.div_lt_div_of_lt_of_dvd (rayM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))) (i % rayM (i / 1024)) (Nat.mod_lt _ (rayM_pos _)) x y h1 h2 h3 h4

def rayGeomCell (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (b.2.1 < 0 ∧ 0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧
    50 * b.1 ≤ -7 * 2 ^ 40 - 20 * b.2.2.2 - 51200 ∧
    -7 * 2 ^ 40 - 20 * b.2.2.1 + 51200 ≤ 50 * b.2.1)

def rayChainCell (i : ℕ) : Bool :=
  decide (69632 ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)

theorem ray_geom_0 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 0 + i))) = true := by
  decide +kernel

theorem ray_geom_1 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 1 + i))) = true := by
  decide +kernel

theorem ray_geom_2 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 2 + i))) = true := by
  decide +kernel

theorem ray_geom_3 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 3 + i))) = true := by
  decide +kernel

theorem ray_geom_4 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 4 + i))) = true := by
  decide +kernel

theorem ray_geom_5 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 5 + i))) = true := by
  decide +kernel

theorem ray_geom_6 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 6 + i))) = true := by
  decide +kernel

theorem ray_geom_7 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 7 + i))) = true := by
  decide +kernel

theorem ray_geom_8 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 8 + i))) = true := by
  decide +kernel

theorem ray_geom_9 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 9 + i))) = true := by
  decide +kernel

theorem ray_geom_10 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 10 + i))) = true := by
  decide +kernel

theorem ray_geom_11 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 11 + i))) = true := by
  decide +kernel

theorem ray_geom_12 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 12 + i))) = true := by
  decide +kernel

theorem ray_geom_13 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 13 + i))) = true := by
  decide +kernel

theorem ray_geom_14 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 14 + i))) = true := by
  decide +kernel

theorem ray_geom_15 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 15 + i))) = true := by
  decide +kernel

theorem ray_geom_16 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 16 + i))) = true := by
  decide +kernel

theorem ray_geom_17 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 17 + i))) = true := by
  decide +kernel

theorem ray_geom_18 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 18 + i))) = true := by
  decide +kernel

theorem ray_geom_19 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 19 + i))) = true := by
  decide +kernel

theorem ray_geom_20 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 20 + i))) = true := by
  decide +kernel

theorem ray_geom_21 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 21 + i))) = true := by
  decide +kernel

theorem ray_geom_22 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 22 + i))) = true := by
  decide +kernel

theorem ray_geom_23 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 23 + i))) = true := by
  decide +kernel

theorem ray_geom_24 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 24 + i))) = true := by
  decide +kernel

theorem ray_geom_25 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 25 + i))) = true := by
  decide +kernel

theorem ray_geom_26 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 26 + i))) = true := by
  decide +kernel

theorem ray_geom_27 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 27 + i))) = true := by
  decide +kernel

theorem ray_geom_28 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 28 + i))) = true := by
  decide +kernel

theorem ray_geom_29 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 29 + i))) = true := by
  decide +kernel

theorem ray_geom_30 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 30 + i))) = true := by
  decide +kernel

theorem ray_geom_31 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 31 + i))) = true := by
  decide +kernel

theorem ray_geom_32 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 32 + i))) = true := by
  decide +kernel

theorem ray_geom_33 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 33 + i))) = true := by
  decide +kernel

theorem ray_geom_34 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 34 + i))) = true := by
  decide +kernel

theorem ray_geom_35 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 35 + i))) = true := by
  decide +kernel

theorem ray_geom_36 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 36 + i))) = true := by
  decide +kernel

theorem ray_geom_37 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 37 + i))) = true := by
  decide +kernel

theorem ray_geom_38 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 38 + i))) = true := by
  decide +kernel

theorem ray_geom_39 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 39 + i))) = true := by
  decide +kernel

theorem ray_geom_40 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 40 + i))) = true := by
  decide +kernel

theorem ray_geom_41 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 41 + i))) = true := by
  decide +kernel

theorem ray_geom_42 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 42 + i))) = true := by
  decide +kernel

theorem ray_geom_43 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 43 + i))) = true := by
  decide +kernel

theorem ray_geom_44 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 44 + i))) = true := by
  decide +kernel

theorem ray_geom_45 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 45 + i))) = true := by
  decide +kernel

theorem ray_geom_46 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 46 + i))) = true := by
  decide +kernel

theorem ray_geom_47 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 47 + i))) = true := by
  decide +kernel

theorem ray_geom_48 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 48 + i))) = true := by
  decide +kernel

theorem ray_geom_49 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 49 + i))) = true := by
  decide +kernel

theorem ray_geom_50 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 50 + i))) = true := by
  decide +kernel

theorem ray_geom_51 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 51 + i))) = true := by
  decide +kernel

theorem ray_geom_52 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 52 + i))) = true := by
  decide +kernel

theorem ray_geom_53 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 53 + i))) = true := by
  decide +kernel

theorem ray_geom_54 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 54 + i))) = true := by
  decide +kernel

theorem ray_geom_55 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 55 + i))) = true := by
  decide +kernel

theorem ray_geom_56 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 56 + i))) = true := by
  decide +kernel

theorem ray_geom_57 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 57 + i))) = true := by
  decide +kernel

theorem ray_geom_58 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 58 + i))) = true := by
  decide +kernel

theorem ray_geom_59 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 59 + i))) = true := by
  decide +kernel

theorem ray_geom_60 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 60 + i))) = true := by
  decide +kernel

theorem ray_geom_61 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 61 + i))) = true := by
  decide +kernel

theorem ray_geom_62 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 62 + i))) = true := by
  decide +kernel

theorem ray_geom_63 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 63 + i))) = true := by
  decide +kernel

theorem ray_geom_64 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 64 + i))) = true := by
  decide +kernel

theorem ray_geom_65 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 65 + i))) = true := by
  decide +kernel

theorem ray_geom_66 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 66 + i))) = true := by
  decide +kernel

theorem ray_geom_67 : (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * 67 + i))) = true := by
  decide +kernel

theorem ray_chain_0 : (List.range 1024).all (fun i => rayChainCell (1024 * 0 + i)) = true := by
  decide +kernel

theorem ray_chain_1 : (List.range 1024).all (fun i => rayChainCell (1024 * 1 + i)) = true := by
  decide +kernel

theorem ray_chain_2 : (List.range 1024).all (fun i => rayChainCell (1024 * 2 + i)) = true := by
  decide +kernel

theorem ray_chain_3 : (List.range 1024).all (fun i => rayChainCell (1024 * 3 + i)) = true := by
  decide +kernel

theorem ray_chain_4 : (List.range 1024).all (fun i => rayChainCell (1024 * 4 + i)) = true := by
  decide +kernel

theorem ray_chain_5 : (List.range 1024).all (fun i => rayChainCell (1024 * 5 + i)) = true := by
  decide +kernel

theorem ray_chain_6 : (List.range 1024).all (fun i => rayChainCell (1024 * 6 + i)) = true := by
  decide +kernel

theorem ray_chain_7 : (List.range 1024).all (fun i => rayChainCell (1024 * 7 + i)) = true := by
  decide +kernel

theorem ray_chain_8 : (List.range 1024).all (fun i => rayChainCell (1024 * 8 + i)) = true := by
  decide +kernel

theorem ray_chain_9 : (List.range 1024).all (fun i => rayChainCell (1024 * 9 + i)) = true := by
  decide +kernel

theorem ray_chain_10 : (List.range 1024).all (fun i => rayChainCell (1024 * 10 + i)) = true := by
  decide +kernel

theorem ray_chain_11 : (List.range 1024).all (fun i => rayChainCell (1024 * 11 + i)) = true := by
  decide +kernel

theorem ray_chain_12 : (List.range 1024).all (fun i => rayChainCell (1024 * 12 + i)) = true := by
  decide +kernel

theorem ray_chain_13 : (List.range 1024).all (fun i => rayChainCell (1024 * 13 + i)) = true := by
  decide +kernel

theorem ray_chain_14 : (List.range 1024).all (fun i => rayChainCell (1024 * 14 + i)) = true := by
  decide +kernel

theorem ray_chain_15 : (List.range 1024).all (fun i => rayChainCell (1024 * 15 + i)) = true := by
  decide +kernel

theorem ray_chain_16 : (List.range 1024).all (fun i => rayChainCell (1024 * 16 + i)) = true := by
  decide +kernel

theorem ray_chain_17 : (List.range 1024).all (fun i => rayChainCell (1024 * 17 + i)) = true := by
  decide +kernel

theorem ray_chain_18 : (List.range 1024).all (fun i => rayChainCell (1024 * 18 + i)) = true := by
  decide +kernel

theorem ray_chain_19 : (List.range 1024).all (fun i => rayChainCell (1024 * 19 + i)) = true := by
  decide +kernel

theorem ray_chain_20 : (List.range 1024).all (fun i => rayChainCell (1024 * 20 + i)) = true := by
  decide +kernel

theorem ray_chain_21 : (List.range 1024).all (fun i => rayChainCell (1024 * 21 + i)) = true := by
  decide +kernel

theorem ray_chain_22 : (List.range 1024).all (fun i => rayChainCell (1024 * 22 + i)) = true := by
  decide +kernel

theorem ray_chain_23 : (List.range 1024).all (fun i => rayChainCell (1024 * 23 + i)) = true := by
  decide +kernel

theorem ray_chain_24 : (List.range 1024).all (fun i => rayChainCell (1024 * 24 + i)) = true := by
  decide +kernel

theorem ray_chain_25 : (List.range 1024).all (fun i => rayChainCell (1024 * 25 + i)) = true := by
  decide +kernel

theorem ray_chain_26 : (List.range 1024).all (fun i => rayChainCell (1024 * 26 + i)) = true := by
  decide +kernel

theorem ray_chain_27 : (List.range 1024).all (fun i => rayChainCell (1024 * 27 + i)) = true := by
  decide +kernel

theorem ray_chain_28 : (List.range 1024).all (fun i => rayChainCell (1024 * 28 + i)) = true := by
  decide +kernel

theorem ray_chain_29 : (List.range 1024).all (fun i => rayChainCell (1024 * 29 + i)) = true := by
  decide +kernel

theorem ray_chain_30 : (List.range 1024).all (fun i => rayChainCell (1024 * 30 + i)) = true := by
  decide +kernel

theorem ray_chain_31 : (List.range 1024).all (fun i => rayChainCell (1024 * 31 + i)) = true := by
  decide +kernel

theorem ray_chain_32 : (List.range 1024).all (fun i => rayChainCell (1024 * 32 + i)) = true := by
  decide +kernel

theorem ray_chain_33 : (List.range 1024).all (fun i => rayChainCell (1024 * 33 + i)) = true := by
  decide +kernel

theorem ray_chain_34 : (List.range 1024).all (fun i => rayChainCell (1024 * 34 + i)) = true := by
  decide +kernel

theorem ray_chain_35 : (List.range 1024).all (fun i => rayChainCell (1024 * 35 + i)) = true := by
  decide +kernel

theorem ray_chain_36 : (List.range 1024).all (fun i => rayChainCell (1024 * 36 + i)) = true := by
  decide +kernel

theorem ray_chain_37 : (List.range 1024).all (fun i => rayChainCell (1024 * 37 + i)) = true := by
  decide +kernel

theorem ray_chain_38 : (List.range 1024).all (fun i => rayChainCell (1024 * 38 + i)) = true := by
  decide +kernel

theorem ray_chain_39 : (List.range 1024).all (fun i => rayChainCell (1024 * 39 + i)) = true := by
  decide +kernel

theorem ray_chain_40 : (List.range 1024).all (fun i => rayChainCell (1024 * 40 + i)) = true := by
  decide +kernel

theorem ray_chain_41 : (List.range 1024).all (fun i => rayChainCell (1024 * 41 + i)) = true := by
  decide +kernel

theorem ray_chain_42 : (List.range 1024).all (fun i => rayChainCell (1024 * 42 + i)) = true := by
  decide +kernel

theorem ray_chain_43 : (List.range 1024).all (fun i => rayChainCell (1024 * 43 + i)) = true := by
  decide +kernel

theorem ray_chain_44 : (List.range 1024).all (fun i => rayChainCell (1024 * 44 + i)) = true := by
  decide +kernel

theorem ray_chain_45 : (List.range 1024).all (fun i => rayChainCell (1024 * 45 + i)) = true := by
  decide +kernel

theorem ray_chain_46 : (List.range 1024).all (fun i => rayChainCell (1024 * 46 + i)) = true := by
  decide +kernel

theorem ray_chain_47 : (List.range 1024).all (fun i => rayChainCell (1024 * 47 + i)) = true := by
  decide +kernel

theorem ray_chain_48 : (List.range 1024).all (fun i => rayChainCell (1024 * 48 + i)) = true := by
  decide +kernel

theorem ray_chain_49 : (List.range 1024).all (fun i => rayChainCell (1024 * 49 + i)) = true := by
  decide +kernel

theorem ray_chain_50 : (List.range 1024).all (fun i => rayChainCell (1024 * 50 + i)) = true := by
  decide +kernel

theorem ray_chain_51 : (List.range 1024).all (fun i => rayChainCell (1024 * 51 + i)) = true := by
  decide +kernel

theorem ray_chain_52 : (List.range 1024).all (fun i => rayChainCell (1024 * 52 + i)) = true := by
  decide +kernel

theorem ray_chain_53 : (List.range 1024).all (fun i => rayChainCell (1024 * 53 + i)) = true := by
  decide +kernel

theorem ray_chain_54 : (List.range 1024).all (fun i => rayChainCell (1024 * 54 + i)) = true := by
  decide +kernel

theorem ray_chain_55 : (List.range 1024).all (fun i => rayChainCell (1024 * 55 + i)) = true := by
  decide +kernel

theorem ray_chain_56 : (List.range 1024).all (fun i => rayChainCell (1024 * 56 + i)) = true := by
  decide +kernel

theorem ray_chain_57 : (List.range 1024).all (fun i => rayChainCell (1024 * 57 + i)) = true := by
  decide +kernel

theorem ray_chain_58 : (List.range 1024).all (fun i => rayChainCell (1024 * 58 + i)) = true := by
  decide +kernel

theorem ray_chain_59 : (List.range 1024).all (fun i => rayChainCell (1024 * 59 + i)) = true := by
  decide +kernel

theorem ray_chain_60 : (List.range 1024).all (fun i => rayChainCell (1024 * 60 + i)) = true := by
  decide +kernel

theorem ray_chain_61 : (List.range 1024).all (fun i => rayChainCell (1024 * 61 + i)) = true := by
  decide +kernel

theorem ray_chain_62 : (List.range 1024).all (fun i => rayChainCell (1024 * 62 + i)) = true := by
  decide +kernel

theorem ray_chain_63 : (List.range 1024).all (fun i => rayChainCell (1024 * 63 + i)) = true := by
  decide +kernel

theorem ray_chain_64 : (List.range 1024).all (fun i => rayChainCell (1024 * 64 + i)) = true := by
  decide +kernel

theorem ray_chain_65 : (List.range 1024).all (fun i => rayChainCell (1024 * 65 + i)) = true := by
  decide +kernel

theorem ray_chain_66 : (List.range 1024).all (fun i => rayChainCell (1024 * 66 + i)) = true := by
  decide +kernel

theorem ray_chain_67 : (List.range 1024).all (fun i => rayChainCell (1024 * 67 + i)) = true := by
  decide +kernel

theorem ray_geom : ∀ m < 68, (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * m + i))) = true := by
  intro m hm
  interval_cases m
  exacts [ray_geom_0, ray_geom_1, ray_geom_2, ray_geom_3, ray_geom_4, ray_geom_5, ray_geom_6, ray_geom_7, ray_geom_8, ray_geom_9, ray_geom_10, ray_geom_11, ray_geom_12, ray_geom_13, ray_geom_14, ray_geom_15, ray_geom_16, ray_geom_17, ray_geom_18, ray_geom_19, ray_geom_20, ray_geom_21, ray_geom_22, ray_geom_23, ray_geom_24, ray_geom_25, ray_geom_26, ray_geom_27, ray_geom_28, ray_geom_29, ray_geom_30, ray_geom_31, ray_geom_32, ray_geom_33, ray_geom_34, ray_geom_35, ray_geom_36, ray_geom_37, ray_geom_38, ray_geom_39, ray_geom_40, ray_geom_41, ray_geom_42, ray_geom_43, ray_geom_44, ray_geom_45, ray_geom_46, ray_geom_47, ray_geom_48, ray_geom_49, ray_geom_50, ray_geom_51, ray_geom_52, ray_geom_53, ray_geom_54, ray_geom_55, ray_geom_56, ray_geom_57, ray_geom_58, ray_geom_59, ray_geom_60, ray_geom_61, ray_geom_62, ray_geom_63, ray_geom_64, ray_geom_65, ray_geom_66, ray_geom_67]

theorem ray_chain : ∀ m < 68, (List.range 1024).all (fun i => rayChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [ray_chain_0, ray_chain_1, ray_chain_2, ray_chain_3, ray_chain_4, ray_chain_5, ray_chain_6, ray_chain_7, ray_chain_8, ray_chain_9, ray_chain_10, ray_chain_11, ray_chain_12, ray_chain_13, ray_chain_14, ray_chain_15, ray_chain_16, ray_chain_17, ray_chain_18, ray_chain_19, ray_chain_20, ray_chain_21, ray_chain_22, ray_chain_23, ray_chain_24, ray_chain_25, ray_chain_26, ray_chain_27, ray_chain_28, ray_chain_29, ray_chain_30, ray_chain_31, ray_chain_32, ray_chain_33, ray_chain_34, ray_chain_35, ray_chain_36, ray_chain_37, ray_chain_38, ray_chain_39, ray_chain_40, ray_chain_41, ray_chain_42, ray_chain_43, ray_chain_44, ray_chain_45, ray_chain_46, ray_chain_47, ray_chain_48, ray_chain_49, ray_chain_50, ray_chain_51, ray_chain_52, ray_chain_53, ray_chain_54, ray_chain_55, ray_chain_56, ray_chain_57, ray_chain_58, ray_chain_59, ray_chain_60, ray_chain_61, ray_chain_62, ray_chain_63, ray_chain_64, ray_chain_65, ray_chain_66, ray_chain_67]

theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 15 * 2 ^ 40 ≤ 4 * (rayCellG 69631).2.2.2 := by
  decide +kernel

lemma ray_geom' (i : ℕ) (hi : i < 69632) :
    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧
    50 * (rayCellG i).1 ≤ -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.2 - 51200 ∧
    -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.1 + 51200 ≤ 50 * (rayCellG i).2.1 := by
  have h := List.all_eq_true.mp (ray_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [rayGeomCell] using h

lemma ray_chain' (i : ℕ) (hi : i + 1 < 69632) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by
  have h := List.all_eq_true.mp (ray_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [rayChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanCore.Cert.SigmaHybS
