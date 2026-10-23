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
public import CatalanCore.Cert.SigmaHybS.Bridge

@[expose] public section

/-!
# Glue for the ray cells: global indexing of the 30 modules (30720 cells), geometry (the cell box contains the tube of its `u`-interval), chain (cover of `[0,3/2]`).
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
  | 26 => 16
  | 27 => 64
  | 28 => 64
  | 29 => 64
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
  | _ => 0

theorem rayAll_ok : ∀ m < 30, ∀ j < 1024 / rayM m, gMacroOK sigH MPRAY (rayM m) (rayP m) j = true := by
  intro m hm
  interval_cases m
  exacts [RayM0_ok, RayM1_ok, RayM2_ok, RayM3_ok, RayM4_ok, RayM5_ok, RayM6_ok, RayM7_ok, RayM8_ok, RayM9_ok, RayM10_ok, RayM11_ok, RayM12_ok, RayM13_ok, RayM14_ok, RayM15_ok, RayM16_ok, RayM17_ok, RayM18_ok, RayM19_ok, RayM20_ok, RayM21_ok, RayM22_ok, RayM23_ok, RayM24_ok, RayM25_ok, RayM26_ok, RayM27_ok, RayM28_ok, RayM29_ok]

theorem rayM_pos (m : ℕ) : 0 < rayM m := by
  unfold rayM; split <;> norm_num

theorem rayM_dvd (m : ℕ) (hm : m < 30) : rayM m ∣ 1024 := by
  interval_cases m <;> decide

def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  cellBox (rayM (i / 1024)) (rayP (i / 1024)) ((i % 1024) / rayM (i / 1024)) (i % rayM (i / 1024))

theorem ray_sound (i : ℕ) (hi : i < 30720) (x y : ℝ)
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
  decide (30720 ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)

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

theorem ray_geom : ∀ m < 30, (List.range 1024).all (fun i => rayGeomCell (rayCellG (1024 * m + i))) = true := by
  intro m hm
  interval_cases m
  exacts [ray_geom_0, ray_geom_1, ray_geom_2, ray_geom_3, ray_geom_4, ray_geom_5, ray_geom_6, ray_geom_7, ray_geom_8, ray_geom_9, ray_geom_10, ray_geom_11, ray_geom_12, ray_geom_13, ray_geom_14, ray_geom_15, ray_geom_16, ray_geom_17, ray_geom_18, ray_geom_19, ray_geom_20, ray_geom_21, ray_geom_22, ray_geom_23, ray_geom_24, ray_geom_25, ray_geom_26, ray_geom_27, ray_geom_28, ray_geom_29]

theorem ray_chain : ∀ m < 30, (List.range 1024).all (fun i => rayChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [ray_chain_0, ray_chain_1, ray_chain_2, ray_chain_3, ray_chain_4, ray_chain_5, ray_chain_6, ray_chain_7, ray_chain_8, ray_chain_9, ray_chain_10, ray_chain_11, ray_chain_12, ray_chain_13, ray_chain_14, ray_chain_15, ray_chain_16, ray_chain_17, ray_chain_18, ray_chain_19, ray_chain_20, ray_chain_21, ray_chain_22, ray_chain_23, ray_chain_24, ray_chain_25, ray_chain_26, ray_chain_27, ray_chain_28, ray_chain_29]

theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 15 * 2 ^ 40 ≤ 4 * (rayCellG 30719).2.2.2 := by
  decide +kernel

lemma ray_geom' (i : ℕ) (hi : i < 30720) :
    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧
    50 * (rayCellG i).1 ≤ -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.2 - 51200 ∧
    -7 * 2 ^ 40 - 20 * (rayCellG i).2.2.1 + 51200 ≤ 50 * (rayCellG i).2.1 := by
  have h := List.all_eq_true.mp (ray_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [rayGeomCell] using h

lemma ray_chain' (i : ℕ) (hi : i + 1 < 30720) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by
  have h := List.all_eq_true.mp (ray_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [rayChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanCore.Cert.SigmaHybS
