module

public import CatalanCore.Cert.SigmaP6.RayM0
public import CatalanCore.Cert.SigmaP6.RayM1
public import CatalanCore.Cert.SigmaP6.RayM2
public import CatalanCore.Cert.SigmaP6.RayM3
public import CatalanCore.Cert.SigmaP6.RayM4
public import CatalanCore.Cert.SigmaP6.RayM5
public import CatalanCore.Cert.SigmaP6.RayM6
public import CatalanCore.Cert.SigmaP6.RayM7
public import CatalanCore.Cert.SigmaP6.RayM8
public import CatalanCore.Cert.SigmaP6.RayM9
public import CatalanCore.Cert.SigmaP6.RayM10
public import CatalanCore.Cert.SigmaP6.RayM11
public import CatalanCore.Cert.SigmaP6.RayM12
public import CatalanCore.Cert.SigmaP6.Bridge

@[expose] public section

/-!
# Glue for the ray cells: global indexing of the 13 modules (13312 = 416 macros x 32 cells),
geometry (the cell box contains the CertFacts box of its `u`-interval), chain (cover of `[0,3/2]`).
-/

open Real

namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

def rayM : ℕ → ℕ
  | 0 => 32
  | 1 => 32
  | 2 => 32
  | 3 => 32
  | 4 => 32
  | 5 => 32
  | 6 => 32
  | 7 => 32
  | 8 => 32
  | 9 => 16
  | 10 => 32
  | 11 => 32
  | 12 => 32
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
  | _ => 0

theorem rayAll_ok : ∀ m < 13, ∀ j < 1024 / rayM m, rayMacroOK MPRAY (rayM m) (rayP m) j = true := by
  intro m hm
  interval_cases m
  exacts [RayM0_ok, RayM1_ok, RayM2_ok, RayM3_ok, RayM4_ok, RayM5_ok, RayM6_ok, RayM7_ok, RayM8_ok, RayM9_ok, RayM10_ok, RayM11_ok, RayM12_ok]

theorem rayM_pos (m : ℕ) : 0 < rayM m := by
  unfold rayM; split <;> norm_num

theorem rayM_dvd (m : ℕ) (hm : m < 13) : rayM m ∣ 1024 := by
  interval_cases m <;> decide

def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  cellBox (rayM (i / 1024)) (rayP (i / 1024)) ((i % 1024) / rayM (i / 1024)) (i % rayM (i / 1024))

theorem ray_sound (i : ℕ) (hi : i < 13312) (x y : ℝ)
    (h1 : ((rayCellG i).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((rayCellG i).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((rayCellG i).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((rayCellG i).2.2.2 : ℝ) / 2 ^ 40) :
    (MPRAY : ℝ) ≤ gfun sigD x y :=
  rayMod_sound MPRAY (rayM (i / 1024)) (rayP (i / 1024)) (1024 / rayM (i / 1024)) (rayAll_ok (i / 1024) (by omega))
    ((i % 1024) / rayM (i / 1024))
    (Nat.div_lt_div_of_lt_of_dvd (rayM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))) (i % rayM (i / 1024)) (Nat.mod_lt _ (rayM_pos _)) x y h1 h2 h3 h4

def geomCell (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (b.2.1 < 0 ∧ 0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧
    30 * b.1 ≤ -3 * 2 ^ 40 - 10 * b.2.2.2 - 30720 ∧
    -3 * 2 ^ 40 - 10 * b.2.2.1 + 30720 ≤ 30 * b.2.1)

def rayChainCell (i : ℕ) : Bool :=
  decide (13312 ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)

theorem ray_geom_0 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 0 + i))) = true := by
  decide +kernel

theorem ray_geom_1 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 1 + i))) = true := by
  decide +kernel

theorem ray_geom_2 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 2 + i))) = true := by
  decide +kernel

theorem ray_geom_3 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 3 + i))) = true := by
  decide +kernel

theorem ray_geom_4 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 4 + i))) = true := by
  decide +kernel

theorem ray_geom_5 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 5 + i))) = true := by
  decide +kernel

theorem ray_geom_6 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 6 + i))) = true := by
  decide +kernel

theorem ray_geom_7 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 7 + i))) = true := by
  decide +kernel

theorem ray_geom_8 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 8 + i))) = true := by
  decide +kernel

theorem ray_geom_9 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 9 + i))) = true := by
  decide +kernel

theorem ray_geom_10 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 10 + i))) = true := by
  decide +kernel

theorem ray_geom_11 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 11 + i))) = true := by
  decide +kernel

theorem ray_geom_12 : (List.range 1024).all (fun i => geomCell (rayCellG (1024 * 12 + i))) = true := by
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

theorem ray_geom : ∀ m < 13, (List.range 1024).all (fun i => geomCell (rayCellG (1024 * m + i))) = true := by
  intro m hm
  interval_cases m
  exacts [ray_geom_0, ray_geom_1, ray_geom_2, ray_geom_3, ray_geom_4, ray_geom_5, ray_geom_6, ray_geom_7, ray_geom_8, ray_geom_9, ray_geom_10, ray_geom_11, ray_geom_12]

theorem ray_chain : ∀ m < 13, (List.range 1024).all (fun i => rayChainCell (1024 * m + i)) = true := by
  intro m hm
  interval_cases m
  exacts [ray_chain_0, ray_chain_1, ray_chain_2, ray_chain_3, ray_chain_4, ray_chain_5, ray_chain_6, ray_chain_7, ray_chain_8, ray_chain_9, ray_chain_10, ray_chain_11, ray_chain_12]

theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 9 * 2 ^ 40 ≤ 2 * (rayCellG 13311).2.2.2 := by
  decide +kernel

lemma ray_geom' (i : ℕ) (hi : i < 13312) :
    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧
    30 * (rayCellG i).1 ≤ -3 * 2 ^ 40 - 10 * (rayCellG i).2.2.2 - 30720 ∧
    -3 * 2 ^ 40 - 10 * (rayCellG i).2.2.1 + 30720 ≤ 30 * (rayCellG i).2.1 := by
  have h := List.all_eq_true.mp (ray_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [geomCell] using h

lemma ray_chain' (i : ℕ) (hi : i + 1 < 13312) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by
  have h := List.all_eq_true.mp (ray_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [rayChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanCore.Cert.SigmaP6
