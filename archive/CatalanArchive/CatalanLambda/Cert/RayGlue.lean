module

public import CatalanLambda.Cert.RayM0
public import CatalanLambda.Cert.RayM1
public import CatalanLambda.Cert.RayM2
public import CatalanLambda.Cert.RayM3
public import CatalanLambda.Cert.RayM4
public import CatalanLambda.Cert.RayM5
public import CatalanLambda.Cert.RayM6
public import CatalanLambda.Cert.RayM7
public import CatalanLambda.Cert.RayM8
public import CatalanLambda.Cert.RayM9
public import CatalanLambda.Cert.RayM10
public import CatalanLambda.Cert.RayM11
public import CatalanLambda.Cert.RayM12
public import CatalanLambda.Cert.RayM13
public import CatalanLambda.Cert.RayM14
public import CatalanLambda.Cert.RayM15
public import CatalanLambda.Cert.RayM16
public import CatalanLambda.Cert.RayM17
public import CatalanLambda.Cert.RayM18
public import CatalanLambda.Cert.RayM19
public import CatalanLambda.Cert.RayM20
public import CatalanLambda.Cert.RayM21
public import CatalanLambda.Cert.RayM22
public import CatalanLambda.Cert.RayM23
public import CatalanLambda.Cert.RayM24
public import CatalanLambda.Cert.RayM25
public import CatalanLambda.Cert.RayM26
public import CatalanLambda.Cert.Bridge

@[expose] public section

/-!
# Glue for the ray cells: global indexing of the 27 modules (27648 = 864 macros x 32 cells),
geometry (the cell box contains the CertFacts box of its `u`-interval), chain (cover of `[0,3/2]`).
-/

open Real

namespace CatalanLambda.Cert

set_option maxRecDepth 100000

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
  | _ => 0

theorem rayAll_ok : ∀ m < 27, ∀ j < 32, rayMacroOK MPRAY 32 (rayP m) j = true := by
  intro m hm
  interval_cases m
  exacts [RayM0_ok, RayM1_ok, RayM2_ok, RayM3_ok, RayM4_ok, RayM5_ok, RayM6_ok, RayM7_ok, RayM8_ok, RayM9_ok, RayM10_ok, RayM11_ok, RayM12_ok, RayM13_ok, RayM14_ok, RayM15_ok, RayM16_ok, RayM17_ok, RayM18_ok, RayM19_ok, RayM20_ok, RayM21_ok, RayM22_ok, RayM23_ok, RayM24_ok, RayM25_ok, RayM26_ok]

def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ := cellBox 32 (rayP (i / 1024)) ((i % 1024) / 32) (i % 32)

theorem ray_sound (i : ℕ) (hi : i < 27648) (x y : ℝ)
    (h1 : ((rayCellG i).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((rayCellG i).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((rayCellG i).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((rayCellG i).2.2.2 : ℝ) / 2 ^ 40) :
    (MPRAY : ℝ) ≤ gfun sigmaS x y :=
  rayMod_sound MPRAY 32 (rayP (i / 1024)) 32 (rayAll_ok (i / 1024) (by omega)) ((i % 1024) / 32)
    (by omega) (i % 32) (by omega) x y h1 h2 h3 h4

def geomCell (b : ℤ × ℤ × ℤ × ℤ) : Bool :=
  decide (b.2.1 < 0 ∧ 0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧
    150 * b.1 ≤ -21 * 2 ^ 40 - 50 * b.2.2.2 - 153600 ∧
    -21 * 2 ^ 40 - 50 * b.2.2.1 + 153600 ≤ 150 * b.2.1)

def rayChainCell (i : ℕ) : Bool :=
  decide (27648 ≤ i + 1 ∨ (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2)

theorem ray_geom : ∀ m < 27, (List.range 1024).all (fun i => geomCell (rayCellG (1024 * m + i))) = true := by
  decide +kernel

theorem ray_chain : ∀ m < 27, (List.range 1024).all (fun i => rayChainCell (1024 * m + i)) = true := by
  decide +kernel

theorem ray_ends : (rayCellG 0).2.2.1 = 0 ∧ 9 * 2 ^ 40 ≤ 2 * (rayCellG 27647).2.2.2 := by
  decide +kernel

lemma ray_geom' (i : ℕ) (hi : i < 27648) :
    (rayCellG i).2.1 < 0 ∧ 0 ≤ (rayCellG i).2.2.1 ∧ (rayCellG i).2.2.1 ≤ (rayCellG i).2.2.2 ∧
    150 * (rayCellG i).1 ≤ -21 * 2 ^ 40 - 50 * (rayCellG i).2.2.2 - 153600 ∧
    -21 * 2 ^ 40 - 50 * (rayCellG i).2.2.1 + 153600 ≤ 150 * (rayCellG i).2.1 := by
  have h := List.all_eq_true.mp (ray_geom (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simpa [geomCell] using h

lemma ray_chain' (i : ℕ) (hi : i + 1 < 27648) : (rayCellG (i + 1)).2.2.1 ≤ (rayCellG i).2.2.2 := by
  have h := List.all_eq_true.mp (ray_chain (i / 1024) (by omega)) (i % 1024) (List.mem_range.mpr (by omega))
  have e : 1024 * (i / 1024) + i % 1024 = i := by omega
  rw [e] at h
  simp only [rayChainCell, decide_eq_true_eq] at h
  rcases h with h | h
  · omega
  · exact h

end CatalanLambda.Cert
