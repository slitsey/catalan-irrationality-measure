module

public import CatalanCore.Cert.SigmaHyb.HA0
public import CatalanCore.Cert.SigmaHyb.HA1
public import CatalanCore.Cert.SigmaHyb.HA2
public import CatalanCore.Cert.SigmaHyb.HA3
public import CatalanCore.Cert.SigmaHyb.GB0
public import CatalanCore.Cert.SigmaHyb.RayRef
public import CatalanCore.Cert.SigmaHyb.HBridge
public import CatalanLambda.Cert.Final

@[expose] public section

/-!
# Hybrid ray cells: boxes, cover

`rayBoxesH` = (common refinement of the legacy ray cells and the coarse h-cells on `[0, YEND]`)
`++` (fresh hybrid cells `GB0` on `[YEND, 3/2]`).
* refinement cell `t` lies in the legacy cell `I t` (so `g_sq ≥ MPRAY` there, legacy `ray_box_ok_thm`)
  and in the coarse h-cell `J t` (so `h ≥ γ_J / 2^32`);  `MPRAY + γ/2^32 ≥ 22147/10000`.
* the fresh cells are checked for `g_h` directly (`gMacroOK hybS`).
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def u16 (P i : ℕ) : ℕ := (P >>> (16 * i)) % 2 ^ 16
def refY (t : ℕ) : ℤ := slot refBY t

def AP : ℕ → ℕ
  | 0 => HA0P
  | 1 => HA1P
  | 2 => HA2P
  | 3 => HA3P
  | _ => 0

theorem aAll : ∀ m < 4, ∀ j < 8, hMacroOK lamS 32 (AP m) j = true := by
  intro m hm
  interval_cases m
  exacts [HA0_ok, HA1_ok, HA2_ok, HA3_ok]

def aBox (g : ℕ) : ℤ × ℤ × ℤ × ℤ := hCellBox 32 (AP (g / 256)) ((g % 256) / 32) (g % 32)
def aGam (g : ℕ) : ℤ := hCellGam 32 (AP (g / 256)) ((g % 256) / 32) (g % 32)

theorem aSound (g : ℕ) (hg : g < 1024) (x y : ℝ)
    (h1 : ((aBox g).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((aBox g).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((aBox g).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((aBox g).2.2.2 : ℝ) / 2 ^ 40) :
    (((aGam g : ℤ) : ℝ) / 2 ^ 32) ≤ Usig lamS x y - UexR x y := by
  have := hMod_sound lamS 32 (AP (g / 256)) 8 (aAll (g / 256) (by omega)) ((g % 256) / 32)
    (by omega) (g % 32) (by omega) x y h1 h2 h3 h4
  simpa [aGam] using this

def GP : ℕ → ℕ
  | 0 => GB0P
  | _ => 0

theorem bAll : ∀ j < 8, gMacroOK hybS (22147 / 10000 : ℚ) 32 GB0P j = true := GB0_ok

def bBox (k : ℕ) : ℤ × ℤ × ℤ × ℤ := hCellBox 32 GB0P (k / 32) (k % 32)

theorem bSound (k : ℕ) (hk : k < 256) (x y : ℝ)
    (h1 : ((bBox k).1 : ℝ) / 2 ^ 40 ≤ x) (h2 : x ≤ ((bBox k).2.1 : ℝ) / 2 ^ 40)
    (h3 : ((bBox k).2.2.1 : ℝ) / 2 ^ 40 ≤ y) (h4 : y ≤ ((bBox k).2.2.2 : ℝ) / 2 ^ 40) :
    (((22147 / 10000 : ℚ)) : ℝ) ≤ gHR hybS x y :=
  gMod_sound hybS (22147 / 10000 : ℚ) 32 GB0P 8 bAll (k / 32) (by omega) (k % 32) (by omega) x y h1 h2 h3 h4

/-- refinement cell `t` of the region A. -/
def refOK (t : ℕ) : Bool :=
  let I := u16 refI t
  let J := u16 refJ t
  let b0 := refY t
  let b1 := refY (t + 1)
  decide (b0 ≤ b1 ∧ I < 27648 ∧ J < 901) &&
    decide ((rayCellG I).2.2.1 ≤ b0 ∧ b1 ≤ (rayCellG I).2.2.2) &&
    decide ((aBox J).2.2.1 ≤ b0 ∧ b1 ≤ (aBox J).2.2.2 ∧
      150 * (aBox J).1 ≤ -21 * 2 ^ 40 - 50 * b1 - 153600 ∧
      -21 * 2 ^ 40 - 50 * b0 + 153600 ≤ 150 * (aBox J).2.1)

def refChunk (m : ℕ) : Bool :=
  (List.range 2600).all (fun i => decide (NR ≤ 2600 * m + i) || refOK (2600 * m + i))

theorem refc_0 : refChunk 0 = true := by decide +kernel
theorem refc_1 : refChunk 1 = true := by decide +kernel
theorem refc_2 : refChunk 2 = true := by decide +kernel
theorem refc_3 : refChunk 3 = true := by decide +kernel
theorem refc_4 : refChunk 4 = true := by decide +kernel
theorem refc_5 : refChunk 5 = true := by decide +kernel
theorem refc_6 : refChunk 6 = true := by decide +kernel
theorem refc_7 : refChunk 7 = true := by decide +kernel
theorem refc_8 : refChunk 8 = true := by decide +kernel
theorem refc_9 : refChunk 9 = true := by decide +kernel

theorem ref_check : ∀ m < 10, refChunk m = true := by
  intro m hm
  interval_cases m
  exacts [refc_0, refc_1, refc_2, refc_3, refc_4, refc_5, refc_6, refc_7, refc_8, refc_9]

def gamOK (J : ℕ) : Bool :=
  decide ((197179 / 100000 : ℚ) + (aGam J : ℚ) / 2 ^ 32 ≥ 22147 / 10000)

theorem gam_check : (List.range 901).all gamOK = true := by decide +kernel

def bOK (k : ℕ) : Bool :=
  let b := bBox k
  decide (0 ≤ b.2.2.1 ∧ b.2.2.1 ≤ b.2.2.2 ∧ b.2.1 < 0 ∧
      150 * b.1 ≤ -21 * 2 ^ 40 - 50 * b.2.2.2 - 153600 ∧
      -21 * 2 ^ 40 - 50 * b.2.2.1 + 153600 ≤ 150 * b.2.1)

def bChain (k : ℕ) : Bool :=
  decide (228 ≤ k + 1 ∨ (bBox (k + 1)).2.2.1 ≤ (bBox k).2.2.2)

theorem b_check : (List.range 228).all bOK = true := by decide +kernel
theorem b_chain : (List.range 228).all bChain = true := by decide +kernel
theorem b_ends : (bBox 0).2.2.1 ≤ (YENDR : ℤ) ∧ 9 * 2 ^ 40 ≤ 2 * (bBox 227).2.2.2 := by decide +kernel
theorem ref_ends : refY 0 = 0 ∧ refY NR = (YENDR : ℤ) := by decide +kernel

end CatalanCore.Cert.SigmaHyb
