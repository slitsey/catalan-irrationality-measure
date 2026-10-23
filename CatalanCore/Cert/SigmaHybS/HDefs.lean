module

public import CatalanCore.Cert.SigmaHybS.SegLine
public import CatalanCore.Cert.SigmaHybS.Macro

@[expose] public section

/-!
# Definitions of the hybrid macro checks (slim import closure for the data modules)

Only definitions live here (so that the `decide +kernel` data modules do not import the heavy soundness
chain): `UbUp`/`UexUp`/`UexAxisUp` (copies of `SigmaHyb.UBox`/`HBox`/`HMacro`, shown `rfl`-equal in `HMacro`),
`gMacroOK` (ray cells, stride `4+4M`) and `realMacroOKH` (real-axis cells, stride `4+3M`).
-/

namespace CatalanCore.Cert.SigmaHybS

open CatalanLambda.Cert (thetaQ)

set_option maxRecDepth 100000

def L2UP : ℚ := 6931471808 / 10 ^ 10

def UbUp (xlo xhi ylo yhi : ℤ) : ℚ :=
  let L1 := L1Q xlo yhi
  let Aup : ℚ := (1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1) ((-(xlo : ℚ) / 2 ^ 40) * L1)
  let l := lQ xhi ylo
  let Bup : ℚ := -(1 / 2) * qmin ((((2 : ℚ) ^ 40 - xhi) / 2 ^ 40) * l)
    ((((2 : ℚ) ^ 40 - xlo) / 2 ^ 40) * l)
  let th := thetaQ (vloQ xlo ylo yhi)
  let Cup : ℚ := -qmin ((ylo : ℚ) / 2 ^ 40 * th) ((yhi : ℚ) / 2 ^ 40 * th)
  1 + Aup + Bup + Cup

def UexUp (xlo xhi ylo yhi : ℤ) : ℚ :=
  (1 / 8) * UbUp (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) (4 * ylo) (4 * yhi) + L2UP / 4

def UexAxisUp (xlo xhi : ℤ) : ℚ :=
  (1 / 8) * (if xhi = 2 ^ 40 then utA (4 * xlo - 2 ^ 42) 0
    else UbUp (4 * xlo - 2 ^ 42) (4 * xhi - 2 ^ 42) 0 0) + L2UP / 4

def sideLine (xlo xhi : ℤ) : Prop :=
  0 ≤ xlo ∧ xlo ≤ xhi ∧ xhi ≤ 2 ^ 40 ∧ (xhi = 2 ^ 40 → 3 * 2 ^ 38 ≤ xlo)

instance (xlo xhi : ℤ) : Decidable (sideLine xlo xhi) := by unfold sideLine; infer_instance

def boxLBH (Ls : ℚ) (xlo xhi ylo yhi : ℤ) : ℚ := boxLBg Ls xlo xhi ylo yhi - UexUp xlo xhi ylo yhi

def gMacroOK (L : List Pt) (mp : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 4 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (L.take i0 ++ L.drop i1)
  let mid := (L.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 4 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let ylo := slot P (a + 2)
    let yhi := slot P (a + 3)
    decide (xhi < 0 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
      decide (mp ≤ boxLBH (sigTL x0 y0 fd xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid)) xlo xhi ylo yhi))

/-! ### real axis -/

def sideReal (xlo xhi : ℤ) : Prop :=
  xlo ≤ xhi ∧ ((xhi ≤ 0 ∧ -(2 ^ 40 : ℤ) ≤ xlo) ∨ (0 ≤ xlo ∧ xhi ≤ 2 ^ 40)) ∧
    (xhi ≤ 0 ∨ sideLine xlo xhi)

instance (xlo xhi : ℤ) : Decidable (sideReal xlo xhi) := by unfold sideReal; infer_instance

def UexAx (xlo xhi : ℤ) : ℚ := if xhi ≤ 0 then UexUp xlo xhi 0 0 else UexAxisUp xlo xhi

def realLBH (x0 y0 : ℤ) (fd : FD) (mid : List Pt) (xlo xhi : ℤ) : ℚ :=
  sigTL x0 y0 fd xlo xhi 0 0 (sigSum xlo xhi 0 0 mid) - (if xhi ≤ 0 then utA xlo xhi else utB xlo xhi)
    - UexAx xlo xhi

def realCell (M P j c : ℕ) : ℤ × ℤ × ℤ :=
  let a := j * (4 + 3 * M) + 4 + 3 * c
  (slot P a, slot P (a + 1), slot P (a + 2))

/-- threshold of cell `c` of macro `j`: `γ/2^32` in segment mode, the constant `G` otherwise. -/
def realThr (mode : Bool) (G : ℚ) (M P j c : ℕ) : ℚ :=
  if mode then ((realCell M P j c).2.2 : ℚ) / 2 ^ 32 else G

def realMacroOKH (L : List Pt) (mode : Bool) (G : ℚ) (M P j : ℕ) : Bool :=
  let b := j * (4 + 3 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let fd := farSum x0 y0 (L.take i0 ++ L.drop i1)
  let mid := (L.drop i0).take (i1 - i0)
  decide (i0 ≤ i1) && (List.range M).all (fun c =>
    let a := b + 4 + 3 * c
    let xlo := slot P a
    let xhi := slot P (a + 1)
    let gam := slot P (a + 2)
    decide (sideReal xlo xhi) &&
      decide ((if mode then (gam : ℚ) / 2 ^ 32 else G) ≤ realLBH x0 y0 fd mid xlo xhi))

end CatalanCore.Cert.SigmaHybS
