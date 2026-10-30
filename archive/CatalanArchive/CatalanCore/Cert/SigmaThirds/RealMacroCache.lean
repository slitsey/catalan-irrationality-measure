module

public import CatalanCore.Cert.SigmaHybS.HDefs

@[expose] public section

/-!
# Exact cached decomposition of the real-axis hybrid macro checker

Segment and line thresholds, side guards and near-point calculations are unchanged.
Only the far-field tuple is supplied explicitly after an equality check.
-/

namespace CatalanCore.Cert.SigmaThirds

open CatalanCore.Cert.SigmaHybS

/-- One cell of `realMacroOKH`, with an explicitly supplied far-field tuple. -/
def cachedRealCellOK (L : List Pt) (mode : Bool) (G : ℚ) (M P j c : ℕ) (fd : FD) : Bool :=
  let b := j * (4 + 3 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let mid := (L.drop i0).take (i1 - i0)
  let a := b + 4 + 3 * c
  let xlo := slot P a
  let xhi := slot P (a + 1)
  let gam := slot P (a + 2)
  decide (sideReal xlo xhi) &&
    decide ((if mode then (gam : ℚ) / 2 ^ 32 else G) ≤ realLBH x0 y0 fd mid xlo xhi)

/-- The explicit tuple gives an exactly equal real-axis checker. -/
theorem realMacroOKH_eq_cached (L : List Pt) (mode : Bool) (G : ℚ) (M P j : ℕ) (fd : FD)
    (hfd : farSum (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
      (L.take (slot P (j * (4 + 3 * M) + 2)).toNat ++
        L.drop (slot P (j * (4 + 3 * M) + 3)).toNat) = fd) :
    realMacroOKH L mode G M P j =
      (decide ((slot P (j * (4 + 3 * M) + 2)).toNat ≤
          (slot P (j * (4 + 3 * M) + 3)).toNat) &&
        (List.range M).all (fun c => cachedRealCellOK L mode G M P j c fd)) := by
  simp only [realMacroOKH, cachedRealCellOK, hfd]

/-- Assemble separate real-cell checks into the existing `realMacroOKH`. -/
theorem realMacroOKH_of_cached (L : List Pt) (mode : Bool) (G : ℚ) (M P j : ℕ) (fd : FD)
    (hfd : farSum (slot P (j * (4 + 3 * M))) (slot P (j * (4 + 3 * M) + 1))
      (L.take (slot P (j * (4 + 3 * M) + 2)).toNat ++
        L.drop (slot P (j * (4 + 3 * M) + 3)).toNat) = fd)
    (hi : (slot P (j * (4 + 3 * M) + 2)).toNat ≤
      (slot P (j * (4 + 3 * M) + 3)).toNat)
    (hcells : ∀ c < M, cachedRealCellOK L mode G M P j c fd = true) :
    realMacroOKH L mode G M P j = true := by
  rw [realMacroOKH_eq_cached L mode G M P j fd hfd, Bool.and_eq_true]
  constructor
  · simpa only [decide_eq_true_eq] using hi
  · apply List.all_eq_true.mpr
    intro c hc
    exact hcells c (List.mem_range.mp hc)

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.realMacroOKH_eq_cached
#print axioms CatalanCore.Cert.SigmaThirds.realMacroOKH_of_cached