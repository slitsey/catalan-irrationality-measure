module

public import CatalanCore.Cert.SigmaHybS.HDefs

@[expose] public section

/-!
# Exact cached decomposition of the existing hybrid macro checker

A far-field tuple is checked once. Each cell is checked in a separate declaration,
then the original `gMacroOK` proposition is reconstructed without changing its guards.
-/

namespace CatalanCore.Cert.SigmaThirds

open CatalanCore.Cert.SigmaHybS

/-- One cell of `gMacroOK`, using an explicitly supplied far-field tuple. -/
def cachedRayCellOK (L : List Pt) (mp : ℚ) (M P j c : ℕ) (fd : FD) : Bool :=
  let b := j * (4 + 4 * M)
  let x0 := slot P b
  let y0 := slot P (b + 1)
  let i0 := (slot P (b + 2)).toNat
  let i1 := (slot P (b + 3)).toNat
  let mid := (L.drop i0).take (i1 - i0)
  let a := b + 4 + 4 * c
  let xlo := slot P a
  let xhi := slot P (a + 1)
  let ylo := slot P (a + 2)
  let yhi := slot P (a + 3)
  decide (xhi < 0 ∧ xlo ≤ xhi ∧ 0 ≤ ylo) &&
    decide (mp ≤ boxLBH (sigTL x0 y0 fd xlo xhi ylo yhi (sigSum xlo xhi ylo yhi mid))
      xlo xhi ylo yhi)

/-- Replacing the computed far tuple by an equal literal is an exact checker equality. -/
theorem gMacroOK_eq_cached (L : List Pt) (mp : ℚ) (M P j : ℕ) (fd : FD)
    (hfd : farSum (slot P (j * (4 + 4 * M))) (slot P (j * (4 + 4 * M) + 1))
      (L.take (slot P (j * (4 + 4 * M) + 2)).toNat ++
        L.drop (slot P (j * (4 + 4 * M) + 3)).toNat) = fd) :
    gMacroOK L mp M P j =
      (decide ((slot P (j * (4 + 4 * M) + 2)).toNat ≤
          (slot P (j * (4 + 4 * M) + 3)).toNat) &&
        (List.range M).all (fun c => cachedRayCellOK L mp M P j c fd)) := by
  simp only [gMacroOK, cachedRayCellOK, hfd]

/-- Assemble separate cell checks into the original hybrid macro checker. -/
theorem gMacroOK_of_cached (L : List Pt) (mp : ℚ) (M P j : ℕ) (fd : FD)
    (hfd : farSum (slot P (j * (4 + 4 * M))) (slot P (j * (4 + 4 * M) + 1))
      (L.take (slot P (j * (4 + 4 * M) + 2)).toNat ++
        L.drop (slot P (j * (4 + 4 * M) + 3)).toNat) = fd)
    (hi : (slot P (j * (4 + 4 * M) + 2)).toNat ≤
      (slot P (j * (4 + 4 * M) + 3)).toNat)
    (hcells : ∀ c < M, cachedRayCellOK L mp M P j c fd = true) :
    gMacroOK L mp M P j = true := by
  rw [gMacroOK_eq_cached L mp M P j fd hfd, Bool.and_eq_true]
  constructor
  · simpa only [decide_eq_true_eq] using hi
  · apply List.all_eq_true.mpr
    intro c hc
    exact hcells c (List.mem_range.mp hc)

end CatalanCore.Cert.SigmaThirds

#print axioms CatalanCore.Cert.SigmaThirds.gMacroOK_eq_cached
#print axioms CatalanCore.Cert.SigmaThirds.gMacroOK_of_cached