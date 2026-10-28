module

public import CatalanCore.Uniform.Decay.PolyCells.Tube
public import CatalanCore.Uniform.Decay.Cert.PilotSevenths

/-!
# Pilot (lane D9): tube cells on the real sevenths polygon

Polygon of `exact-check/hypotheses/hyp.py` (`r0 = 273/2000`, two vertices, NW tail `s = 5000/1353`),
data `sevData` (`m' = 2.1405...`, `ε = 1/1000`).  Far constants `M1 = 2`, `T0 = 3/2` are
illustrative (as in D6: the mass-cancellation hypothesis of the actual frame is not instantiated).
The finite tail segment has `tmax = 1/2`, so beyond it `Im z ≥ 2.05`.

Kernel times (`decide +kernel`, `Elab.async false`, profiler) are recorded in NOTES.
-/

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1
set_option maxRecDepth 100000

namespace CatalanCore.Uniform.Decay.PolyCells.Pilot

open CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cert.Pilot
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Cells

def sevP : RatPolygon where
  r0 := 273 / 2000
  verts := [(-8809027 / 50000000, 787 / 10000), (-11253987 / 50000000, 1041 / 5000)]
  s := 5000 / 1353

def farD : FarData := ⟨2, 3 / 2⟩

/-- The three segments: base → p1, p1 → p2, finite tail. -/
def edgeS : List (Pt × Pt) := edgesAll sevP (1 / 2)

/-- Uniform parameter cells `[i/n, (i+1)/n]`, `i = lo, …, hi-1`. -/
def cellsRange (lo hi n : ℕ) : List (ℚ × ℚ) :=
  (List.range (hi - lo)).map fun i => (((lo + i : ℕ) : ℚ) / n, ((lo + i + 1 : ℕ) : ℚ) / n)

def uniform (n : ℕ) : List (ℚ × ℚ) := cellsRange 0 n n

theorem edges_len : edgeS.length = 3 := by decide +kernel

/-! Far cells on the tail segment (edge 2): `Im ≥ 0.208 + 1.848 τ`, far from `τ ≥ 0.76`. -/
theorem tail_far_one : cellFarOk sevData farD (edgeS.getD 2 default) (3 / 4 + 1 / 32, 1) = true := by
  decide +kernel
theorem tail_far_8 : ((cellsRange 24 32 32).all (cellFarOk sevData farD (edgeS.getD 2 default))) = true := by
  decide +kernel
theorem tail_far_32 : ((cellsRange 50 64 64).all (cellFarOk sevData farD (edgeS.getD 2 default))) = true := by
  decide +kernel
theorem tail_far_rest : farOk sevData farD ((lastPt (basePt sevP) sevP.verts).2 + sevP.s * (1 / 2)) = true := by
  decide +kernel

/-! Covers and the (non-far) polygon edges 0 and 1. -/
theorem cover_64 : coverOk 0 1 (uniform 64) = true := by decide +kernel
theorem edge0_not_far : ((uniform 64).any (cellFarOk sevData farD (edgeS.getD 0 default))) = false := by
  decide +kernel
theorem edge1_not_far : ((uniform 64).any (cellFarOk sevData farD (edgeS.getD 1 default))) = false := by
  decide +kernel

/-- The whole tube pipeline (cover + far arithmetic on every cell of 3 edges x 64 cells), with the
near oracle replaced by `true` (arithmetic timing only: no soundness is claimed). -/
theorem pipeline_timing :
    tubeCellsOk (fun e c => cellFarOk sevData farD e c || true) edgeS
      [uniform 64, uniform 64, uniform 64] = true := by decide +kernel

end CatalanCore.Uniform.Decay.PolyCells.Pilot
