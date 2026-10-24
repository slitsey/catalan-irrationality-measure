module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.Mod3

/-!
# Frame-generic discharge of `ReductionHyp` (DO Prop 1.3, instance level)

`reduction_G`: for a `Frame` `Fr`, prime `ℓ`, threshold `K` with `ModData Fr ℓ K`, and a
geometry `G` with `[0,K) ⊆ C`, all nodes `< ℓ`, `X', Y'` above `K`: if `x ∈ ℤ_(ℓ)` and
`det Full(x) = 0` then `det B(h + x̄/κ) = 0`, where `B` is built from the Cauchy columns of the
absent high nodes (`nd : g → ℕ`, injective with range `absS`) and of `X'`, `Y'`.
`Y₀ = h + x̄/κ` does not depend on `G`.

(Sign convention: `Full` here uses `+Mn`; DO's uses `R = -M0`, so `X_DO = -x`.)
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime] {Fr : Frame}

lemma Ttop_self (ℓ K : ℕ) [Fact ℓ.Prime] : Ttop ℓ K ℓ = 0 := by
  ext a b; simp [Ttop]

/-- **DO Proposition 1.3 (instance, frame-generic).**  The two-level case `T = ℓ` of `reduction_G3`. -/
theorem reduction_G (D : ModData Fr ℓ K) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < ℓ)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {g : Type} [Fintype g] [DecidableEq g] (nd : g → ℕ) (hnd : Function.Injective nd)
    (hab : ∀ n, (∃ i, nd i = n) ↔ n ∈ absS K ℓ G.C G.X' G.Y')
    {x : ℚ} (hx : x ∈ S ℓ) (hdet : (G.Full Fr x).det = 0) :
    (bordered (D.h + red ℓ x / D.κ) (Gcols ℓ K nd) (WX ℓ K G) (WY ℓ K G)).det = 0 := by
  have := reduction_G3 D.toLevels G hlow hlt hhi nd hnd hab hx hdet
  rwa [Ttop_self, smul_zero, add_zero, ← bordered_eq_borderedN] at this

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
