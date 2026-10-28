module

public import CatalanCore.Uniform.Content.UFMember.Expansion
public import CatalanCore.Uniform.Content.UFMoments.Local

@[expose] public section

/-!
# UF moments: `hnum` from the LOCAL second-order function `Φ`

In the Gauss DVR the one-node moments are `α_t = rowMomA/det Q` etc.; on a joint type `J`
the first-order direction is one `d_J`, and the second-order function is defined by

  `β_t = α_t (p d_J + p² Φ(t))`     (rows: `rowMomB = rowMomA (p d + p² Φ)`; columns primed).

`hnum_of_local`: if `res Φ(t) = K + h(t̄)` on the `J` rows and columns, with `h = hDer Ret v`
(the derived frame), then the `J`-block hypothesis `hnum` of `JBlockCauchy.of_moments` /
`JBlockKill.of_moments` holds, with `m_z = ᾱ_z / det Q̄` and `m'_y = ᾱ'_y` (no `λ` bookkeeping).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **`hnum` from local second-order expansions.** -/
theorem hnum_of_local (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (c : ι → ℕ)
    (xs ys : κ → ℕ) (Jr Jc : Finset κ) (dJ : GaussLoc p) (Φ Φ' : κ → GaussLoc p)
    (hr : ∀ z ∈ Jr, algebraMap _ (GaussLoc p) (rowMomB A Fr c xs z) =
      algebraMap _ (GaussLoc p) (rowMomA A z) * (piL p * dJ + piL p ^ 2 * Φ z))
    (hc : ∀ y ∈ Jc, algebraMap _ (GaussLoc p) (colMomB A Fr c ys y) =
      algebraMap _ (GaussLoc p) (colMomA A y) * (piL p * dJ + piL p ^ 2 * Φ' y))
    (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) (K : RatFunc (ZMod p))
    (hΦ : ∀ z ∈ Jr, res p (Φ z) = K + hDer Ret v ((xs z : ℕ) : ZMod p))
    (hΦ' : ∀ y ∈ Jc, res p (Φ' y) = K + hDer Ret v ((ys y : ℕ) : ZMod p))
    (hdet : phiP p A.toBlocks₁₁.det ≠ 0) :
    ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum A Fr c xs ys z y = Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p A.toBlocks₁₁.det *
        (phiP p (rowMomA A z) / phiP p A.toBlocks₁₁.det * phiP p (colMomA A y) *
          (hDer Ret v ((ys y : ℕ) : ZMod p) - hDer Ret v ((xs z : ℕ) : ZMod p))) := by
  intro z hz y hy
  set f := algebraMap (LocRing p)[X] (GaussLoc p)
  have hloc : f (dispNum A Fr c xs ys z y) = piL p ^ 2 *
      (f (rowMomA A z) * f (colMomA A y) * (Φ' y - Φ z)) := by
    rw [dispNum_eq_moments, map_sub, map_mul, map_mul, hr z hz, hc y hy]
    ring
  obtain ⟨q, hq, hres⟩ := dvd_of_local p _ 2 _ hloc
  refine ⟨q, hq, ?_⟩
  rw [hres, map_mul, map_mul, map_sub, hΦ z hz, hΦ' y hy, res_algebraMap, res_algebraMap]
  field_simp
  ring

end CatalanCore.Uniform.Content.UFMoments
