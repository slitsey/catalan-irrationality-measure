module

public import CatalanCore.Uniform.Content.UFFamily2.Fiber
public import CatalanCore.Uniform.Content.UFFamily2.Lu

@[expose] public section

/-!
# UF families with non-empty fibers: kill certificates from LU records (lane H, H11)

`KillCert.ofLu` is `UFFamily.KillCert.ofTypes` with the cross-wedge hypothesis supplied by two
checked `LuData` records and a prime avoiding their integer cross wedge.  The run start is the node
itself (`shiftData_refl`); a run shift can be passed through `KillCert.ofTypes` directly.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.UFFamily

namespace CatalanCore.Uniform.Content.UFFamily2

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **Kill certificate of the node `v` against `t0` from two named joint types and two LU records.** -/
noncomputable def KillCert.ofLu (T : TwoTermData Fr q o) (hqp : q < p) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N)
    (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (hcinj : Function.Injective c)
    (t0 v : ℕ) (ht0 : t0 < N) (hv : v < N) (u0 : ℤ) (J K : JType) (DJ DK : ℤ)
    (FJ : FiberList p q o c t0 J) (FK : FiberList p q o c v K)
    (hJ : IntOK q o (p % q) Fr.norm u0 J DJ) (hK : IntOK q o (p % q) Fr.norm u0 K DK)
    (XJ XK : LuData)
    (oJ : XJ.ok J.nodes.length (mkFib q o (p % q) Fr.norm u0 J DJ) DJ = true)
    (oK : XK.ok K.nodes.length (mkFib q o (p % q) Fr.norm u0 K DK) DK = true)
    (hnd : ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b) :
    KillCert (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp c xs ys hc hx hy t0 v :=
  KillCert.ofTypes T hqp hNp hsq hnorm hnorm0 c xs ys hc hx hy hcinj t0 v v ht0 hv
    (shiftData_refl _ c v) u0 J K DJ DK FJ FK hJ hK (LuData.crossZ_zmod_ne oJ oK hnd)

end CatalanCore.Uniform.Content.UFFamily2
