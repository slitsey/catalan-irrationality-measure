module

public import CatalanCore.Uniform.Content.UFFamily.Realize
public import CatalanCore.Uniform.Content.UFWedge.Kill

@[expose] public section

/-!
# UF families: kill certificates from joint types (lane H10)

`FiberList` records that a list `J` of floor pairs enumerates the core nodes of the residue fiber of a
node `t`.  `KillCert.ofTypes` turns two such lists (the representative `t₀` and the run start `ts`),
a shift (`ShiftData`) and the single integer inequality `crossZ ≠ 0 mod p` into a `KillCert`,
so that a bank only has to NAME the two joint types, the scalings `DJ DK`, the evaluation point and
check `IntOK` and `crossZ` by the kernel.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The list `J` enumerates the core nodes of the residue fiber of the node `t`, with the floor
data `(⌊c/p⌋, ⌊(q c - o)/p⌋)`. -/
structure FiberList (p q o : ℕ) (c : ι → ℕ) (t : ℕ) (J : JType) where
  g : Fin J.nodes.length → ι
  hg : Function.Injective g
  hcol : ∀ i, ((c (g i) : ℕ) : ZMod p) = ((t : ℕ) : ZMod p)
  hsurj : ∀ a, ((c a : ℕ) : ZMod p) = ((t : ℕ) : ZMod p) → ∃ i, g i = a
  hne : ∀ i, c (g i) ≠ t
  hnode : ∀ i : Fin J.nodes.length, J.node i = (c (g i) / p, (q * c (g i) - o) / p)
  hzone : J.zone = (t / p, (q * t - o) / p)

/-- A nonzero integer not divisible by `p` is nonzero in `𝔽_p`. -/
theorem cast_ne_of_not_dvd {c : ℤ} (h : ¬ (p : ℤ) ∣ c) : (c : ZMod p) ≠ 0 := by
  rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **Kill certificate from two named joint types.** -/
noncomputable def KillCert.ofTypes (T : TwoTermData Fr q o) (hqp : q < p) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N)
    (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (hcinj : Function.Injective c)
    (t0 tv ts : ℕ) (ht0 : t0 < N) (hts : ts < N)
    (hshift : ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0) c ts tv)
    (u0 : ℤ) (J K : JType) (DJ DK : ℤ) (FJ : FiberList p q o c t0 J) (FK : FiberList p q o c ts K)
    (hJ : IntOK q o (p % q) Fr.norm u0 J DJ) (hK : IntOK q o (p % q) Fr.norm u0 K DK)
    (hnz : (crossZ J.nodes.length K.nodes.length DJ DK (mkFib q o (p % q) Fr.norm u0 J DJ)
      (mkFib q o (p % q) Fr.norm u0 K DK) : ZMod p) ≠ 0) :
    KillCert (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp c xs ys hc hx hy t0 tv where
  ts := ts
  hshift := hshift
  u0 := (u0 : ZMod p)
  mJ := J.nodes.length
  mK := K.nodes.length
  DJ := DJ
  DK := DK
  J := mkFib q o (p % q) Fr.norm u0 J DJ
  K := mkFib q o (p % q) Fr.norm u0 K DK
  hJ := nodeFib_realizes T hqp hNp hsq hnorm hnorm0 c xs ys hc hx hy t0 ht0 u0 J DJ FJ.g FJ.hg
    FJ.hcol FJ.hsurj hcinj FJ.hne FJ.hnode FJ.hzone hJ
  hK := nodeFib_realizes T hqp hNp hsq hnorm hnorm0 c xs ys hc hx hy ts hts u0 K DK FK.g FK.hg
    FK.hcol FK.hsurj hcinj FK.hne FK.hnode FK.hzone hK
  hnz := hnz

end CatalanCore.Uniform.Content.UFFamily
