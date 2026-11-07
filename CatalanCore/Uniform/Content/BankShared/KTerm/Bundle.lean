module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Content
public import CatalanCore.Arith.Hybrid.PeriodicEntries
public import CatalanFrames.HybCommon.Numer

@[expose] public section
set_option Elab.async false

/-! # The pole bundle of a two-lattice frame (wave H1)

A frame whose entries `Delta k`, `Dsq k` have poles at `p ∣ k`, `p ∣ 3k - ρ`, `p ∣ 2k - 1` (the denominators
`k (3k - ρ) (2k - 1)`; `ρ = 2` for `chi_{-3}`, `ρ ∈ {1, 2}` for the planes `L₃ + tπ²`).  A `KBundle` is
what the window, prefix and tropical branch theorems of the `k`-shift route (`KTerm.Trop`, `.Win`, `.Pre`) use
of such a frame:

* `inst r m`: the hybrid instance at the scale data `(r, m)` with `DiagOK` and the numerology `BadInfo _ 3 2`
  (`L = 3`, bad primes `≤ 3`);
* `pole`: `PoleData Fr p N` for `p ≥ 5`, `3 N < p²`, whose singular set is the three lattices;
* the shifts `(3, ρ)`, `(2, 1)` of the `k`-shift catalogue.

`Bank.Chi3.KContent.Trop` supplies `chi3Bundle`; a plane supplies its own. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic CatalanFrames.HybCommon

/-- The bundle of a two-lattice frame (see the module docstring). -/
structure KBundle where
  Fr : Frame
  ρ : ℕ
  inst : ℕ → ℕ → HybInst Fr
  diagOK : ∀ r m, (inst r m).DiagOK r m
  badInfo : ∀ r m, BadInfo (inst r m) 3 2
  pole : ∀ (p N : ℕ) [Fact p.Prime], 5 ≤ p → 3 * N < p * p → PoleData Fr p N
  singular_iff : ∀ (p N : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (hN : 3 * N < p * p) (t : ℤ),
    (pole p N h5 hN).singular t ↔
      ((p : ℤ) ∣ t ∨ (p : ℤ) ∣ 3 * t - (ρ : ℤ) ∨ (p : ℤ) ∣ 2 * t - 1)

namespace KBundle

/-- The shifts of the `k`-shift catalogue of the bundle: `3 k_A = j p + ρ`, `2 k_B = j p + 1`. -/
def shifts (B : KBundle) : List Shift := [⟨3, B.ρ, 1⟩, ⟨2, 1, 1⟩]

instance (B : KBundle) (r m : ℕ) : (B.inst r m).DiagOK r m := B.diagOK r m

end KBundle

end CatalanCore.Uniform.Content.BankShared.KTerm
