module

public import CatalanCore.Uniform.Content.UFFamily.KillOfTypes

@[expose] public section

/-!
# UF families: nodes with an empty core fiber (lane H10)

If the core nodes are all `< r` and a node `t` satisfies `r ≤ t < p`, no core node is congruent to `t`
modulo `p`: the fiber is EMPTY, the joint type is `⟨[], (0, ⌊(q t - o)/p⌋)⟩`, and the bordered
determinants are `A = z`, `B = Dn`.  `fiberList_empty` is the `FiberList`, `crossZ_empty` the integer
cross wedge `DJ · z_K - z_J · DK`, `ShiftData.refl` the trivial run shift (every node is the start of
its own run).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem fiberList_empty_aux {r : ℕ} (c : ι → ℕ) (hcr : ∀ a, c a < r) {t : ℕ} (hrt : r ≤ t)
    (htp : t < p) (a : ι) : ((c a : ℕ) : ZMod p) ≠ ((t : ℕ) : ZMod p) := by
  intro h
  have h1 := (ZMod.natCast_eq_natCast_iff' _ _ p).1 h
  have := hcr a
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt htp] at h1
  omega

/-- **The empty fiber.** -/
def fiberList_empty {r : ℕ} (c : ι → ℕ) (hcr : ∀ a, c a < r) {t : ℕ} (hrt : r ≤ t) (htp : t < p) :
    FiberList p q o c t ⟨[], (0, (q * t - o) / p)⟩ where
  g := fun i => Fin.elim0 i
  hg := fun i => Fin.elim0 i
  hcol := fun i => Fin.elim0 i
  hsurj := fun a h => absurd h (fiberList_empty_aux c hcr hrt htp a)
  hne := fun i => Fin.elim0 i
  hnode := fun i => Fin.elim0 i
  hzone := by
    show ((0 : ℕ), (q * t - o) / p) = (t / p, (q * t - o) / p)
    rw [Nat.div_eq_of_lt htp]

/-- The cross wedge of two empty-fiber types. -/
theorem crossZ_empty (DJ DK : ℤ) (J K : IntFib 0) :
    crossZ 0 0 DJ DK J K = DJ * K.z - J.z * DK := by
  simp [crossZ, fibZ, detN, sumN, IntFib.toB]

/-- Every node is the start of its own run. -/
theorem shiftData_refl (D : PoleData Fr p N) (c : ι → ℕ) (t : ℕ) : ShiftData D c t t :=
  ⟨0, rfl, fun k h1 h2 => by omega, Equiv.refl _, fun i => rfl, fun i k h1 h2 => by omega⟩

end CatalanCore.Uniform.Content.UFFamily
