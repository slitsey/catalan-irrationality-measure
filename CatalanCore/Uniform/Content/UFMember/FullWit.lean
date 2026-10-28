module

public import CatalanCore.Uniform.Content.UFMember.SchurDiv
public import CatalanCore.Arith.Hybrid.PeriodicEntries

@[expose] public section

/-!
# UF member package: the Smith witness of the full hybrid matrix from `PoleData`

For a frame with entry-level pole data `PoleData Fr p N` (`N < p²`, H3's `twoTermPoleData` for
two-term frames) and nodes below `N`:

* the pole-square bound `hint` and the cross-fiber bound `hfib` hold (`hint_of_poleData`,
  `hfib_of_poleData`), so O1–O3 are discharged;
* `fullSmithWit`: any two-level data of the divided border Schur complement `schurW` gives a
  scaled-gauge three-level witness of the full matrix, with price
  `2(|C| + m) - (m + a + (a - b))` (`fullSmithWit_price`);
* `TwoLevelData.trivial`: with no kernel data the witness still exists (price `2|C| + m`), a
  sanity instance of the whole pipeline.

The only remaining obligation for the sevenths Smith layer is O4: `TwoLevelData` of `schurW` with
`a = σ_J` and `b = |retained poles|` (via `TwoLevelData.ofFamilies`).
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.UFMember

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

lemma rowNode_lt {c : ι → ℕ} {xs : κ → ℕ} (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N)
    (i : ι ⊕ κ) : rowNode c xs i < N := by
  rcases i with a | a
  · exact hc a
  · exact hx a

lemma colNode_lt {c : ι → ℕ} {ys : κ → ℕ} (hc : ∀ a, c a < N) (hy : ∀ j, ys j < N)
    (j : ι ⊕ κ) : colNode c ys j < N := by
  rcases j with a | a
  · exact hc a
  · exact hy a

/-- The pole-square bound from `PoleData`. -/
theorem hint_of_poleData (D : PoleData Fr p N) (hN : N < p * p) {c : ι → ℕ} {xs ys : κ → ℕ}
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) :
    ∀ i j, (p : ℚ) ^ 2 * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p := fun i j =>
  D.square_mem hN (rowNode_lt hc hx i) (colNode_lt hc hy j)

/-- The cross-fiber bound from `PoleData`. -/
theorem hfib_of_poleData (D : PoleData Fr p N) {c : ι → ℕ} {xs ys : κ → ℕ}
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) :
    ∀ i j, ((rowNode c xs i : ℕ) : ZMod p) ≠ ((colNode c ys j : ℕ) : ZMod p) →
      (p : ℚ) * Fr.Mn (rowNode c xs i) (colNode c ys j) ∈ LocRing p := fun i j h =>
  (D.good_cross (rowNode_lt hc hx i) (colNode_lt hc hy j) (sub_ne_zero.2 (Ne.symm h))).mem

/-- **The Smith witness of the full hybrid matrix** (scaled gauge), from two-level data of the
divided border Schur complement. -/
noncomputable def fullSmithWit (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) {a b : ℕ}
    (T : TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p))
      (schurW c xs ys (hint_of_poleData D hN hc hx hy)) a b) :
    ThreeLevelWit p ((FullN Fr c xs ys (X : ℚ[X])).map (scaleU p)) b :=
  ThreeLevelWit.ofSchurData _ (sLift c xs ys (hint_of_poleData D hN hc hx hy))
    (sLift_hB c xs ys _) (sLift_core_det c xs ys _) _
    (sLift_schur_eq c xs ys _ (hfib_of_poleData D hc hx hy) hdist) T

theorem fullSmithWit_price (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) {a b : ℕ}
    (T : TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p))
      (schurW c xs ys (hint_of_poleData D hN hc hx hy)) a b) :
    (fullSmithWit D hN c xs ys hc hx hy hdist T).price =
      2 * Fintype.card (ι ⊕ κ) - (Fintype.card κ + (a + (a - b))) :=
  ThreeLevelWit.ofSchurData_price _ _ _ _ _ _ T

/-- The empty two-level data (no kernel vectors). -/
noncomputable def TwoLevelData.trivial {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (φ : R →+* K) (π : R) {B : Type*} [Fintype B] [DecidableEq B] (W : Matrix B B R) :
    TwoLevelData φ π W 0 0 where
  L₂ := 1
  P₂ := 1
  s := ∅
  N₂ := 0
  hL₂ := by simp
  hP₂ := by simp
  hrow := by simp
  hcol := by simp
  hN₂ := fun i => absurd i.2 (Finset.notMem_empty _)
  hb := by simp
  hcard := rfl

end CatalanCore.Uniform.Content.UFMember
