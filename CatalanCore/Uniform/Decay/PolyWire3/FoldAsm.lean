module

public import CatalanCore.Uniform.Decay.PolyWire3.Fold

@[expose] public section
set_option Elab.async false

/-!
# Cons-form assembly of the folded energy table (ledger B05; names of `lean-project-plan/w0/CONTRACT-FOLD.md`)

The generator (`cover.py`, `foldemit.py`) emits the folded energy table one entry per theorem and assembles it
in cons form, as `rowOk_*`, `tabOk_*` do for the plain table.  `eFoldEntry` is `foldEntry`;
`eFoldRow D E cn i j m` checks the entries `(i, j), …, (i, j + m - 1)`, `eFoldTab D E cn i m` the rows
`i, …, m - 1` of length `m`.  `energyFoldOk_of_tab` returns to `energyFoldOk`.
Sibling of `PolyWire3.Fold` (not changed).
-/

namespace CatalanCore.Uniform.Decay.PolyWire3

open Finset CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PairEnergy CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.Cells
  CatalanCore.Uniform.Decay.PolyWire2

/-- One entry of the folded table (contract name for `foldEntry`). -/
def eFoldEntry (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (i j : ℕ) : Bool :=
  foldEntry D E cn i j

theorem eFoldEntry_rep {D : SplineData} {E : List (List ℚ)} {cn : ℕ → ℕ → ℕ × ℕ} {i j : ℕ}
    (hc : cn i j = (i, j)) (hp : pairOk D i j (eOf E i j) = true) : eFoldEntry D E cn i j = true := by
  unfold eFoldEntry foldEntry
  simp [hc, hp]

/-- The entries `(i, j), …, (i, j + m - 1)`. -/
def eFoldRow (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (i j : ℕ) : ℕ → Bool
  | 0 => true
  | m + 1 => eFoldEntry D E cn i j && eFoldRow D E cn i (j + 1) m

theorem eFoldRow_nil (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (i j : ℕ) :
    eFoldRow D E cn i j 0 = true := rfl

theorem eFoldRow_cons {D : SplineData} {E : List (List ℚ)} {cn : ℕ → ℕ → ℕ × ℕ} {i j m : ℕ}
    (h : eFoldEntry D E cn i j = true) (h2 : eFoldRow D E cn i (j + 1) m = true) :
    eFoldRow D E cn i j (m + 1) = true := by
  simp [eFoldRow, h, h2]

theorem eFoldRow_get {D : SplineData} {E : List (List ℚ)} {cn : ℕ → ℕ → ℕ × ℕ} {i : ℕ} :
    ∀ (m j : ℕ), eFoldRow D E cn i j m = true → ∀ k, k < m → eFoldEntry D E cn i (j + k) = true
  | 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | m + 1, j, h, k, hk => by
    simp only [eFoldRow, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := eFoldRow_get m (j + 1) h.2 k (by omega)
      rwa [show j + 1 + k = j + (k + 1) by omega] at this

/-- The rows `i, …, m - 1` (each of length `m`). -/
def eFoldTab (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (i m : ℕ) : Bool :=
  (List.range m).all fun r => decide (r < i) || eFoldRow D E cn r 0 m

theorem eFoldTab_nil (D : SplineData) (E : List (List ℚ)) (cn : ℕ → ℕ → ℕ × ℕ) (m : ℕ) :
    eFoldTab D E cn m m = true := by
  unfold eFoldTab
  rw [List.all_eq_true]
  intro r hr
  simp [List.mem_range.1 hr]

theorem eFoldTab_cons {D : SplineData} {E : List (List ℚ)} {cn : ℕ → ℕ → ℕ × ℕ} {i m : ℕ}
    (h : eFoldRow D E cn i 0 m = true) (h2 : eFoldTab D E cn (i + 1) m = true) :
    eFoldTab D E cn i m = true := by
  unfold eFoldTab at h2 ⊢
  rw [List.all_eq_true] at h2 ⊢
  intro r hr
  have := h2 r hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this ⊢
  rcases this with h3 | h3
  · by_cases hri : r = i
    · right; rw [hri]; exact h
    · left; omega
  · right; exact h3

/-- **Back to `energyFoldOk`.** -/
theorem energyFoldOk_of_tab {D : SplineData} {E : List (List ℚ)} {cn : ℕ → ℕ → ℕ × ℕ} {m : ℕ}
    (hn : D.n = m) (h : eFoldTab D E cn 0 m = true) (hs : tabSum D E ≤ D.Ibound) :
    energyFoldOk D cn E = true := by
  unfold energyFoldOk
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, hs⟩
  rw [List.all_eq_true]
  intro i hi
  rw [List.all_eq_true]
  intro j hj
  rw [hn] at hi hj
  unfold eFoldTab at h
  rw [List.all_eq_true] at h
  have hrow := h i hi
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hrow
  rcases hrow with h0 | h0
  · exact absurd h0 (Nat.not_lt_zero _)
  · have := eFoldRow_get m 0 h0 j (List.mem_range.1 hj)
    simpa [eFoldEntry] using this

end CatalanCore.Uniform.Decay.PolyWire3
