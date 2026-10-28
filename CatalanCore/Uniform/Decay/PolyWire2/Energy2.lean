import CatalanCore.Uniform.Decay.PolyFull.Oracle2
import CatalanCore.Uniform.Decay.Cells.Energy
set_option Elab.async false

/-!
# The pair-energy test in cons form (lane B, package B3b)

`energyOk2 E D` implies `energyOkOf pairOracle E D`, but is structurally recursive on the rows and
entries of the table, so each pair energy `pairOk D i j E_ij` can be one separate `decide +kernel`
theorem, assembled by the cons lemmas `rowOk_cons` / `tabOk_cons`.
-/

namespace CatalanCore.Uniform.Decay.PolyWire2

open CatalanCore.Uniform.Decay.Cells CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.PolyFull

/-- Row `i` of the table, from column `j` on. -/
def rowOk (D : SplineData) (i : ℕ) : ℕ → List ℚ → Bool
  | j, [] => decide (D.n ≤ j)
  | j, e :: es => pairOracle.pairOk D i j e && rowOk D i (j + 1) es

theorem rowOk_nil (D : SplineData) (i j : ℕ) (h : D.n ≤ j) : rowOk D i j [] = true := by
  simp [rowOk, h]

theorem rowOk_cons {D : SplineData} {i j : ℕ} {e : ℚ} {es : List ℚ}
    (h : pairOracle.pairOk D i j e = true) (hr : rowOk D i (j + 1) es = true) :
    rowOk D i j (e :: es) = true := by
  simp [rowOk, h, hr]

theorem rowOk_sound (D : SplineData) (i : ℕ) :
    ∀ (row : List ℚ) (j : ℕ), rowOk D i j row = true →
      ∀ k, j + k < D.n → pairOracle.pairOk D i (j + k) (row.getD k 0) = true
  | [], j, h, k, hk => by simp [rowOk] at h; omega
  | e :: es, j, h, 0, hk => by
      simp only [rowOk, Bool.and_eq_true] at h
      simpa using h.1
  | e :: es, j, h, k + 1, hk => by
      simp only [rowOk, Bool.and_eq_true] at h
      have := rowOk_sound D i es (j + 1) h.2 k (by omega)
      have e1 : j + (k + 1) = j + 1 + k := by omega
      rw [e1]
      simpa using this

/-- The whole table from row `i` on. -/
def tabOk (D : SplineData) : ℕ → List (List ℚ) → Bool
  | i, [] => decide (D.n ≤ i)
  | i, r :: rs => rowOk D i 0 r && tabOk D (i + 1) rs

theorem tabOk_nil (D : SplineData) (i : ℕ) (h : D.n ≤ i) : tabOk D i [] = true := by
  simp [tabOk, h]

theorem tabOk_cons {D : SplineData} {i : ℕ} {r : List ℚ} {rs : List (List ℚ)}
    (h : rowOk D i 0 r = true) (hr : tabOk D (i + 1) rs = true) : tabOk D i (r :: rs) = true := by
  simp [tabOk, h, hr]

theorem tabOk_sound (D : SplineData) :
    ∀ (E : List (List ℚ)) (i : ℕ), tabOk D i E = true →
      ∀ k, i + k < D.n → ∀ j, j < D.n →
        pairOracle.pairOk D (i + k) j ((E.getD k []).getD j 0) = true
  | [], i, h, k, hk => by simp [tabOk] at h; omega
  | r :: rs, i, h, 0, hk => by
      simp only [tabOk, Bool.and_eq_true] at h
      intro j hj
      have := rowOk_sound D i r 0 h.1 j (by omega)
      simpa using this
  | r :: rs, i, h, k + 1, hk => by
      simp only [tabOk, Bool.and_eq_true] at h
      intro j hj
      have := tabOk_sound D rs (i + 1) h.2 k (by omega) j hj
      have e1 : i + (k + 1) = i + 1 + k := by omega
      rw [e1]
      simpa using this

/-- **The energy test** in cons form. -/
def energyOk2 (E : List (List ℚ)) (D : SplineData) : Bool :=
  tabOk D 0 E && decide (tabSum D E ≤ D.Ibound)

theorem energyOk2_imp {E : List (List ℚ)} {D : SplineData} (h : energyOk2 E D = true) :
    energyOkOf pairOracle E D = true := by
  simp only [energyOk2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  simp only [energyOkOf, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, h2⟩
  rw [List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  have := tabOk_sound D E 0 h1 i.1 (by simpa using i.2) j.1 j.2
  simpa using this

end CatalanCore.Uniform.Decay.PolyWire2
