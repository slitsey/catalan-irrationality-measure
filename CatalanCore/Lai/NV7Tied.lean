module

public import CatalanCore.Lai.Tied
public import CatalanCore.Lai.NV7

@[expose] public section

/-! # `CatalanCore.Lai.NV7Tied`: the NV7a/NV7b `TiedNV` instances (ledger LN08/LR04). -/

section
/-!
# The NV7 `TiedNV` instances (plane `e = 4`, ratio `e = 1`), ledger LN08/LR04

Primes `ℓ ≡ 5 (mod 7)` have the tied member `n = (3ℓ - 1)/7` (`3ℓ = 7n + 1`), and primes `ℓ ≡ 3 (mod 7)`
have `n = (3ℓ - 2)/7` (`3ℓ = 7n + 2`); in both cases `ℓ = (7/3) n + d` with `d = 1/3, 2/3`.  The exception
set contains `73`, `1039` (and the primes `< 11`, and the prime divisors of `b` in the plane).
-/

open CatalanCore.Measure CatalanCore.Lai

namespace CatalanCore.Lai.NV7

theorem line_data_5 {ℓ : ℕ} (hp : ℓ.Prime) (h : ℓ % 7 = 5) (h11 : 11 ≤ ℓ) :
    3 * ℓ = 7 * ((3 * ℓ - 1) / 7) + 1 ∧ 7 ≤ (3 * ℓ - 1) / 7 := by
  have h12 : ℓ ≠ 12 := fun h' => by subst h'; norm_num at hp
  omega

theorem line_data_3 {ℓ : ℕ} (h : ℓ % 7 = 3) (h11 : 11 ≤ ℓ) :
    3 * ℓ = 7 * ((3 * ℓ - 2) / 7) + 2 ∧ 7 ≤ (3 * ℓ - 2) / 7 := by
  omega

/-- Plane, `ℓ ≡ 5 (mod 7)`. -/
noncomputable def nv7aPlaneTied (a b : ℤ) (exc : Finset ℕ)
    (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ b → ℓ ∈ exc) (h73 : 73 ∈ exc) (h1039 : 1039 ∈ exc) :
    TiedNV (laiPlaneFam a b) id 126 planeW :=
  tiedOfClass 7 5 (by norm_num) (7 / 3) (1 / 3) (by norm_num) 4 exc hexc
    (fun ℓ => (3 * ℓ - 1) / 7)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have := line_data_5 hp hc h11
      show 1 ≤ (3 * ℓ - 1) / 7
      omega)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have h3 : 3 * ℓ = 7 * ((3 * ℓ - 1) / 7) + 1 := (line_data_5 hp hc h11).1
      show (ℓ : ℝ) = 7 / 3 * (((3 * ℓ - 1) / 7 : ℕ) : ℝ) + 1 / 3
      have : (3 * (ℓ : ℝ)) = 7 * (((3 * ℓ - 1) / 7 : ℕ) : ℝ) + 1 := by exact_mod_cast h3
      linarith)
    (planeBad 4) (planeBad_dvd 4)
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      obtain ⟨h1, h2⟩ := line_data_5 hp hc h11
      have hbl : ¬ (ℓ : ℤ) ∣ b := fun hd => hex (hb ℓ hp hd)
      exact nv7_plane ((3 * ℓ - 1) / 7) h2 (Or.inl h1) (fun h => hex (by rw [h]; exact h73))
        (fun h => hex (by rw [h]; exact h1039)) a b p q hbl hq hbad)

/-- Plane, `ℓ ≡ 3 (mod 7)`. -/
noncomputable def nv7bPlaneTied (a b : ℤ) (exc : Finset ℕ)
    (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ b → ℓ ∈ exc) (h73 : 73 ∈ exc) (h1039 : 1039 ∈ exc) :
    TiedNV (laiPlaneFam a b) id 126 planeW :=
  tiedOfClass 7 3 (by norm_num) (7 / 3) (2 / 3) (by norm_num) 4 exc hexc
    (fun ℓ => (3 * ℓ - 2) / 7)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have := line_data_3 hc h11
      show 1 ≤ (3 * ℓ - 2) / 7
      omega)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have h3 : 3 * ℓ = 7 * ((3 * ℓ - 2) / 7) + 2 := (line_data_3 hc h11).1
      show (ℓ : ℝ) = 7 / 3 * (((3 * ℓ - 2) / 7 : ℕ) : ℝ) + 2 / 3
      have : (3 * (ℓ : ℝ)) = 7 * (((3 * ℓ - 2) / 7 : ℕ) : ℝ) + 2 := by exact_mod_cast h3
      linarith)
    (planeBad 4) (planeBad_dvd 4)
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      obtain ⟨h1, h2⟩ := line_data_3 hc h11
      have hbl : ¬ (ℓ : ℤ) ∣ b := fun hd => hex (hb ℓ hp hd)
      exact nv7_plane ((3 * ℓ - 2) / 7) h2 (Or.inr h1) (fun h => hex (by rw [h]; exact h73))
        (fun h => hex (by rw [h]; exact h1039)) a b p q hbl hq hbad)

/-- Ratio, `ℓ ≡ 5 (mod 7)`. -/
noncomputable def nv7aRatioTied (exc : Finset ℕ) (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc)
    (h73 : 73 ∈ exc) (h1039 : 1039 ∈ exc) : TiedNV laiRatioFam id 126 ratioW :=
  tiedOfClass 7 5 (by norm_num) (7 / 3) (1 / 3) (by norm_num) 1 exc hexc
    (fun ℓ => (3 * ℓ - 1) / 7)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have := line_data_5 hp hc h11
      show 1 ≤ (3 * ℓ - 1) / 7
      omega)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have h3 : 3 * ℓ = 7 * ((3 * ℓ - 1) / 7) + 1 := (line_data_5 hp hc h11).1
      show (ℓ : ℝ) = 7 / 3 * (((3 * ℓ - 1) / 7 : ℕ) : ℝ) + 1 / 3
      have : (3 * (ℓ : ℝ)) = 7 * (((3 * ℓ - 1) / 7 : ℕ) : ℝ) + 1 := by exact_mod_cast h3
      linarith)
    ratioBad ratioBad_dvd
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      obtain ⟨h1, h2⟩ := line_data_5 hp hc h11
      have hpl : ¬ (ℓ : ℤ) ∣ p := fun hd => hbad (Int.natCast_dvd.1 hd)
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
      have := nv7_ratio ((3 * ℓ - 1) / 7) h2 (Or.inl h1) (fun h => hex (by rw [h]; exact h73))
        (fun h => hex (by rw [h]; exact h1039)) p (q : ℤ) hq0 hpl
      have e : (((q : ℤ)) : ℚ) = (q : ℚ) := Int.cast_natCast q
      rw [e] at this
      exact this)

/-- Ratio, `ℓ ≡ 3 (mod 7)`. -/
noncomputable def nv7bRatioTied (exc : Finset ℕ) (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc)
    (h73 : 73 ∈ exc) (h1039 : 1039 ∈ exc) : TiedNV laiRatioFam id 126 ratioW :=
  tiedOfClass 7 3 (by norm_num) (7 / 3) (2 / 3) (by norm_num) 1 exc hexc
    (fun ℓ => (3 * ℓ - 2) / 7)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have := line_data_3 hc h11
      show 1 ≤ (3 * ℓ - 2) / 7
      omega)
    (fun ℓ hp hc hex => by
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      have h3 : 3 * ℓ = 7 * ((3 * ℓ - 2) / 7) + 2 := (line_data_3 hc h11).1
      show (ℓ : ℝ) = 7 / 3 * (((3 * ℓ - 2) / 7 : ℕ) : ℝ) + 2 / 3
      have : (3 * (ℓ : ℝ)) = 7 * (((3 * ℓ - 2) / 7 : ℕ) : ℝ) + 2 := by exact_mod_cast h3
      linarith)
    ratioBad ratioBad_dvd
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      have h11 : 11 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
      obtain ⟨h1, h2⟩ := line_data_3 hc h11
      have hpl : ¬ (ℓ : ℤ) ∣ p := fun hd => hbad (Int.natCast_dvd.1 hd)
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
      have := nv7_ratio ((3 * ℓ - 2) / 7) h2 (Or.inr h1) (fun h => hex (by rw [h]; exact h73))
        (fun h => hex (by rw [h]; exact h1039)) p (q : ℤ) hq0 hpl
      have e : (((q : ℤ)) : ℚ) = (q : ℚ) := Int.cast_natCast q
      rw [e] at this
      exact this)

end CatalanCore.Lai.NV7

end
