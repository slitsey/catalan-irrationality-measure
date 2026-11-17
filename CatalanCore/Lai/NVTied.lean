module

public import CatalanCore.Lai.Tied
public import CatalanCore.Lai.NV

@[expose] public section



/-!
# The Lai `TiedNV` instances (plane `e = 4`, ratio `e = 1`)

For a prime `ℓ ≡ 1 (mod 18)` write `ℓ = 9m + 1`; the tied member is `n = 2m = 2(ℓ - 1)/9` and
`ℓ = (9/2) n + 1`.  The `nv` fields are Corollaries NV1 and NV2.
-/

open CatalanCore.Measure CatalanCore.Lai

namespace CatalanCore.Lai.NV

theorem lai_class_data {ℓ : ℕ} (hp : ℓ.Prime) (h : ℓ % 18 = 1) :
    ℓ = 9 * ((ℓ - 1) / 9) + 1 ∧ 2 ≤ (ℓ - 1) / 9 := by
  have h1 : ℓ ≠ 1 := hp.ne_one
  omega

/-- The plane instance for the Lai primes, `e = 4`. -/
noncomputable def laiPlaneTied (a b : ℤ) (exc : Finset ℕ)
    (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ b → ℓ ∈ exc) :
    TiedNV (laiPlaneFam a b) id 126 planeW :=
  tiedOfClass 18 1 (by norm_num) (9 / 2) 1 (by norm_num) 4 exc hexc
    (fun ℓ => 2 * ((ℓ - 1) / 9))
    (fun ℓ hp hc _ => by
      have := lai_class_data hp hc
      show 1 ≤ 2 * ((ℓ - 1) / 9)
      omega)
    (fun ℓ hp hc _ => by
      obtain ⟨j, hj⟩ : ∃ j, ℓ = 18 * j + 1 := ⟨ℓ / 18, by omega⟩
      subst hj
      have : (18 * j + 1 - 1) / 9 = 2 * j := by omega
      show ((18 * j + 1 : ℕ) : ℝ) = 9 / 2 * ((2 * ((18 * j + 1 - 1) / 9) : ℕ) : ℝ) + 1
      rw [this]; push_cast; ring)
    (planeBad 4) (planeBad_dvd 4)
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      obtain ⟨h1, h2⟩ := lai_class_data hp hc
      have hbl : ¬ (ℓ : ℤ) ∣ b := fun hd => hex (hb ℓ hp hd)
      exact lai_nv_plane (m := (ℓ - 1) / 9) h1 (by omega) a b p q hbl hq hbad)

/-- The ratio instance for the Lai primes, `e = 1`. -/
noncomputable def laiRatioTied (exc : Finset ℕ) (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 11 → ℓ ∈ exc) :
    TiedNV laiRatioFam id 126 ratioW :=
  tiedOfClass 18 1 (by norm_num) (9 / 2) 1 (by norm_num) 1 exc hexc
    (fun ℓ => 2 * ((ℓ - 1) / 9))
    (fun ℓ hp hc _ => by
      have := lai_class_data hp hc
      show 1 ≤ 2 * ((ℓ - 1) / 9)
      omega)
    (fun ℓ hp hc _ => by
      obtain ⟨j, hj⟩ : ∃ j, ℓ = 18 * j + 1 := ⟨ℓ / 18, by omega⟩
      subst hj
      have : (18 * j + 1 - 1) / 9 = 2 * j := by omega
      show ((18 * j + 1 : ℕ) : ℝ) = 9 / 2 * ((2 * ((18 * j + 1 - 1) / 9) : ℕ) : ℝ) + 1
      rw [this]; push_cast; ring)
    ratioBad ratioBad_dvd
    (fun ℓ hp hc hex p q hq hbad => by
      haveI := Fact.mk hp
      obtain ⟨h1, h2⟩ := lai_class_data hp hc
      have hpl : ¬ (ℓ : ℤ) ∣ p := fun hd => hbad (Int.natCast_dvd.1 hd)
      have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
      have := lai_nv_ratio (m := (ℓ - 1) / 9) h1 (by omega) p (q : ℤ) hq0 hpl
      simpa using this)

end CatalanCore.Lai.NV
