module

public import CatalanCore.Lai.Tied
public import CatalanCore.Lai.NV
public import CatalanCore.Lai.B83

@[expose] public section



/-!
# The Lai `TiedNV` instances (plane `e = 4`, ratio `e = 1`)

For a prime `ℓ ≡ 1 (mod 18)` write `ℓ = 9m + 1`; the tied member is `n = 2m = 2(ℓ - 1)/9` and
`ℓ = (9/2) n + 1`.  The `nv` fields are Corollaries NV1 and NV2.

The band instances `b83TiedPlane`, `b83TiedRatio` (Criterion W2B, ledger LB11): every prime `ℓ ≥ 100`
is tied to every member `n` with `8n/3 < ℓ < 3n - 1`, slope interval `[c₁, c₂] = [8/3, 3]`, offset
tolerance `D' = 2`; the `nv` fields are the corollaries `nv_plane_B83`, `nv_ratio_B83` of Theorem B83.
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

/-! ### The band instances (Theorem B83) -/

/-- The plane instance for the band `8n/3 < ℓ < 3n - 1`, `e = 4`.  The exception set contains the
primes `< 100`, `24359` and the primes dividing `b`. -/
noncomputable def b83TiedPlane (a b : ℤ) (exc : Finset ℕ)
    (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 100 → ℓ ∈ exc) (h24359 : 24359 ∈ exc)
    (hb : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ b → ℓ ∈ exc) :
    TiedNV (laiPlaneFam a b) id 126 planeW where
  S := classSet 126 1 0
  S_unit := classSet_unit
  c₁ := 8 / 3
  c₂ := 3
  c₁_pos := by norm_num
  c₁_le := by norm_num
  D' := 2
  D'_nonneg := by norm_num
  e := 4
  exc := exc
  rel := fun ℓ (n : ℕ) => 8 * n < 3 * ℓ ∧ ℓ + 1 < 3 * n
  exists_mem := fun ℓ hp _ hex x y hxy hx hy => by
    have h100 : 100 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
    obtain ⟨n, hn1, hn2, hn3, hn4⟩ := band_exists_n h100 hxy hx hy
    exact ⟨n, ⟨hn1, hn2⟩, by show x - 2 ≤ ((n : ℕ) : ℝ); linarith,
      by show ((n : ℕ) : ℝ) ≤ y + 2; linarith⟩
  adm := fun _ _ _ _ (n : ℕ) hn => by
    show 1 ≤ n
    have := hn.2
    omega
  Bad := planeBad 4
  bad_dvd := planeBad_dvd 4
  nv := fun ℓ hp _ hex (n : ℕ) hn p q hq hbad => by
    have := Fact.mk hp
    have h13 : ℓ ≠ 13 := fun h => hex (hexc ℓ hp (by omega))
    have h24 : ℓ ≠ 24359 := fun h => hex (by rw [h]; exact h24359)
    have hbl : ¬ (ℓ : ℤ) ∣ b := fun hd => hex (hb ℓ hp hd)
    exact B83Main.nv_plane_B83 n hn.1 hn.2 h13 h24 a b p q hbl hq hbad

/-- The ratio instance for the band `8n/3 < ℓ < 3n - 1`, `e = 1`. -/
noncomputable def b83TiedRatio (exc : Finset ℕ) (hexc : ∀ ℓ : ℕ, ℓ.Prime → ℓ < 100 → ℓ ∈ exc)
    (h24359 : 24359 ∈ exc) : TiedNV laiRatioFam id 126 ratioW where
  S := classSet 126 1 0
  S_unit := classSet_unit
  c₁ := 8 / 3
  c₂ := 3
  c₁_pos := by norm_num
  c₁_le := by norm_num
  D' := 2
  D'_nonneg := by norm_num
  e := 1
  exc := exc
  rel := fun ℓ (n : ℕ) => 8 * n < 3 * ℓ ∧ ℓ + 1 < 3 * n
  exists_mem := fun ℓ hp _ hex x y hxy hx hy => by
    have h100 : 100 ≤ ℓ := by by_contra h; exact hex (hexc ℓ hp (by omega))
    obtain ⟨n, hn1, hn2, hn3, hn4⟩ := band_exists_n h100 hxy hx hy
    exact ⟨n, ⟨hn1, hn2⟩, by show x - 2 ≤ ((n : ℕ) : ℝ); linarith,
      by show ((n : ℕ) : ℝ) ≤ y + 2; linarith⟩
  adm := fun _ _ _ _ (n : ℕ) hn => by
    show 1 ≤ n
    have := hn.2
    omega
  Bad := ratioBad
  bad_dvd := ratioBad_dvd
  nv := fun ℓ hp _ hex (n : ℕ) hn p q hq hbad => by
    have := Fact.mk hp
    have h13 : ℓ ≠ 13 := fun h => hex (hexc ℓ hp (by omega))
    have h24 : ℓ ≠ 24359 := fun h => hex (by rw [h]; exact h24359)
    have hpl : ¬ (ℓ : ℤ) ∣ p := fun hd => hbad (Int.natCast_dvd.1 hd)
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have := B83Main.nv_ratio_B83 n hn.1 hn.2 h13 h24 p (q : ℤ) hq0 hpl
    simpa using this

end CatalanCore.Lai.NV
