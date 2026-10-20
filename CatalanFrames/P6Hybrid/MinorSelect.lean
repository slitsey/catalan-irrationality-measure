module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanCore.Measure.Pinned
public import CatalanCore.Rect.CommonMinor

@[expose] public section

open CatalanCore CatalanCore.Rect

namespace CatalanFrames.P6Hybrid

/-- The same fixed original degree works throughout a positive-width prime interval. -/
theorem minor_geometry_selection (ℓ : ℕ) (hℓ : ℓ % 6 = 1) (N : ℝ) (hN : 140 ≤ N)
    (hlo : (51 / 20 : ℝ) * N ≤ ℓ) (hhi : (ℓ : ℝ) ≤ (59 / 20 : ℝ) * N) :
    ∃ t r m : ℕ, ℓ = 6 * t + 1 ∧ 1 ≤ t ∧ P6Adm9 r m ∧ 1 ≤ m ∧
      2 * t + 1 ≤ r ∧ r + 2 * m ≤ 3 * t ∧ N ≤ (r : ℝ) ∧ (r : ℝ) ≤ N + 1 := by
  let t := ℓ / 6
  let r := ⌈N⌉₊
  let m := (r + 7) / 8
  have ht : ℓ = 6 * t + 1 := by dsimp [t]; omega
  have hrlo : N ≤ (r : ℝ) := Nat.le_ceil N
  have hrhi : (r : ℝ) < N + 1 := Nat.ceil_lt_add_one (by linarith : 0 ≤ N)
  have hm1 : r ≤ 8 * m := by dsimp [m]; omega
  have hm2 : 8 * m ≤ r + 7 := by dsimp [m]; omega
  have hm1R : (r : ℝ) ≤ 8 * m := by exact_mod_cast hm1
  have hm2R : (8 : ℝ) * m ≤ r + 7 := by exact_mod_cast hm2
  have htR : (ℓ : ℝ) = 6 * t + 1 := by exact_mod_cast ht
  have hrlarge : 140 ≤ r := by exact_mod_cast (hN.trans hrlo)
  have htm : r + 2 * m ≤ 3 * t := by
    have hR : (r : ℝ) + 2 * m ≤ 3 * t := by linarith
    exact_mod_cast hR
  have hKr : 2 * t + 1 ≤ r := by
    have hR : (2 : ℝ) * t + 1 ≤ r := by linarith
    exact_mod_cast hR
  refine ⟨t, r, m, ht, ?_, ⟨hm1, by omega⟩, ?_, hKr, htm, hrlo, hrhi.le⟩ <;> omega

/-- Pure assembly of a square-regular fixed-degree nonvanishing input. -/
theorem hasNVPinC_commonMinor_of_regular (Fr : Frame) (d : ℕ)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop}
    (hcls : ∀ ℓ, Cls ℓ → ℓ % 6 = 1)
    (hNV : ∀ ℓ : ℕ, ℓ.Prime → Cls ℓ → ∀ t r m : ℕ,
      ℓ = 6 * t + 1 → 1 ≤ t → P6Adm9 r m → 1 ≤ m →
      2 * t + 1 ≤ r → r + 2 * m ≤ 3 * t →
      ∀ p q : ℤ, 0 < q → IsCoprime p q → ¬ Bad ℓ q.natAbs →
      ∃ s : Finset (Fin r), r - s.card ≤ d ∧ (commonMinorPoly Fr r m s).eval ((p : ℚ) / q) ≠ 0) :
    HasNVPinC (commonMinorFam Fr P6Adm9 d) Cls Bad (51 / 20) (59 / 20) := by
  refine ⟨1, 140, ?_⟩
  intro ℓ hℓ hc N hN hlo hhi p q hq hcop hbad
  obtain ⟨t, r, m, ht, ht1, ha, hm, hKr, htop, hrlo, hrhi⟩ :=
    minor_geometry_selection ℓ (hcls ℓ hc) N hN hlo hhi
  obtain ⟨s, hs, hne⟩ := hNV ℓ hℓ hc t r m ht ht1 ha hm hKr htop p q hq hcop hbad
  exact ⟨⟨r, m, s⟩, ⟨ha, hs⟩, hrlo, hrhi, hne⟩

end CatalanFrames.P6Hybrid
