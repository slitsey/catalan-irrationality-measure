module

public import CatalanCore.Rect.CommonMinor
public import CatalanCore.Measure.Pinned

@[expose] public section

/-! # Prime-independent nonvanishing plugs into the existing pinned interface

Any unbounded set of admissible hybrid geometries with nonvanishing at every
original degree supplies `HasNVPinC`, for arbitrary prime intervals. Thus the
characteristic-zero selector can reuse the measure engine without a band
constraint or a new frozen-family contract.
-/

open Polynomial Finset

namespace CatalanCore.Rect.CharZeroNV

theorem hasNVPinC_of_every_degree (Fam : PolyFamily) (r₀ : ℕ)
    (hNV : ∀ r : ℕ, r₀ ≤ r → ∀ x : ℚ,
      ∃ i, Fam.Adm i ∧ Fam.deg i = r ∧ Fam.evalQ i x ≠ 0)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    HasNVPinC Fam Cls Bad α β := by
  refine ⟨1, max 1 (r₀ : ℝ), ?_⟩
  intro ell hell hcls N hN hlo hhi p q hq hcop hbad
  have hN0 : 0 ≤ N := by linarith [le_max_left (1 : ℝ) (r₀ : ℝ)]
  have hNlo : (r₀ : ℝ) ≤ N := (le_max_right _ _).trans hN
  let r := ⌈N⌉₊
  have hrlo : N ≤ (r : ℝ) := Nat.le_ceil N
  have hrhi : (r : ℝ) < N + 1 := Nat.ceil_lt_add_one hN0
  have hr₀ : r₀ ≤ r := by exact_mod_cast hNlo.trans hrlo
  obtain ⟨i, hi, hd, he⟩ := hNV r hr₀ ((p : ℚ) / q)
  refine ⟨i, hi, ?_, ?_, he⟩
  · simpa [hd] using hrlo
  · simpa [hd] using hrhi.le

theorem commonMinor_hasNVPinC (Fr : Frame) (Adm : ℕ → ℕ → Prop) (r₀ : ℕ)
    (hAdm : ∀ r, r₀ ≤ r → ∃ m, Adm r m)
    (hNV : ∀ r, r₀ ≤ r → ∀ m x,
      ∃ s : Finset (Fin r), r - s.card ≤ 1 ∧ (commonMinorPoly Fr r m s).eval x ≠ 0)
    (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) :
    HasNVPinC (commonMinorFam Fr Adm 1) Cls Bad α β := by
  apply hasNVPinC_of_every_degree _ r₀ _ Cls Bad α β
  intro r hr x
  obtain ⟨m, hm⟩ := hAdm r hr
  obtain ⟨s, hs, he⟩ := hNV r hr m x
  exact ⟨⟨r, m, s⟩, ⟨hm, hs⟩, rfl, he⟩

end CatalanCore.Rect.CharZeroNV
