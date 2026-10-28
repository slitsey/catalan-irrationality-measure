module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
# UF window cells: the counting lemmas on the border `[r, r + 2m)` (lane H, H12)

Pure `ℕ`/`Finset` counting used by the generic window cell (`Cell3`):

* `card_win_sum`: the rows `r + 2 i` and columns `r + 2 i + 1` lying in `[t₀, t_v]` are
  `min (t_v + 1) (r + 2 m) - t₀` in number;
* `card_outside`: the border nodes outside `[t₀, t_v]` that are not multiples of `p` are at least
  `2 m - (min (t_v+1) (r+2m) - t₀) - 1` in number (`2 m ≤ p`: at most one multiple of `p`);
* `card_S0`: the window together with those nodes.
-/

namespace CatalanCore.Uniform.Content.UFFamily3

open Finset

theorem card_win_sum (r m t0 tv : ℕ) (ht0 : r ≤ t0) :
    ((range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).card +
      ((range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).card =
      min (tv + 1) (r + 2 * m) - t0 := by
  have hA : (((range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).image
      (fun i => r + 2 * i)).card =
      ((range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).card :=
    Finset.card_image_of_injective _ (fun a b h => by simp at h; omega)
  have hB : (((range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).image
      (fun i => r + 2 * i + 1)).card =
      ((range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).card :=
    Finset.card_image_of_injective _ (fun a b h => by simp at h; omega)
  have hD : Disjoint (((range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).image
      (fun i => r + 2 * i))
      (((range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).image
      (fun i => r + 2 * i + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hy
    omega
  have hU : (((range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).image
      (fun i => r + 2 * i)) ∪
      (((range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).image
      (fun i => r + 2 * i + 1)) = Finset.Ico t0 (min (tv + 1) (r + 2 * m)) := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico]
    constructor
    · rintro (⟨a, ⟨h1, h2, h3⟩, rfl⟩ | ⟨a, ⟨h1, h2, h3⟩, rfl⟩) <;> omega
    · intro ⟨h1, h2⟩
      by_cases hp : (v - r) % 2 = 0
      · left; exact ⟨(v - r) / 2, ⟨by omega, by omega, by omega⟩, by omega⟩
      · right; exact ⟨(v - r) / 2, ⟨by omega, by omega, by omega⟩, by omega⟩
  rw [← hA, ← hB, ← Finset.card_union_of_disjoint hD, hU, Nat.card_Ico]

theorem card_mult_le_one (r m p : ℕ) (h2 : 2 * m ≤ p) :
    ((Finset.Ico r (r + 2 * m)).filter (fun v => p ∣ v)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_Ico] at ha hb
  rcases le_total a b with h | h
  · have := (Nat.dvd_sub ha.2 hb.2)
    have hd : p ∣ b - a := Nat.dvd_sub hb.2 ha.2
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd : p ∣ a - b := Nat.dvd_sub ha.2 hb.2
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

theorem card_outside (r m p t0 tv : ℕ) (h2 : 2 * m ≤ p) (ht0 : r ≤ t0) :
    2 * m - (min (tv + 1) (r + 2 * m) - t0) - 1 ≤
      ((Finset.Ico r (r + 2 * m)).filter (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v)).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Finset.Ico r (r + 2 * m))
    (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v)
  rw [Nat.card_Ico] at h1
  have hsub : ((Finset.Ico r (r + 2 * m)).filter (fun v => ¬ ((v < t0 ∨ tv < v) ∧ ¬ p ∣ v))) ⊆
      Finset.Ico t0 (min (tv + 1) (r + 2 * m)) ∪
        ((Finset.Ico r (r + 2 * m)).filter (fun v => p ∣ v)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hv ⊢
    by_cases hd : p ∣ v
    · exact Or.inr ⟨hv.1, hd⟩
    · left; omega
  have h3 := Finset.card_le_card hsub
  have h4 := Finset.card_union_le (Finset.Ico t0 (min (tv + 1) (r + 2 * m)))
    ((Finset.Ico r (r + 2 * m)).filter (fun v => p ∣ v))
  rw [Nat.card_Ico] at h4
  have h5 := card_mult_le_one r m p h2
  omega

theorem card_S0 (r m p t0 tv : ℕ) (h2 : 2 * m ≤ p) (ht0 : r ≤ t0) :
    (tv + 1 - t0) + (2 * m - (min (tv + 1) (r + 2 * m) - t0) - 1) ≤
      (Finset.Icc t0 tv ∪
        (Finset.Ico r (r + 2 * m)).filter (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v)).card := by
  have hD : Disjoint (Finset.Icc t0 tv)
      ((Finset.Ico r (r + 2 * m)).filter (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v)) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_Icc, Finset.mem_filter] at hx hy
    omega
  rw [Finset.card_union_of_disjoint hD, Nat.card_Icc]
  have := card_outside r m p t0 tv h2 ht0
  omega

end CatalanCore.Uniform.Content.UFFamily3
