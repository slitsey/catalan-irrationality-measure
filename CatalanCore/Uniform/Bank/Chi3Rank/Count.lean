import CatalanCore.Uniform.Bank.Chi3Rank.Fibre
set_option Elab.async false

/-! # Counting lemmas for the rank layer (lane H, H16) -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Finset

theorem parity_count (lo : ℕ) : ∀ d : ℕ,
    (((Ico lo (lo + d)).filter (fun x => x % 2 = 1)).card +
      ((Ico lo (lo + d)).filter (fun x => x % 2 = 0)).card = d) ∧
    (d % 2 = 0 → ((Ico lo (lo + d)).filter (fun x => x % 2 = 1)).card =
      ((Ico lo (lo + d)).filter (fun x => x % 2 = 0)).card) ∧
    (d % 2 = 1 → lo % 2 = 1 → ((Ico lo (lo + d)).filter (fun x => x % 2 = 1)).card =
      ((Ico lo (lo + d)).filter (fun x => x % 2 = 0)).card + 1) ∧
    (d % 2 = 1 → lo % 2 = 0 → ((Ico lo (lo + d)).filter (fun x => x % 2 = 0)).card =
      ((Ico lo (lo + d)).filter (fun x => x % 2 = 1)).card + 1) := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    have e : Ico lo (lo + (d + 1)) = insert (lo + d) (Ico lo (lo + d)) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hn : lo + d ∉ Ico lo (lo + d) := by simp
    rw [e, Finset.filter_insert, Finset.filter_insert]
    obtain ⟨h1, h2, h3, h4⟩ := ih
    by_cases hp : (lo + d) % 2 = 1
    · have hp' : ¬ (lo + d) % 2 = 0 := by omega
      rw [if_pos hp, if_neg hp']
      rw [Finset.card_insert_of_notMem (by simp [hn])]
      omega
    · have hp' : (lo + d) % 2 = 0 := by omega
      rw [if_neg hp, if_pos hp']
      rw [Finset.card_insert_of_notMem (by simp [hn])]
      omega

theorem parity_ge (lo hi : ℕ) :
    (hi - lo) / 2 ≤ ((Ico lo hi).filter (fun x => x % 2 = 1)).card ∧
    (hi - lo) / 2 ≤ ((Ico lo hi).filter (fun x => x % 2 = 0)).card := by
  rcases le_total lo hi with h | h
  · obtain ⟨d, rfl⟩ : ∃ d, hi = lo + d := ⟨hi - lo, by omega⟩
    obtain ⟨h1, h2, h3, h4⟩ := parity_count lo d
    have : lo + d - lo = d := by omega
    rw [this]
    constructor <;> omega
  · simp [Nat.sub_eq_zero_of_le h]

open Classical in
theorem card_kept (r : ℕ) (s : Finset (Fin r)) (A : Finset ℕ) (hA : ∀ x ∈ A, x < r) :
    A.card ≤ (A.filter (keptN r s)).card + (r - s.card) := by
  have h := Finset.card_filter_add_card_filter_not (s := A) (keptN r s)
  have hle : (A.filter (fun x => ¬ keptN r s x)).card ≤ r - s.card := by
    have hsub : A.filter (fun x => ¬ keptN r s x) ⊆ (sᶜ : Finset (Fin r)).image Fin.val := by
      intro x hx
      have hx' := Finset.mem_filter.1 hx
      have hxr := hA x hx'.1
      refine Finset.mem_image.2 ⟨⟨x, hxr⟩, ?_, rfl⟩
      rw [Finset.mem_compl]
      intro hs
      exact hx'.2 ⟨hxr, hs⟩
    calc _ ≤ ((sᶜ : Finset (Fin r)).image Fin.val).card := Finset.card_le_card hsub
      _ ≤ (sᶜ : Finset (Fin r)).card := Finset.card_image_le
      _ = r - s.card := by simp [Finset.card_compl]
  omega

open Classical in
theorem card_good (r p : ℕ) (s : Finset (Fin r)) (A : Finset ℕ) (P : ℕ → Prop)
    (hP : ∀ x ∈ A, ¬ P x → ∃ v, v < r ∧ ¬ keptN r s v ∧ v % p = x) :
    A.card ≤ (A.filter P).card + (r - s.card) := by
  have h := Finset.card_filter_add_card_filter_not (s := A) P
  have hsub : A.filter (fun x => ¬ P x) ⊆
      (((sᶜ : Finset (Fin r)).image Fin.val).image (fun v => v % p)) := by
    intro x hx
    have hx' := Finset.mem_filter.1 hx
    obtain ⟨v, hvr, hvk, hvx⟩ := hP x hx'.1 hx'.2
    refine Finset.mem_image.2 ⟨v, Finset.mem_image.2 ⟨⟨v, hvr⟩, ?_, rfl⟩, hvx⟩
    rw [Finset.mem_compl]
    intro hs
    exact hvk ⟨hvr, hs⟩
  have hle : (A.filter (fun x => ¬ P x)).card ≤ r - s.card := by
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ ((sᶜ : Finset (Fin r)).image Fin.val).card := Finset.card_image_le
      _ ≤ (sᶜ : Finset (Fin r)).card := Finset.card_image_le
      _ = r - s.card := by simp [Finset.card_compl]
  omega

end CatalanCore.Uniform.Bank.Chi3Rank
