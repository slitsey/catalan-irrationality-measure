import CatalanCore.Uniform.Bank.Lambda.Boundary
import Mathlib.Tactic
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open Finset CatalanCore.Uniform.Bank.Chi3Rank
open scoped Classical

/-- Physical residues strictly inside a leading affine run, separated from its boundaries. -/
noncomputable def runResidues (p res : ℕ) (a b : ℚ) : Finset ℕ :=
  (range p).filter (fun x => x % 2 = res ∧ a + 4 ≤ (x : ℚ) ∧ (x : ℚ) ≤ b - 4)

/-- A uniform constant loss per run, valid at every scale and for either parity. -/
theorem runResidues_card_lower (p res : ℕ) (a b : ℚ) (hres : res = 0 ∨ res = 1)
    (ha : 0 ≤ a) (hb : b ≤ p) :
    (b - a) / 2 - 6 ≤ ((runResidues p res a b).card : ℚ) := by
  let L : ℕ := ⌈a + 4⌉₊
  let H : ℕ := ⌈b - 4⌉₊
  let F := (Ico L H).filter (fun x => x % 2 = res)
  have hF : F ⊆ runResidues p res a b := by
    intro x hx
    obtain ⟨hxI, hxpar⟩ := Finset.mem_filter.1 hx
    obtain ⟨hL, hH⟩ := Finset.mem_Ico.1 hxI
    have hlo : a + 4 ≤ (x : ℚ) := (Nat.ceil_le.1 hL)
    have hhi : (x : ℚ) < b - 4 := Nat.lt_ceil.1 hH
    have hxp : x < p := by exact_mod_cast (show (x : ℚ) < p by linarith)
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hxp, hxpar, hlo, hhi.le⟩
  have hpar : (H - L) / 2 ≤ F.card := by
    rcases hres with rfl | rfl
    · exact (parity_ge L H).2
    · exact (parity_ge L H).1
  have hdiv : H - L ≤ 2 * F.card + 1 := by omega
  have hdivQ : ((H - L : ℕ) : ℚ) ≤ 2 * (F.card : ℚ) + 1 := by exact_mod_cast hdiv
  have hlen : (H : ℚ) - L ≤ ((H - L : ℕ) : ℚ) := by
    by_cases h : L ≤ H
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le (by omega)]
      have hq : (H : ℚ) ≤ L := by exact_mod_cast (show H ≤ L by omega)
      norm_num
      linarith
  have hL : (L : ℚ) < a + 5 := by
    have h := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ a + 4 by linarith)
    change (L : ℚ) < a + 5
    dsimp [L]
    linarith
  have hH : b - 4 ≤ (H : ℚ) := Nat.le_ceil _
  have hcard : (F.card : ℚ) ≤ ((runResidues p res a b).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hF
  linarith

theorem good_runResidues_card_lower (r p res : ℕ) (s : Finset (Fin r))
    (a b : ℚ) (hres : res = 0 ∨ res = 1) (ha : 0 ≤ a) (hb : b ≤ p) :
    (b - a) / 2 - 6 - (r - s.card : ℕ) ≤
      (((runResidues p res a b).filter (fun x => x ∉ deletedResidues r p s)).card : ℚ) := by
  have h := runResidues_card_lower p res a b hres ha hb
  have hc := filter_not_deleted_card r p s (runResidues p res a b)
  have hcQ : ((runResidues p res a b).card : ℚ) ≤
      (((runResidues p res a b).filter (fun x => x ∉ deletedResidues r p s)).card : ℚ) +
        ((r - s.card : ℕ) : ℚ) := by exact_mod_cast hc
  linarith

/-- The matching upper estimate makes the leading row/column balance quantitative. -/
theorem runResidues_card_upper (p res : ℕ) (a b : ℚ) (hres : res = 0 ∨ res = 1)
    (hab : a ≤ b) :
    ((runResidues p res a b).card : ℚ) ≤ (b - a) / 2 + 6 := by
  by_cases h4 : 4 ≤ b
  · let L : ℕ := ⌈a + 4⌉₊
    let H : ℕ := ⌊b - 4⌋₊ + 1
    let F := (Ico L H).filter (fun x => x % 2 = res)
    have hsub : runResidues p res a b ⊆ F := by
      intro x hx
      obtain ⟨_, hxpar, hlo, hhi⟩ := Finset.mem_filter.1 hx
      have hl : L ≤ x := Nat.ceil_le.2 hlo
      have hh : x < H := by have := Nat.le_floor hhi; dsimp [H]; omega
      exact Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hl, hh⟩, hxpar⟩
    have hcard : ((runResidues p res a b).card : ℚ) ≤ (F.card : ℚ) := by
      exact_mod_cast Finset.card_le_card hsub
    by_cases hLH : L ≤ H
    · have hsum := (parity_count L (H - L)).1
      have he : L + (H - L) = H := Nat.add_sub_of_le hLH
      rw [he] at hsum
      have hge := parity_ge L H
      have hnat : 2 * F.card ≤ H - L + 1 := by
        rcases hres with rfl | rfl <;> dsimp [F] at * <;> omega
      have hnatQ : 2 * (F.card : ℚ) ≤ ((H - L : ℕ) : ℚ) + 1 := by exact_mod_cast hnat
      rw [Nat.cast_sub hLH] at hnatQ
      have hL : a + 4 ≤ (L : ℚ) := Nat.le_ceil _
      have hH : (H : ℚ) ≤ b - 3 := by
        have hf := Nat.floor_le (show (0 : ℚ) ≤ b - 4 by linarith)
        dsimp [H]
        push_cast
        linarith
      linarith
    · have he : F = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have hI := Finset.mem_Ico.1 (Finset.mem_filter.1 hx).1
        omega
      rw [he] at hcard
      simp only [Finset.card_empty, Nat.cast_zero] at hcard
      linarith
  · have he : runResidues p res a b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      have h := (Finset.mem_filter.1 hx).2
      have hx0 : (0 : ℚ) ≤ x := Nat.cast_nonneg _
      linarith [h.2.2]
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

#print axioms runResidues_card_lower
end CatalanCore.Uniform.Bank.Lambda
