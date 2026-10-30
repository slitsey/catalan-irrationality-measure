import CatalanCore.Uniform.Content.Member.Template
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Content.BankShared.SawPrefix
open CatalanCore.Arith.Hybrid Finset

noncomputable def H (n : ℕ) : ℝ := ∑ k ∈ range n, 1 / ((k : ℝ) + 1)
theorem H_succ (n : ℕ) : H (n + 1) = H n + 1 / ((n : ℝ) + 1) := by
  simp [H, sum_range_succ]

theorem reciprocal_sum_le_log (a : ℝ) (ha : 0 < a) (n : ℕ) :
    (∑ k ∈ range n, 1 / (a + (k : ℝ) + 1)) ≤ Real.log (a + n) - Real.log a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have hx : 0 < a + (n : ℝ) := by positivity
    have hy : 0 < a + (n : ℝ) + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at h
    have he : (a + (n : ℝ)) / (a + (n : ℝ) + 1) - 1 =
        -(1 / (a + (n : ℝ) + 1)) := by field_simp; ring
    rw [he] at h
    push_cast
    simp only [add_assoc] at *
    linarith

theorem H_double_sub_le_log_two (n : ℕ) (hn : 0 < n) :
    H (2 * n) - H n ≤ Real.log 2 := by
  have hsum : H (2 * n) - H n =
      ∑ k ∈ range n, 1 / ((n : ℝ) + (k : ℝ) + 1) := by
    rw [show 2 * n = n + n by omega]
    simp only [H, sum_range_add, Nat.cast_add]
    ring
  rw [hsum]
  have h := reciprocal_sum_le_log (n : ℝ) (by exact_mod_cast hn) n
  have he : Real.log ((n : ℝ) + n) - Real.log n = Real.log 2 := by
    rw [show (n : ℝ) + n = 2 * n by ring,
      Real.log_mul (by norm_num) (by exact_mod_cast hn.ne')]
    ring
  rwa [he] at h

noncomputable def debits (n : ℕ) : ℝ :=
  ∑ k ∈ range n, 1 / (2 * ((k : ℝ) + 1) * ((k : ℝ) + 2) * (2 * (k : ℝ) + 3))

theorem debits_succ (n : ℕ) :
    debits (n + 1) = debits n +
      1 / (2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) * (2 * (n : ℝ) + 3)) := by
  simp [debits, sum_range_succ]

theorem debits_eq (n : ℕ) :
    debits n = 3 / 2 - 1 / (2 * ((n : ℝ) + 1)) -
      2 * (H (2 * (n + 1)) - H (n + 1)) := by
  induction n with
  | zero => norm_num [debits, H]
  | succ n ih =>
    have hd : H (2 * (n + 1 + 1)) =
        H (2 * (n + 1)) + 1 / (2 * ((n : ℝ) + 1) + 1) +
          1 / (2 * ((n : ℝ) + 1) + 2) := by
      rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by omega, H_succ, H_succ]
      push_cast
      ring
    rw [debits_succ, ih, hd, H_succ (n + 1)]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    have h4 : 2 * (n : ℝ) + 4 ≠ 0 := by positivity
    field_simp
    <;> ring

noncomputable def pair (a C : ℝ) (n : ℕ) : List Piece :=
  [{ s := a / ((n : ℝ) + 1), t := 2 * a / (2 * (n : ℝ) + 1),
     α := 2 + 3 * a, β := -((n : ℝ) + 1), C := C },
   { s := 2 * a / (2 * (n : ℝ) + 1), t := a / n,
     α := 2 + a, β := n, C := C }]

noncomputable def pieces (a C : ℝ) : ℕ → List Piece
  | 0 => []
  | n + 1 => pair a C (n + 1) ++ pieces a C n

theorem listInt_append (l r : List Piece) : listInt (l ++ r) = listInt l + listInt r := by
  induction l with
  | nil => simp [listInt]
  | cons p l ih => simp only [List.cons_append, listInt, ih]; ring

theorem pair_mass (a C : ℝ) (n : ℕ) (hn : 0 < n) :
    listInt (pair a C n) =
      (2 + 2 * a) * a * (1 / n - 1 / ((n : ℝ) + 1)) -
        a ^ 2 / (2 * n * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1)) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [pair, listInt, Piece.int]
  field_simp
  <;> ring

theorem pieces_mass (a C : ℝ) (n : ℕ) :
    listInt (pieces a C n) =
      (2 + 2 * a) * a * (1 - 1 / ((n : ℝ) + 1)) - a ^ 2 * debits n := by
  induction n with
  | zero => simp [pieces, listInt, debits]
  | succ n ih =>
    rw [pieces, listInt_append, pair_mass a C (n + 1) (by omega), ih, debits_succ]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    have h3 : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
    field_simp
    <;> ring

theorem mass_le (a C : ℝ) (n : ℕ) :
    (2 + 2 * a) * (a / ((n : ℝ) + 1)) + listInt (pieces a C n) ≤
      2 * a + a ^ 2 / 2 + 2 * a ^ 2 * Real.log 2 + a ^ 2 / (2 * ((n : ℝ) + 1)) := by
  rw [pieces_mass, debits_eq]
  have h := mul_le_mul_of_nonneg_left (H_double_sub_le_log_two (n + 1) (by omega))
    (show 0 ≤ 2 * a ^ 2 by positivity)
  push_cast at h
  have he :
      (2 + 2 * a) * (a / ((n : ℝ) + 1)) +
        ((2 + 2 * a) * a * (1 - 1 / ((n : ℝ) + 1)) -
          a ^ 2 * (3 / 2 - 1 / (2 * ((n : ℝ) + 1)) -
            2 * (H (2 * (n + 1)) - H (n + 1)))) =
      2 * a + a ^ 2 / 2 + a ^ 2 / (2 * ((n : ℝ) + 1)) +
        2 * a ^ 2 * (H (2 * (n + 1)) - H (n + 1)) := by
    field_simp
    <;> ring
  rw [he]
  linarith

theorem exists_mass_slack (a C ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (2 + 2 * a) * (a / ((n : ℝ) + 1)) + listInt (pieces a C n) ≤
      2 * a + a ^ 2 / 2 + 2 * a ^ 2 * Real.log 2 + ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a ^ 2 / (2 * ε))
  have hb : a ^ 2 / (2 * ((n : ℝ) + 1)) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * ((n : ℝ) + 1))).2
    have h := (div_lt_iff₀ (show 0 < 2 * ε by positivity)).1 hn
    nlinarith
  exact ⟨n, (mass_le a C n).trans (by linarith)⟩

#print axioms exists_mass_slack
end CatalanCore.Uniform.Content.BankShared.SawPrefix
