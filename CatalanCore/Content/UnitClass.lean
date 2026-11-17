module

public import CatalanCore.Lai.ContentLaw

@[expose] public section

/-! # `CatalanCore.Content.UnitClass`: unit-class identities (ledger LC05/LC07). -/

section
/-!
# `CatalanCore.Content.UnitClass`: the unit-class identities `ĉ(s) · Π′(-s)² = K · D_α(s)`

(content Lemma 2.3, ledger LC05/LC07).  For `ℓ = α + 2n`, `A = 6n - 2ℓ`, the unit part of
`C(6n,k)² C(2n+k,k)³` at `k = s + jℓ` is `κ(j) ĉ(s)`, and for `α ≤ s < ℓ`

`ĉ(s) · ∏_{t ≠ s, t ≤ A} (t - s)^{2 ν₀(t)} = K · ∏_{i < α} (s - i)`,  `K = (A!)² / ((2n)!)³`,

on `T2 = [α, A]` (pure factorial algebra) and on `T4 = (A, ℓ)` (Wilson reflection).
-/

open Finset CatalanCore.Basic CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `∏_{t ≠ s, t ≤ A} (t - s)^{2 ν₀(t)}` (for `s ≤ A`), resp. `∏_{t ≤ A} …` (for `s > A`). -/
noncomputable def PcoreR (ℓ α A s : ℕ) : ZMod ℓ :=
  if s < A + 1 then ∏ t ∈ (range (A + 1)).erase s,
      (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1))
  else ∏ t ∈ range (A + 1), (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1))

theorem fz_ne {m : ℕ} (hm : m < ℓ) : ((m.factorial : ℕ) : ZMod ℓ) ≠ 0 :=
  fz_ne_zero (p := ℓ) hm

/-- `∏_{t<a} (s - t) · (s - a)! = s!`. -/
theorem prod_range_sub (s a : ℕ) (h : a ≤ s) :
    (∏ t ∈ range a, ((s : ZMod ℓ) - t)) * (((s - a).factorial : ℕ) : ZMod ℓ) =
      ((s.factorial : ℕ) : ZMod ℓ) := by
  have h1 := Nat.factorial_mul_descFactorial h
  rw [Nat.descFactorial_eq_prod_range] at h1
  have h2 := congrArg (fun z : ℕ => (z : ZMod ℓ)) h1
  simp only [Nat.cast_mul, Nat.cast_prod] at h2
  rw [mul_comm]
  convert h2 using 2
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Nat.cast_sub (by have := mem_range.1 ht; omega)]

/-- `∏_{a ≤ t < b} (s - t) · (s - b)! = (s - a)!`. -/
theorem prod_Ico_sub (s a b : ℕ) (hab : a ≤ b) (hbs : b ≤ s) :
    (∏ t ∈ Ico a b, ((s : ZMod ℓ) - t)) * (((s - b).factorial : ℕ) : ZMod ℓ) =
      (((s - a).factorial : ℕ) : ZMod ℓ) := by
  have h := prod_range_sub (ℓ := ℓ) (s - a) (b - a) (by omega)
  rw [Finset.prod_Ico_eq_prod_range]
  have e : s - a - (b - a) = s - b := by omega
  rw [e] at h
  convert h using 2
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Nat.cast_sub (by omega), Nat.cast_add]
  ring

/-- `∏_{s < t ≤ A} (t - s) = (A - s)!`. -/
theorem prod_Ico_after (s A : ℕ) (hs : s ≤ A) :
    (∏ t ∈ Ico (s + 1) (A + 1), (((t : ℕ) : ZMod ℓ) - s)) = (((A - s).factorial : ℕ) : ZMod ℓ) := by
  rw [Finset.prod_Ico_eq_prod_range]
  have e : A + 1 - (s + 1) = A - s := by omega
  rw [e, ← Finset.prod_range_add_one_eq_factorial]
  push_cast
  refine Finset.prod_congr rfl fun t ht => ?_
  push_cast; ring

theorem PcoreR_T2 (α A s : ℕ) (hα : α ≤ s) (hsA : s ≤ A) :
    PcoreR ℓ α A s = (∏ t ∈ range α, ((s : ZMod ℓ) - t)) ^ 6 *
      (((s - α).factorial : ℕ) : ZMod ℓ) ^ 2 * (((A - s).factorial : ℕ) : ZMod ℓ) ^ 2 := by
  unfold PcoreR
  rw [if_pos (by omega)]
  have hsplit : (range (A + 1)).erase s = range α ∪ Ico α s ∪ Ico (s + 1) (A + 1) := by
    ext t; simp only [mem_erase, mem_range, mem_union, mem_Ico]; omega
  have hd1 : Disjoint (range α) (Ico α s) := by
    rw [Finset.disjoint_left]; intro t h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  have hd2 : Disjoint (range α ∪ Ico α s) (Ico (s + 1) (A + 1)) := by
    rw [Finset.disjoint_left]; intro t h1 h2
    simp only [mem_union, mem_range, mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.prod_union hd2, Finset.prod_union hd1]
  have e1 : ∏ t ∈ range α, (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1)) =
      (∏ t ∈ range α, ((s : ZMod ℓ) - t)) ^ 6 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [if_pos (mem_range.1 ht)]
    have : (((t : ℕ) : ZMod ℓ) - s) = -((s : ZMod ℓ) - t) := by ring
    rw [this]
    exact Even.neg_pow (by decide) _
  have e2 : ∏ t ∈ Ico α s, (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1)) =
      (((s - α).factorial : ℕ) : ZMod ℓ) ^ 2 := by
    have h := prod_Ico_sub (ℓ := ℓ) s α s hα le_rfl
    rw [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one] at h
    rw [← h, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [if_neg (by have := mem_Ico.1 ht; omega)]
    ring
  have e3 : ∏ t ∈ Ico (s + 1) (A + 1), (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1)) =
      (((A - s).factorial : ℕ) : ZMod ℓ) ^ 2 := by
    rw [← prod_Ico_after (ℓ := ℓ) s A hsA, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [if_neg (by have := mem_Ico.1 ht; omega)]
  rw [e1, e2, e3]

theorem PcoreR_T4 (α A s : ℕ) (hα : α ≤ A + 1) (hsA : A + 1 ≤ s) :
    PcoreR ℓ α A s = (∏ t ∈ range α, ((s : ZMod ℓ) - t)) ^ 6 *
      (∏ t ∈ Ico α (A + 1), ((s : ZMod ℓ) - t)) ^ 2 := by
  unfold PcoreR
  rw [if_neg (by omega)]
  have hsplit : range (A + 1) = range α ∪ Ico α (A + 1) := by
    ext t; simp only [mem_range, mem_union, mem_Ico]; omega
  have hd1 : Disjoint (range α) (Ico α (A + 1)) := by
    rw [Finset.disjoint_left]; intro t h1 h2; simp only [mem_range, mem_Ico] at h1 h2; omega
  rw [hsplit, Finset.prod_union hd1]
  have e1 : ∏ t ∈ range α, (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1)) =
      (∏ t ∈ range α, ((s : ZMod ℓ) - t)) ^ 6 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [if_pos (mem_range.1 ht)]
    have : (((t : ℕ) : ZMod ℓ) - s) = -((s : ZMod ℓ) - t) := by ring
    rw [this]
    exact Even.neg_pow (by decide) _
  have e2 : ∏ t ∈ Ico α (A + 1), (((t : ℕ) : ZMod ℓ) - s) ^ (2 * (if t < α then 3 else 1)) =
      (∏ t ∈ Ico α (A + 1), ((s : ZMod ℓ) - t)) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [if_neg (by have := mem_Ico.1 ht; omega)]
    ring
  rw [e1, e2]

variable (ℓ) in
/-- `K = (A!)² / ((2n)!)³`. -/
noncomputable def Kc (n A : ℕ) : ZMod ℓ := (fz ℓ A) ^ 2 / (fz ℓ (2 * n)) ^ 3

/-- **Unit identity on `T2`.** -/
theorem unit_T2 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hα1 : 1 ≤ α)
    (hαs : α ≤ s) (hsA : s ≤ A) :
    chat ℓ A (2 * n) 0 1 s * PcoreR ℓ α A s =
      Kc ℓ n A * ∏ t ∈ range α, ((s : ZMod ℓ) - t) := by
  have hAl : A < ℓ := by omega
  have e1 : A + 0 * ℓ - s = A - s := by simp
  have e2 : 2 * n + s - 1 * ℓ = s - α := by omega
  unfold chat Kc
  rw [e1, e2, PcoreR_T2 α A s hαs hsA]
  have hX := prod_range_sub (ℓ := ℓ) s α hαs
  have hfA : fz ℓ A ≠ 0 := fz_ne_zero (p := ℓ) hAl
  have hf2 : fz ℓ (2 * n) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfs : fz ℓ s ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfAs : fz ℓ (A - s) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfsα : fz ℓ (s - α) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  unfold fz at *
  set X := ∏ t ∈ range α, ((s : ZMod ℓ) - t) with hXdef
  have hXne : X ≠ 0 := by
    intro h0; apply hfs; rw [← hX, h0, zero_mul]
  rw [← hX]
  rw [← hX] at hfs
  field_simp

/-- **Unit identity on `T4`** (Wilson reflection). -/
theorem unit_T4 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hα1 : 1 ≤ α)
    (hαA : α ≤ A + 1) (hAs : A + 1 ≤ s) (hsl : s < ℓ) :
    chat ℓ A (2 * n) 1 1 s * PcoreR ℓ α A s =
      Kc ℓ n A * ∏ t ∈ range α, ((s : ZMod ℓ) - t) := by
  have hAl : A < ℓ := by omega
  have e1 : A + 1 * ℓ - s = ℓ - 1 - (s - A - 1) := by omega
  have e2 : 2 * n + s - 1 * ℓ = s - α := by omega
  have hW := fact_reflect (p := ℓ) (s - A - 1) (by omega)
  unfold chat Kc
  rw [e1, e2, PcoreR_T4 α A s hαA hAs]
  have hX := prod_range_sub (ℓ := ℓ) s α (by omega)
  have hY := prod_Ico_sub (ℓ := ℓ) s α (A + 1) hαA hAs
  have hfA : fz ℓ A ≠ 0 := fz_ne_zero (p := ℓ) hAl
  have hf2 : fz ℓ (2 * n) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfs : fz ℓ s ≠ 0 := fz_ne_zero (p := ℓ) hsl
  have hfx : fz ℓ (s - A - 1) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfg : fz ℓ (ℓ - 1 - (s - A - 1)) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have hfsα : fz ℓ (s - α) ≠ 0 := fz_ne_zero (p := ℓ) (by omega)
  have e3 : s - (A + 1) = s - A - 1 := by omega
  rw [e3] at hY
  unfold fz at *
  set X := ∏ t ∈ range α, ((s : ZMod ℓ) - t) with hXdef
  set Y := ∏ t ∈ Ico α (A + 1), ((s : ZMod ℓ) - t) with hYdef
  set fx : ZMod ℓ := (((s - A - 1).factorial : ℕ) : ZMod ℓ) with hfxdef
  set g : ZMod ℓ := ((((ℓ - 1 - (s - A - 1)).factorial : ℕ)) : ZMod ℓ) with hgdef
  have hg2 : g ^ 2 = (fx ^ 2)⁻¹ := by
    have h1 : (fx * g) ^ 2 = 1 := by
      rw [hW, ← pow_mul, mul_comm, pow_mul]; simp
    field_simp
    rw [← h1]; ring
  rw [← hX]
  rw [← hX] at hfs
  have hYe : Y = ((s - α).factorial : ZMod ℓ) * fx⁻¹ := by
    field_simp; linear_combination hY
  rw [hYe, div_pow, mul_pow (_ : ZMod ℓ), hg2]
  field_simp

end CatalanCore.Lai.NV7

end
