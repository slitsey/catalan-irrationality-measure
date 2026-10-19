module

public import CatalanCore.Arith.Hybrid.Dual

@[expose] public section

/-!
# From levels to one-level duals (general instance)

For a prime `p ∉ bad`:
`tropExp p ≤ cOf p (r+m) + tropVal (HW p) + 2 (r+m) · #{e ∈ [2, E] : p^e ≤ L N}`;
for `p ∈ bad`:
`tropExp p ≤ cOf p (r+m) + 2 (r+m) · #{e ∈ [1, E] : p^e ≤ Ebd N + N}`.
Only the level-1 term of good primes needs the sharp duals (`Dual.lean`, `Dual3.lean`).
-/

open Finset

namespace CatalanCore.Arith.Hybrid

variable {Fr : Frame} (I : HybInst Fr)

lemma tropVal_HW_zero (q r m : ℕ) (h : ∀ A B, A ≤ r + 2 * m → B ≤ r + 2 * m →
    wt I.lev q A B = 0) : tropVal (HW I.lev q r m) = 0 := by
  have : HW I.lev q r m = fun _ _ => 0 := by
    funext a b; exact h _ _ (hybRow_le r m a) (hybCol_le r m b)
  rw [this]; unfold tropVal; simp

lemma tropVal_HW_le_two (lev : ℕ → ℕ → ℕ) (q r m : ℕ) : tropVal (HW lev q r m) ≤ 2 * (r + m) := by
  apply tropVal_le_of_forall
  intro σ
  calc ∑ b, HW lev q r m (σ b) b ≤ ∑ _b : Fin r ⊕ Fin m, 2 :=
        Finset.sum_le_sum fun b _ => wt_le_two _ _ _ _
    _ = 2 * (r + m) := by simp [mul_comm]

private lemma trop_split (r m p : ℕ) :
    tropVal (hybW I r m p) ≤ cOf I p * (r + m) +
      tropVal (fun a b => ∑ e ∈ Icc 1 (Elev I r m), HW I.lev (p ^ e) r m a b) := by
  apply tropVal_le_of_forall
  intro σ
  have := le_tropVal (fun a b => ∑ e ∈ Icc 1 (Elev I r m), HW I.lev (p ^ e) r m a b) σ
  have e1 : ∑ b, hybW I r m p (σ b) b = cOf I p * (r + m) +
      ∑ b, ∑ e ∈ Icc 1 (Elev I r m), HW I.lev (p ^ e) r m (σ b) b := by
    unfold hybW levels
    rw [Finset.sum_add_distrib]
    simp [HW, mul_comm]
  rw [e1]
  exact Nat.add_le_add_left this _

/-- Good primes. -/
theorem tropExp_le (r m p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) (hb : p ∉ I.cd.bad) :
    tropExp I r m p ≤ cOf I p * (r + m) + tropVal (HW I.lev p r m) +
      2 * (r + m) * ((Finset.Icc 2 (Elev I r m)).filter
        (fun e => p ^ e ≤ I.cd.L * (r + 2 * m))).card := by
  unfold tropExp
  refine (trop_split I r m p).trans ?_
  refine (Nat.add_le_add_left (tropVal_sum_le _ _) _).trans ?_
  have hE1 : 1 ≤ Elev I r m := by unfold Elev; omega
  have hsplit : Icc 1 (Elev I r m) = insert 1 (Icc 2 (Elev I r m)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hn : 1 ∉ Icc 2 (Elev I r m) := by simp
  rw [hsplit, Finset.sum_insert hn, pow_one]
  have h3 : ∑ e ∈ Icc 2 (Elev I r m), tropVal (HW I.lev (p ^ e) r m) ≤
      2 * (r + m) * ((Icc 2 (Elev I r m)).filter (fun e => p ^ e ≤ I.cd.L * (r + 2 * m))).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 (Elev I r m))
      (fun e => p ^ e ≤ I.cd.L * (r + 2 * m))]
    have hz : ∑ e ∈ (Icc 2 (Elev I r m)).filter (fun e => ¬ p ^ e ≤ I.cd.L * (r + 2 * m)),
        tropVal (HW I.lev (p ^ e) r m) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have he' := Finset.mem_filter.mp he
      exact tropVal_HW_zero I _ r m (fun A B hA hB => wt_eq_zero_of_large I hp hb
        (by have := (Finset.mem_Icc.mp he'.1).1; omega) (by omega) hA hB)
    rw [hz, add_zero]
    calc _ ≤ ∑ e ∈ (Icc 2 (Elev I r m)).filter (fun e => p ^ e ≤ I.cd.L * (r + 2 * m)),
          2 * (r + m) := Finset.sum_le_sum fun e _ => tropVal_HW_le_two _ _ r m
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

/-- Bad primes: all levels, with the cruder threshold. -/
theorem tropExp_le_bad (r m p : ℕ) :
    tropExp I r m p ≤ cOf I p * (r + m) +
      2 * (r + m) * ((Finset.Icc 1 (Elev I r m)).filter
        (fun e => p ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m))).card := by
  unfold tropExp
  refine (trop_split I r m p).trans ?_
  refine (Nat.add_le_add_left (tropVal_sum_le _ _) _).trans ?_
  have h3 : ∑ e ∈ Icc 1 (Elev I r m), tropVal (HW I.lev (p ^ e) r m) ≤
      2 * (r + m) * ((Icc 1 (Elev I r m)).filter
        (fun e => p ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m))).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 (Elev I r m))
      (fun e => p ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m))]
    have hz : ∑ e ∈ (Icc 1 (Elev I r m)).filter
        (fun e => ¬ p ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m)),
        tropVal (HW I.lev (p ^ e) r m) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have he' := Finset.mem_filter.mp he
      exact tropVal_HW_zero I _ r m (fun A B hA hB => wt_eq_zero_of_Ebd I (by omega) hA hB)
    rw [hz, add_zero]
    calc _ ≤ ∑ e ∈ (Icc 1 (Elev I r m)).filter
          (fun e => p ^ e ≤ I.Ebd (r + 2 * m) + (r + 2 * m)), 2 * (r + m) :=
          Finset.sum_le_sum fun e _ => tropVal_HW_le_two _ _ r m
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

end CatalanCore.Arith.Hybrid
