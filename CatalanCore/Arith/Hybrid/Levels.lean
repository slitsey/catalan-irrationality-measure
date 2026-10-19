module

public import CatalanCore.Arith.Hybrid.Dual

@[expose] public section

/-!
# From levels to one-level duals

`tropExp r m p ≤ cOf p (r+m) + tropVal (HW p r m) + 2 (r+m) · #{e ∈ [2, E] : p^e ≤ 4N}`:
the level-1 term is the only one that needs the sharp duals (`Dual.lean`); higher levels cost
the trivial `2 (r + m)` and exist only for `p^e ≤ 4 (r+2m)`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

lemma blk_eq_zero_of_pow_large {p e N a : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hbig : 4 * N < p ^ e)
    (ha : a ≤ N) : blk (p ^ e) a = 0 := by
  unfold blk
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hs
  have hk' := Finset.mem_Icc.mp hk
  have hcop : Nat.Coprime k (4 * k - 1) := by
    have h1 : Nat.gcd k (4 * k - 1) ∣ k := Nat.gcd_dvd_left _ _
    have h2 : Nat.gcd k (4 * k - 1) ∣ 4 * k - 1 := Nat.gcd_dvd_right _ _
    have h3 : Nat.gcd k (4 * k - 1) ∣ 4 * k := h1.mul_left 4
    have h4 := Nat.dvd_sub h3 h2
    have e : 4 * k - (4 * k - 1) = 1 := by omega
    rw [e] at h4
    exact Nat.dvd_one.mp h4
  by_cases hpk : p ∣ k
  · have hc : Nat.Coprime (p ^ e) (4 * k - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      have := Nat.dvd_gcd hpk h
      rw [hcop] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    have := hc.dvd_of_dvd_mul_right hs
    have := Nat.le_of_dvd (by omega) this
    omega
  · have hc : Nat.Coprime (p ^ e) k := by
      apply Nat.Coprime.pow_left
      rwa [Nat.Prime.coprime_iff_not_dvd hp]
    have := hc.dvd_of_dvd_mul_left hs
    have := Nat.le_of_dvd (by omega) this
    omega

lemma wt_eq_zero_of_pow_large {p e N A B : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hbig : 4 * N < p ^ e)
    (hA : A ≤ N) (hB : B ≤ N) : wt (p ^ e) A B = 0 := by
  unfold wt
  rw [blk_eq_zero_of_pow_large hp he hbig hA, blk_eq_zero_of_pow_large hp he hbig hB]
  by_cases h : A = B
  · simp [h]
  · rw [if_neg h]
    have hnd : ¬ (((p ^ e : ℕ) : ℤ) ∣ (A : ℤ) - B) := by
      intro hd
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by
        rw [abs_lt]; constructor <;> omega)
      omega
    push_cast at hnd
    simp [hnd]

lemma tropVal_HW_zero (q r m : ℕ) (h : ∀ A B, A ≤ r + 2 * m → B ≤ r + 2 * m → wt q A B = 0) :
    tropVal (HW q r m) = 0 := by
  have : HW q r m = fun _ _ => 0 := by
    funext a b; exact h _ _ (Frame_hybRow_lt r m a).le (Frame_hybCol_lt r m b).le
  rw [this]; unfold tropVal; simp

lemma tropVal_HW_le_two (q r m : ℕ) : tropVal (HW q r m) ≤ 2 * (r + m) := by
  apply tropVal_le_of_forall
  intro σ
  calc ∑ b, HW q r m (σ b) b ≤ ∑ _b : Fin r ⊕ Fin m, 2 :=
        Finset.sum_le_sum fun b _ => wt_le_two _ _ _
    _ = 2 * (r + m) := by simp [mul_comm]

theorem tropExp_le (r m p : ℕ) (hr : 1 ≤ r) (hp : p.Prime) :
    tropExp r m p ≤ cOf p * (r + m) + tropVal (HW p r m) +
      2 * (r + m) * ((Finset.Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card := by
  unfold tropExp
  have h1 : tropVal (hybW r m p) ≤ cOf p * (r + m) +
      tropVal (fun a b => ∑ e ∈ Icc 1 (Elev r m), HW (p ^ e) r m a b) := by
    apply tropVal_le_of_forall
    intro σ
    have := le_tropVal (fun a b => ∑ e ∈ Icc 1 (Elev r m), HW (p ^ e) r m a b) σ
    have e1 : ∑ b, hybW r m p (σ b) b = cOf p * (r + m) +
        ∑ b, ∑ e ∈ Icc 1 (Elev r m), HW (p ^ e) r m (σ b) b := by
      unfold hybW levels
      rw [Finset.sum_add_distrib]
      simp [HW, mul_comm]
    rw [e1]
    exact Nat.add_le_add_left this _
  refine h1.trans ?_
  refine (Nat.add_le_add_left (tropVal_sum_le _ _) _).trans ?_
  have hE1 : 1 ≤ Elev r m := by unfold Elev; nlinarith
  have hsplit : Icc 1 (Elev r m) = insert 1 (Icc 2 (Elev r m)) := by
    ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  have hn : 1 ∉ Icc 2 (Elev r m) := by simp
  rw [hsplit, Finset.sum_insert hn, pow_one]
  have h3 : ∑ e ∈ Icc 2 (Elev r m), tropVal (HW (p ^ e) r m) ≤
      2 * (r + m) * ((Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m))).card := by
    rw [← Finset.sum_filter_add_sum_filter_not (Icc 2 (Elev r m))
      (fun e => p ^ e ≤ 4 * (r + 2 * m))]
    have hz : ∑ e ∈ (Icc 2 (Elev r m)).filter (fun e => ¬ p ^ e ≤ 4 * (r + 2 * m)),
        tropVal (HW (p ^ e) r m) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      have he' := Finset.mem_filter.mp he
      exact tropVal_HW_zero _ r m (fun A B hA hB => wt_eq_zero_of_pow_large hp
        (by have := (Finset.mem_Icc.mp he'.1).1; omega) (by omega) hA hB)
    rw [hz, add_zero]
    calc _ ≤ ∑ e ∈ (Icc 2 (Elev r m)).filter (fun e => p ^ e ≤ 4 * (r + 2 * m)), 2 * (r + m) :=
          Finset.sum_le_sum fun e _ => tropVal_HW_le_two _ r m
      _ = _ := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

end CatalanCore.Arith.Hybrid
