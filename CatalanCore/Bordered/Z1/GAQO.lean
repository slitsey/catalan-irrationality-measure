module

public import CatalanCore.Bordered.Z1.GAent

/-!
# Z1.5 (order K < c < K + s): transfers to `X` and `Xᵀ`, with full eigen equations.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

section QO

variable (s m d : ℕ) (hd1 : 1 ≤ d) (hds : d < s)

local notation "θQ" => (-((s + m + d : ℕ) : ℝ))

lemma rq_d_zero : rq s m θQ (d : ℝ) = 0 := by
  unfold rq; push_cast; ring

omit hd1 in
lemma rq_pred_zero (hd : 1 ≤ d) : rq s m θQ (((d - 1 : ℕ) : ℝ) + 1) = 0 := by
  have : ((d - 1 : ℕ) : ℝ) + 1 = d := by rw [Nat.cast_sub hd]; push_cast; ring
  rw [this]; exact rq_d_zero s m d

include hd1 hds in
/-- Q-side: an `X′`-eigenvector supported on `k < d` gives an `X`-eigenvector there. -/
theorem transferQ (lam : ℝ) (v : ℕ → ℝ) (hsupp : ∀ k, d ≤ k → v k = 0)
    (hne : ∃ k, k < d ∧ v k ≠ 0)
    (hv : ∀ k : Fin s, (Xp s m θQ *ᵥ (fun j : Fin s => v j)) k = lam * v k) :
    ∃ v' : ℕ → ℝ, (∀ k, d ≤ k → v' k = 0) ∧ (∃ k, k < d ∧ v' k ≠ 0) ∧
      ∀ k : Fin s, (Xmat s m θQ *ᵥ (fun j : Fin s => v' j)) k = lam * v' k := by
  have hcpos : (0 : ℝ) ≤ ((s + m + d : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨w', h1, ⟨k0, hk0, hk0', hk0''⟩, h3⟩ := tri3_transfer (n := s)
    (fun i : ℕ => lq θQ ((i : ℝ) + 2)) (fun i : ℕ => Dq s m θQ (-((i : ℝ) + 1)))
    (fun i : ℕ => rq s m θQ ((i : ℝ) + 1)) (Xup s m θQ) (Xlow s m θQ) 0 d lam
    (fun i _ hi => by
      refine ⟨?_, Xup_ne_real s m i _ (by omega) ?_ ?_⟩
      · unfold lq
        have : (i : ℝ) + 1 < d := by exact_mod_cast hi
        have h2 : (i : ℝ) + 2 - 1 + θQ ≠ 0 := by push_cast; intro h; linarith
        have h3 : (i : ℝ) + 2 - 1 ≠ 0 := by intro h; have := Nat.cast_nonneg (α := ℝ) i; linarith
        exact mul_ne_zero (pow_ne_zero _ h3) (pow_ne_zero _ h2)
      · have : (i : ℝ) + 1 < d := by exact_mod_cast hi
        push_cast; intro h; linarith
      · have : (i : ℝ) + 1 < d := by exact_mod_cast hi
        push_cast; intro h; linarith)
    (fun i _ hi => Xmat_prod_eq s m i _ (by omega))
    v (fun k hk => by
      rcases hk with hk | hk
      · omega
      · exact hsupp k hk)
    (by obtain ⟨k, hk1, hk2⟩ := hne; exact ⟨k, Nat.zero_le _, hk1, hk2⟩)
    (fun k _ hk => hv k)
  refine ⟨w', fun k hk => h1 k (Or.inr hk), ⟨k0, hk0', hk0''⟩, ?_⟩
  intro k
  by_cases hk : (k : ℕ) < d
  · exact h3 k (Nat.zero_le _) hk
  · show (tri3 s _ _ _ *ᵥ (fun j : Fin s => w' j)) k = _
    rw [tri3_row]
    have e0 : w' k = 0 := h1 k (Or.inr (by omega))
    have e1 : w' ((k : ℕ) + 1) = 0 := h1 _ (Or.inr (by omega))
    have e2 : (if 0 < (k : ℕ) then rq s m θQ ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) * w' ((k : ℕ) - 1) else 0) = 0 := by
      by_cases h0 : 0 < (k : ℕ)
      · rw [if_pos h0]
        by_cases hkd : (k : ℕ) = d
        · have : (k : ℕ) - 1 = d - 1 := by omega
          rw [this, rq_pred_zero s m d hd1, zero_mul]
        · rw [h1 _ (Or.inr (by omega)), mul_zero]
      · rw [if_neg h0]
    rw [e0, e1, e2]; simp

include hd1 hds in
/-- O-side: an `X′`-eigenvector supported on `d ≤ k < s` gives a left eigenvector of `X`
(`Xᵀ ω = λ ω`) supported there. -/
theorem transferO (lam : ℝ) (w : ℕ → ℝ) (hsupp : ∀ k, k < d ∨ s ≤ k → w k = 0)
    (hne : ∃ k, d ≤ k ∧ k < s ∧ w k ≠ 0)
    (hw : ∀ k : Fin s, (Xp s m θQ *ᵥ (fun j : Fin s => w j)) k = lam * w k) :
    ∃ ω : ℕ → ℝ, (∀ k, k < d ∨ s ≤ k → ω k = 0) ∧ (∃ k, d ≤ k ∧ k < s ∧ ω k ≠ 0) ∧
      ∀ k : Fin s, ((Xmat s m θQ)ᵀ *ᵥ (fun j : Fin s => ω j)) k = lam * ω k := by
  have hcpos : (0 : ℝ) ≤ ((s + m + d : ℕ) : ℝ) := Nat.cast_nonneg _
  obtain ⟨w', h1, h2, h3⟩ := tri3_transfer (n := s)
    (fun i : ℕ => rq s m θQ ((i : ℝ) + 1)) (fun i : ℕ => Dq s m θQ (-((i : ℝ) + 1)))
    (fun i : ℕ => lq θQ ((i : ℝ) + 2)) (Xup s m θQ) (Xlow s m θQ) d s lam
    (fun i hi hi2 => by
      refine ⟨?_, Xup_ne_real s m i _ (by omega) ?_ ?_⟩
      · unfold rq
        have hs : (i : ℝ) + 1 < s := by exact_mod_cast hi2
        have hdi : (d : ℝ) ≤ i := by exact_mod_cast hi
        have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        refine mul_ne_zero (mul_ne_zero ?_ ?_) (pow_ne_zero _ ?_)
        · intro h; linarith
        · intro h; linarith
        · push_cast; intro h; linarith
      · have hs : (i : ℝ) + 1 < s := by exact_mod_cast hi2
        push_cast; intro h; linarith
      · have hdi : (d : ℝ) ≤ i := by exact_mod_cast hi
        push_cast; intro h; linarith)
    (fun i _ hi => by rw [mul_comm]; exact Xmat_prod_eq s m i _ (by omega))
    w hsupp hne (fun k _ _ => hw k)
  refine ⟨w', h1, h2, ?_⟩
  intro k
  have hT : (Xmat s m θQ)ᵀ = tri3 s (fun i : ℕ => rq s m θQ ((i : ℝ) + 1))
      (fun i : ℕ => Dq s m θQ (-((i : ℝ) + 1))) (fun i : ℕ => lq θQ ((i : ℝ) + 2)) :=
    tri3_transpose _ _ _
  rw [hT]
  by_cases hk : d ≤ (k : ℕ)
  · exact h3 k hk k.2
  · show (tri3 s _ _ _ *ᵥ (fun j : Fin s => w' j)) k = _
    rw [tri3_row]
    have e0 : w' k = 0 := h1 k (Or.inl (by omega))
    have e1 : (if (k : ℕ) + 1 < s then rq s m θQ (((k : ℕ) : ℝ) + 1) * w' ((k : ℕ) + 1) else 0) = 0 := by
      by_cases hk1 : (k : ℕ) + 1 < s
      · rw [if_pos hk1]
        by_cases hkd : (k : ℕ) + 1 = d
        · have : ((k : ℕ) : ℝ) + 1 = d := by exact_mod_cast hkd
          rw [this, rq_d_zero s m d, zero_mul]
        · rw [h1 _ (Or.inl (by omega)), mul_zero]
      · rw [if_neg hk1]
    have e2 : (if 0 < (k : ℕ) then lq θQ ((((k : ℕ) - 1 : ℕ) : ℝ) + 2) * w' ((k : ℕ) - 1) else 0) = 0 := by
      by_cases h0 : 0 < (k : ℕ)
      · rw [if_pos h0, h1 _ (Or.inl (by omega)), mul_zero]
      · rw [if_neg h0]
    rw [e0, e1, e2]; simp

end QO

end CatalanCore.Bordered.Z1
