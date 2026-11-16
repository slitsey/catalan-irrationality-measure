module

public import CatalanCore.Zeta5.CostIn.Gamma
public import CatalanCore.Zeta5.CostIn.Discrete
public import CatalanCore.Zeta5.CostIn.Legendre

@[expose] public section

/-!
# ZC17: `-v_p(S_K) - γ_p^in = p R(K/p) + O(M²)` uniformly for `3 ≤ K/p ≤ M`

For `K = 40 n`, `p` prime, `M ≥ 40`, `200 M² ≤ K`, `K/M < p ≤ K/3` (the inner range of `Frames.InnerAlloc`),
`R = Profile.Rg = -Γ - N₀` (`CostIn.Gamma.neg_Gam_sub_N0`):

* `zc17_wsum`   : `|-v_p(S_K) - 2∑w - p Rg(K/p)| ≤ 7500 M²` for every reserve `2M ≤ L₀ ≤ 13M + 10`;
* `zc17_gammaIn`: the same for `Normalizer.gammaIn` (reserve `4M + 10`, floor), constant `7501 M²`;
* **`zc17`**    : `|-LpKM M n p - p Rg(K/p)| ≤ 190 M³` (`LpKM = v_p(S_K) + γ_p^in` in this range);
* `zc17_exists` : the `O(M³)` statement with an absolute constant.

Proof: `two_W_real` splits `2∑w` into the zero class (`Zsum_abs : |Z₀| ≤ 462 M²`), the base class sum
`∑_c Hq` and the `E` extra rows (`eps_sum`, top-`E` layer cake over `ℓ_K = 2⌊K/p⌋ + a_c`); `class_vs_Phi`
compares them with `p Φ(K/p, T_p, E/p)` (`ClassSum.class_sum_approx`, error `≤ 6301 M²`);
`Phi_compare` replaces `(T_p, E/p)` by `(⌊2Hx⌋, u)` (`Phi_lip`, `Phi_cont`), so `p Φ = p Γ`, error `≤ 240 M²`;
`Legendre.vSK_approx` compares `v_p(S_K)` with `p N₀`.
-/

open Finset

namespace Apery.CostIn

lemma sum_range_lin_q (L : ℕ) (c : ℚ) :
    ∑ t ∈ range L, ((t : ℚ) + c) = (L : ℚ) * (L - 1) / 2 + L * c := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma lip_const_le {T Q M : ℝ} (hM : 40 ≤ M) (hT0 : 0 ≤ T) (hT : T ≤ 3 * M + 1) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ M) : |2 * T - 2 * Q - 4| + 2 ≤ 7 * M := by
  have : |2 * T - 2 * Q - 4| ≤ 6 * M := by
    rw [abs_le]; constructor <;> linarith
  linarith

lemma abs_min_sub_min_left (E a b : ℝ) : |min E a - min E b| ≤ |a - b| := by
  have := abs_min_sub_min_le_max E a E b
  rwa [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at this

lemma Hq_abs_le {T X1 X2 M : ℝ} (hM : 40 ≤ M) (hT0 : 0 ≤ T) (hT : T ≤ 3 * M) (hX1 : 0 ≤ X1)
    (hX1M : X1 ≤ M) (hX2 : 0 ≤ X2) (hX2M : X2 ≤ M) {α β : ℕ} (hα : α ≤ 2) (hβ : β ≤ 2) :
    |Hq T X1 X2 α β| ≤ 70 * M ^ 2 := by
  have hα' : (α : ℝ) ≤ 2 := by exact_mod_cast hα
  have hβ' : (β : ℝ) ≤ 2 := by exact_mod_cast hβ
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg _
  have hβ0 : (0 : ℝ) ≤ β := Nat.cast_nonneg _
  unfold Hq
  rw [abs_mul]
  have h1 : |T - 3 * (2 * X2 + β)| ≤ 7 * M := by
    rw [abs_le]; constructor <;> nlinarith
  have h2 : |T + 3 * (2 * X2 + β) - (2 * X1 + α) - 5| ≤ 10 * M := by
    rw [abs_le]; constructor <;> nlinarith
  calc _ ≤ (7 * M) * (10 * M) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
    _ = 70 * M ^ 2 := by ring

section inner
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma lK_eq {a : Fin (p / 2 + 1)} (ha : a ≠ 0) :
    lK p n a = 2 * (40 * n / p) + aCnt p (40 * n % p) (a : ℕ) := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  unfold lK
  exact SX_class H.p_odd h1 h2 (40 * n)

lemma lN_eq {a : Fin (p / 2 + 1)} (ha : a ≠ 0) :
    lN p n a = 2 * (3 * n / p) + aCnt p (3 * n % p) (a : ℕ) := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  unfold lN
  exact SX_class H.p_odd h1 h2 (3 * n)

lemma Bse_zero_eq : Bse p (40 * n) (3 * n) 0 =
    5 + 6 * ((3 * n / p : ℕ) * 2 : ℕ) - ((40 * n / p : ℕ) * 2 : ℕ) := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  unfold Bse
  simp only [if_true, Nat.cast_zero, Int.cast_zero, SX_zero]
  push_cast; ring

lemma tmin_ge : -(M : ℚ) - 3 ≤ tmin H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) := by
  unfold tmin
  refine Finset.le_inf' _ _ fun a ha => ?_
  have ha0 : a ≠ 0 := (Finset.mem_erase.mp ha).1
  rw [H.topw_eq a ha0]
  have h1 := lK_eq H ha0
  have h2 : aCnt p (40 * n % p) (a : ℕ) ≤ 2 := aCnt_le_two _ _ _
  have h3 := H.mK_lt
  have h4 : (lK p n a : ℚ) ≤ 2 * M := by
    have : lK p n a ≤ 2 * M := by omega
    exact_mod_cast this
  have h5 : (0 : ℚ) ≤ (innerT p n L0 : ℚ) := Nat.cast_nonneg _
  have h6 : (0 : ℚ) ≤ (if a ∈ epsSet p n L0 then 1 else 0) := by split_ifs <;> norm_num
  linarith

/-- The weights of the reserved zero class are `O(M)`. -/
lemma winner_zero_abs (i : Fin (innerL p n L0 0)) :
    |winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, i⟩| ≤ 33 * M := by
  have hz : (⟨0, i⟩ : Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)).1 = 0 := rfl
  unfold winner
  rw [if_pos hz]
  simp only
  have hB := Bse_zero_eq H
  have hi : (i : ℕ) < L0 := by have := i.isLt; have h0 := H.innerL_zero; omega
  have hL := H.hL0b
  have hmN := H.mN_lt
  have hmK := H.mK_lt
  have hM := H.hM
  have hi' : ((i : ℕ) : ℚ) + 1 ≤ 13 * M + 10 := by exact_mod_cast (by omega : (i : ℕ) + 1 ≤ 13 * M + 10)
  have hN' : ((3 * n / p : ℕ) : ℚ) + 1 ≤ M := by exact_mod_cast hmN
  have hK' : ((40 * n / p : ℕ) : ℚ) + 1 ≤ M := by exact_mod_cast hmK
  have hM' : (40 : ℚ) ≤ M := by exact_mod_cast hM
  have hN0 : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := Nat.cast_nonneg _
  have hK0 : (0 : ℚ) ≤ ((40 * n / p : ℕ) : ℚ) := Nat.cast_nonneg _
  have hi0 : (0 : ℚ) ≤ ((i : ℕ) : ℚ) := Nat.cast_nonneg _
  have ht := tmin_ge H
  rw [hB]
  push_cast
  have e1 : (2 * ((i : ℕ) : ℚ) + (5 + 6 * ((3 * n / p : ℕ) * 2) - (40 * n / p : ℕ) * 2 - 4) / 2) ≤ 33 * M := by
    nlinarith
  have e2 : -(M : ℚ) ≤ 2 * ((i : ℕ) : ℚ) + (5 + 6 * ((3 * n / p : ℕ) * 2) - (40 * n / p : ℕ) * 2 - 4) / 2 := by
    nlinarith
  have hQ : ∀ x y : ℚ, x ≤ 33 * M → -(M : ℚ) ≤ x → -(M : ℚ) - 3 ≤ y → |min x y| ≤ 33 * M := by
    intro x y hx1 hx2 hy
    rw [abs_le]
    constructor
    · rw [le_min_iff]; constructor <;> linarith
    · exact (min_le_left _ _).trans hx1
  have := hQ _ _ e1 e2 ht
  exact_mod_cast this

lemma winner_class_sum (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    ∑ t : Fin (innerL p n L0 a),
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨a, t⟩ =
      (innerL p n L0 a : ℚ) * ((innerL p n L0 a : ℚ) + Bse p (40 * n) (3 * n) a - 5) / 2 := by
  have e : ∀ t : Fin (innerL p n L0 a),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨a, t⟩ =
        ((t : ℕ) : ℚ) + (Bse p (40 * n) (3 * n) a - 4) / 2 := by
    intro t
    unfold winner
    simp only
    rw [if_neg ha]
  rw [Finset.sum_congr rfl fun t _ => e t,
    Fin.sum_univ_eq_sum_range (fun t => (t : ℚ) + (Bse p (40 * n) (3 * n) a - 4) / 2)
      (innerL p n L0 a), sum_range_lin_q]
  ring

lemma two_W_eq :
    2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s =
      2 * (∑ t : Fin (innerL p n L0 0),
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, t⟩)
      + ∑ a : Fin (p / 2 + 1), (if a = 0 then 0 else
          (innerL p n L0 a : ℚ) * ((innerL p n L0 a : ℚ) + Bse p (40 * n) (3 * n) a - 5)) := by
  rw [Fintype.sum_sigma]
  set G : Fin (p / 2 + 1) → ℚ := fun a => ∑ t : Fin (innerL p n L0 a),
    winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨a, t⟩ with hG
  have h1 : ∀ a, G a = (if a = 0 then G 0 else 0) + (if a = 0 then 0 else G a) := by
    intro a; by_cases h : a = 0
    · subst h; simp
    · simp [h]
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_add_distrib, Finset.sum_ite_eq' ,
    if_pos (Finset.mem_univ _), mul_add]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : a = 0
  · simp [h]
  · simp only [h, if_false]
    rw [hG]
    simp only
    rw [winner_class_sum H a h]; ring

lemma Bse_ne_zero_eq {a : Fin (p / 2 + 1)} (ha : a ≠ 0) :
    Bse p (40 * n) (3 * n) a = 6 * (lN p n a : ℚ) - (lK p n a : ℚ) := by
  have hna : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  unfold Bse lN lK
  rw [if_neg hna]; ring

/-- The class term `L(L + B - 5)` equals `Hq(…)` plus `ε(2T - ℓ_K - 4)`. -/
lemma class_term {a : Fin (p / 2 + 1)} (ha : a ≠ 0) :
    (((innerL p n L0 a : ℚ) * ((innerL p n L0 a : ℚ) + Bse p (40 * n) (3 * n) a - 5) : ℚ) : ℝ) =
      Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)
          (aCnt p (40 * n % p) a) (aCnt p (3 * n % p) a)
        + (if a ∈ epsSet p n L0 then
            (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - (aCnt p (40 * n % p) a : ℝ) - 4)
          else 0) := by
  have hs := H.innerL_spec a ha
  have hK := lK_eq H ha
  have hN := lN_eq H ha
  have hB := Bse_ne_zero_eq H ha
  have hsR : (innerL p n L0 a : ℝ) + 3 * (lN p n a : ℝ) =
      (innerT p n L0 : ℝ) + (if a ∈ epsSet p n L0 then 1 else 0) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hs
    split_ifs at this ⊢ <;> push_cast at this ⊢ <;> linarith
  have hKR : (lK p n a : ℝ) = 2 * ((40 * n / p : ℕ) : ℝ) + (aCnt p (40 * n % p) a : ℝ) := by
    exact_mod_cast hK
  have hNR : (lN p n a : ℝ) = 2 * ((3 * n / p : ℕ) : ℝ) + (aCnt p (3 * n % p) a : ℝ) := by
    exact_mod_cast hN
  push_cast
  rw [hB]
  push_cast
  unfold Hq
  by_cases he : a ∈ epsSet p n L0
  · simp only [he, ↓reduceIte] at hsR ⊢
    have hL : (innerL p n L0 a : ℝ) = (innerT p n L0 : ℝ) + 1 - 3 * (lN p n a : ℝ) := by linarith
    rw [hL, hKR, hNR]; ring
  · simp only [he, ↓reduceIte] at hsR ⊢
    have hL : (innerL p n L0 a : ℝ) = (innerT p n L0 : ℝ) - 3 * (lN p n a : ℝ) := by linarith
    rw [hL, hKR, hNR]; ring

/-- **Decomposition of `2 ∑ w`** into the zero class, the base class sum and the extras. -/
lemma two_W_real :
    ((2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
        winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s : ℚ) : ℝ) =
      2 * ((∑ t : Fin (innerL p n L0 0),
          winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, t⟩ : ℚ) : ℝ)
      + ∑ c ∈ Icc 1 (p / 2),
          Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)
            (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c)
      + ∑ a ∈ epsSet p n L0,
          (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - (aCnt p (40 * n % p) a : ℝ) - 4) := by
  rw [two_W_eq H]
  push_cast
  obtain ⟨hsub, hcard, hprop⟩ := H.epsSet_spec
  have h0 : (0 : Fin (p / 2 + 1)) ∉ epsSet p n L0 := fun h0 =>
    (Finset.mem_erase.mp (hsub h0)).1 rfl
  set Hc : ℕ → ℝ := fun c => Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)
    (aCnt p (40 * n % p) c) (aCnt p (3 * n % p) c) with hHc
  set Rn : ℕ → ℝ := fun c =>
    2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - (aCnt p (40 * n % p) c : ℝ) - 4 with hRn
  have hpt : ∀ a : Fin (p / 2 + 1),
      (((if a = 0 then 0 else (innerL p n L0 a : ℚ) *
        ((innerL p n L0 a : ℚ) + Bse p (40 * n) (3 * n) a - 5) : ℚ)) : ℝ) =
        (if (a : ℕ) = 0 then 0 else Hc a) + (if a ∈ epsSet p n L0 then Rn a else 0) := by
    intro a
    by_cases ha : a = 0
    · subst ha; simp [h0]
    · have hna : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
      rw [if_neg ha, if_neg hna]
      have := class_term H ha
      push_cast at this ⊢
      simpa [hHc, hRn] using this
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib]
  have hA : ∑ a : Fin (p / 2 + 1), (if (a : ℕ) = 0 then 0 else Hc a) =
      ∑ c ∈ Icc 1 (p / 2), Hc c := by
    rw [sum_fin_succ_real (p / 2) (fun c => if c = 0 then 0 else Hc c)]
    simp only [if_true, zero_add]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [if_neg (by have := (Finset.mem_Icc.mp hc).1; omega)]
  have hB : ∑ a : Fin (p / 2 + 1), (if a ∈ epsSet p n L0 then Rn a else 0) =
      ∑ a ∈ epsSet p n L0, Rn a := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hA, hB]
  ring

/-- The extras: `∑_{a ∈ ε} (2T - 2Q - a_c - 4) = E(2T - 2Q - 4) - min(E, n₁) - min(E, n₂)`. -/
lemma eps_sum :
    ∑ a ∈ epsSet p n L0,
        (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - (aCnt p (40 * n % p) a : ℝ) - 4) =
      (innerE p n L0 : ℝ) * (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4)
        - ((min (innerE p n L0)
              ((Icc 1 (p / 2)).filter fun c => 1 ≤ aCnt p (40 * n % p) c).card : ℕ) : ℝ)
        - ((min (innerE p n L0)
              ((Icc 1 (p / 2)).filter fun c => 2 ≤ aCnt p (40 * n % p) c).card : ℕ) : ℝ) := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨hsub, hcard, hprop⟩ := H.epsSet_spec
  have htop : ∀ a ∈ epsSet p n L0, ∀ b ∈ (Finset.univ.erase (0 : Fin (p / 2 + 1))), b ∉ epsSet p n L0 →
      aCnt p (40 * n % p) (b : ℕ) ≤ aCnt p (40 * n % p) (a : ℕ) := by
    intro a ha b hb hbS
    have h1 := hprop a ha b hb hbS
    have ha0 : a ≠ 0 := (Finset.mem_erase.mp (hsub ha)).1
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    rw [lK_eq H ha0, lK_eq H hb0] at h1
    omega
  have hsum := sum_top_two (Finset.univ.erase (0 : Fin (p / 2 + 1))) (epsSet p n L0)
    (fun a : Fin (p / 2 + 1) => aCnt p (40 * n % p) (a : ℕ)) (fun a _ => aCnt_le_two _ _ _) hsub htop
  rw [hcard, card_filter_fin_erase (fun c => 1 ≤ aCnt p (40 * n % p) c),
    card_filter_fin_erase (fun c => 2 ≤ aCnt p (40 * n % p) c)] at hsum
  rw [Finset.sum_congr rfl fun (a : Fin (p / 2 + 1)) _ => (by ring : (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ)
      - (aCnt p (40 * n % p) (a : ℕ) : ℝ) - 4) = (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4)
      - (aCnt p (40 * n % p) (a : ℕ) : ℝ)), Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul]
  have hsumR : ∑ a ∈ epsSet p n L0, (aCnt p (40 * n % p) (a : ℕ) : ℝ) =
      ((min (innerE p n L0) ((Icc 1 (p / 2)).filter fun c => 1 ≤ aCnt p (40 * n % p) c).card : ℕ) : ℝ)
      + ((min (innerE p n L0) ((Icc 1 (p / 2)).filter fun c => 2 ≤ aCnt p (40 * n % p) c).card : ℕ) : ℝ) := by
    rw [← Nat.cast_add, ← hsum, Nat.cast_sum]
  rw [hsumR]
  ring

/-- The sum of all row weights `∑ w` (a rational). -/
noncomputable def Wsum : ℚ :=
  ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
    winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s

/-- The weights of the reserved zero class. -/
noncomputable def Zsum : ℚ :=
  ∑ t : Fin (innerL p n L0 0), winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, t⟩

lemma Zsum_abs : |(Zsum H : ℚ)| ≤ 462 * (M : ℚ) ^ 2 := by
  unfold Zsum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ t : Fin (innerL p n L0 0),
      |winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, t⟩| ≤ 33 * M := by
    intro t
    have := winner_zero_abs H t
    exact_mod_cast this
  calc _ ≤ ∑ t : Fin (innerL p n L0 0), (33 * (M : ℚ)) := Finset.sum_le_sum fun t _ => hb t
    _ = (innerL p n L0 0 : ℚ) * (33 * M) := by simp
    _ ≤ 14 * (M : ℚ) * (33 * M) := by
      have h0 := H.innerL_zero
      have hL := H.hL0b
      have hM := H.hM
      have : (innerL p n L0 0 : ℚ) ≤ 14 * M := by
        have : innerL p n L0 0 ≤ 14 * M := by omega
        exact_mod_cast this
      have : (0 : ℚ) ≤ 33 * M := by positivity
      nlinarith
    _ = 462 * (M : ℚ) ^ 2 := by ring

end inner

section xfacts
variable {n p : ℕ}

lemma x_floor (hp : 0 < p) : ⌊((40 * n : ℕ) : ℝ) / (p : ℝ)⌋ = ((40 * n / p : ℕ) : ℤ) :=
  floor_nat_div (40 * n) p

lemma x_fract : Int.fract (((40 * n : ℕ) : ℝ) / (p : ℝ)) = ((40 * n % p : ℕ) : ℝ) / (p : ℝ) :=
  Int.fract_div_natCast_eq_div_natCast_mod

lemma ax_eq (hp : 0 < p) : 3 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ)) = ((3 * n : ℕ) : ℝ) / (p : ℝ) := by
  have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast; field_simp

lemma ax_floor (hp : 0 < p) : ⌊3 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ))⌋ = ((3 * n / p : ℕ) : ℤ) := by
  rw [ax_eq hp]; exact floor_nat_div (3 * n) p

lemma ax_fract (hp : 0 < p) :
    Int.fract (3 / 40 * (((40 * n : ℕ) : ℝ) / (p : ℝ))) = ((3 * n % p : ℕ) : ℝ) / (p : ℝ) := by
  rw [ax_eq hp]; exact Int.fract_div_natCast_eq_div_natCast_mod

end xfacts


section cmp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

/-- **Discrete class sum versus the allocation model** `Φ(K/p, T_p, E/p)`:
`|2 ∑ w - 2 Z₀ - p Φ| ≤ 6301 M²`. -/
lemma class_vs_Phi :
    |((2 * Wsum H : ℚ) : ℝ) - 2 * ((Zsum H : ℚ) : ℝ) -
      (p : ℝ) * Phi (((40 * n : ℕ) : ℝ) / (p : ℝ)) (innerT p n L0 : ℝ)
        ((innerE p n L0 : ℝ) / (p : ℝ))| ≤ 6301 * (M : ℝ) ^ 2 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hp0 : 0 < p := H.prime.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hm := H.p_odd
  have hv : 40 * n % p < p := Nat.mod_lt _ hp0
  have hv' : 3 * n % p < p := Nat.mod_lt _ hp0
  have hmain := two_W_real H
  rw [eps_sum H] at hmain
  change ((2 * Wsum H : ℚ) : ℝ) = _ at hmain
  -- bounds for the class weights
  have hT : innerT p n L0 ≤ 3 * M := H.innerT_le
  have hQ := H.mK_lt
  have hqN := H.mN_lt
  have hM := H.hM
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hTR : (innerT p n L0 : ℝ) ≤ 3 * M := by exact_mod_cast hT
  have hQR : ((40 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hQ.le
  have hNR : ((3 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hqN.le
  have hcoef := sum_abs_coef_le
    (Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)) (70 * (M : ℝ) ^ 2)
    (fun a b ha hb => Hq_abs_le hMR (Nat.cast_nonneg _) hTR (Nat.cast_nonneg _) hQR
      (Nat.cast_nonneg _) hNR ha hb)
  have hcl := class_sum_approx hm hv hv'
    (Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ))
  -- the extras
  have h1 := n1_approx (v := 40 * n % p) hm hv
  have h2 := n2_approx (v := 40 * n % p) hm hv
  set N1 := ((Icc 1 (p / 2)).filter fun c => 1 ≤ aCnt p (40 * n % p) c).card with hN1
  set N2 := ((Icc 1 (p / 2)).filter fun c => 2 ≤ aCnt p (40 * n % p) c).card with hN2
  set E := innerE p n L0 with hE
  set v := 40 * n % p with hvdef
  have hf : (p : ℝ) * min ((v : ℝ) / p) (1 / 2) = min (v : ℝ) (p / 2) := by
    rw [mul_min_of_nonneg _ _ hpR.le, mul_div_cancel₀ _ hpR.ne']; congr 1; ring
  have hg : (p : ℝ) * max 0 ((v : ℝ) / p - 1 / 2) = max 0 ((v : ℝ) - p / 2) := by
    rw [mul_max_of_nonneg _ _ hpR.le, mul_zero, mul_sub, mul_div_cancel₀ _ hpR.ne']; congr 2; ring
  have hmin1 : (p : ℝ) * min ((E : ℝ) / p) (min ((v : ℝ) / p) (1 / 2)) =
      min (E : ℝ) (min (v : ℝ) (p / 2)) := by
    rw [mul_min_of_nonneg _ _ hpR.le, mul_div_cancel₀ _ hpR.ne', hf]
  have hmin2 : (p : ℝ) * min ((E : ℝ) / p) (max 0 ((v : ℝ) / p - 1 / 2)) =
      min (E : ℝ) (max 0 ((v : ℝ) - p / 2)) := by
    rw [mul_min_of_nonneg _ _ hpR.le, mul_div_cancel₀ _ hpR.ne', hg]
  have hA1 := abs_min_sub_min_left (E : ℝ) (N1 : ℝ) (min (v : ℝ) (p / 2))
  have hA2 := abs_min_sub_min_left (E : ℝ) (N2 : ℝ) (max 0 ((v : ℝ) - p / 2))
  unfold Phi
  rw [x_floor hp0, ax_floor hp0, x_fract, ax_fract hp0]
  simp only [Int.cast_natCast]
  have hPE : (p : ℝ) * ((E : ℝ) / p * (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4)) =
      (E : ℝ) * (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4) := by
    field_simp
  have hcast1 : (((min E N1 : ℕ)) : ℝ) = min (E : ℝ) (N1 : ℝ) := Nat.cast_min E N1
  have hcast2 : (((min E N2 : ℕ)) : ℝ) = min (E : ℝ) (N2 : ℝ) := Nat.cast_min E N2
  rw [hcast1, hcast2] at hmain
  have hexp : (p : ℝ) * (Cint (Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ))
      ((v : ℝ) / p) (((3 * n % p : ℕ) : ℝ) / p) +
      (E : ℝ) / p * (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4)
      - min ((E : ℝ) / p) (min ((v : ℝ) / p) (1 / 2))
      - min ((E : ℝ) / p) (max 0 ((v : ℝ) / p - 1 / 2))) =
      (p : ℝ) * Cint (Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ))
        ((v : ℝ) / p) (((3 * n % p : ℕ) : ℝ) / p)
      + (E : ℝ) * (2 * (innerT p n L0 : ℝ) - 2 * ((40 * n / p : ℕ) : ℝ) - 4)
      - min (E : ℝ) (min (v : ℝ) (p / 2)) - min (E : ℝ) (max 0 ((v : ℝ) - p / 2)) := by
    rw [mul_sub, mul_sub, mul_add, hPE, hmin1, hmin2]
  rw [hexp]
  have hcl' : |∑ c ∈ Icc 1 (p / 2), Hq (innerT p n L0 : ℝ) ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)
      (aCnt p v c) (aCnt p (3 * n % p) c) - (p : ℝ) * Cint (Hq (innerT p n L0 : ℝ)
        ((40 * n / p : ℕ) : ℝ) ((3 * n / p : ℕ) : ℝ)) ((v : ℝ) / p) (((3 * n % p : ℕ) : ℝ) / p)| ≤
      6300 * (M : ℝ) ^ 2 := by
    refine hcl.trans ?_
    nlinarith [hcoef]
  have hZ : ((Zsum H : ℚ) : ℝ) = ((∑ t : Fin (innerL p n L0 0),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨0, t⟩ : ℚ) : ℝ) := rfl
  rw [hmain, hZ]
  have hB1 := hA1.trans h1
  have hB2 := hA2.trans h2
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  rw [abs_le] at hcl' hB1 hB2 ⊢
  constructor <;> linarith [hcl'.1, hcl'.2, hB1.1, hB1.2, hB2.1, hB2.2]

set_option maxHeartbeats 1000000 in
/-- **`T_p` against `⌊2Hx⌋`; allocation continuity.** `|p Φ(x, T_p, E/p) - p Γ(x)| ≤ 240 M²`. -/
lemma Phi_compare :
    |(p : ℝ) * Phi (((40 * n : ℕ) : ℝ) / (p : ℝ)) (innerT p n L0 : ℝ) ((innerE p n L0 : ℝ) / (p : ℝ))
      - (p : ℝ) * Gam (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤ 240 * (M : ℝ) ^ 2 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hp0 : 0 < p := H.prime.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hm := H.p_odd
  set x : ℝ := ((40 * n : ℕ) : ℝ) / (p : ℝ) with hxdef
  have hx : (p : ℝ) * x = 40 * n := by rw [hxdef]; push_cast; field_simp
  -- natural number bookkeeping
  have htot := H.tot_eq
  have hE := H.E_lt
  have hT := H.innerT_le
  have hL0a := H.hL0a
  have hL0b := H.hL0b
  have hM := H.hM
  have hK := H.hK
  have hpM := H.p200
  have hq := H.mN_lt
  have hQ := H.mK_lt
  have hL37 : L0 ≤ 37 * n := by nlinarith
  have hq3 : 3 * n / p ≤ 3 * n := Nat.div_le_self _ _
  unfold innerTot at htot
  have htot' : (p / 2) * innerT p n L0 + innerE p n L0 + L0 + 3 * (3 * n / p) = 46 * n := by
    generalize 3 * n / p = b at *
    omega
  have htotR : ((p : ℝ) - 1) / 2 * (innerT p n L0 : ℝ) + (innerE p n L0 : ℝ) + (L0 : ℝ)
      + 3 * ((3 * n / p : ℕ) : ℝ) = 46 * n := by
    have h1 : ((p / 2 : ℕ) : ℝ) = ((p : ℝ) - 1) / 2 := by
      have : (p : ℝ) = 2 * ((p / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hm.symm
      linarith
    have h2 : (((p / 2) * innerT p n L0 + innerE p n L0 + L0 + 3 * (3 * n / p) : ℕ) : ℝ) = 46 * n := by
      rw [htot']; push_cast; ring
    push_cast at h2
    rw [h1] at h2
    linarith
  -- real facts
  set Tp : ℝ := (innerT p n L0 : ℝ) with hTp
  set E : ℝ := (innerE p n L0 : ℝ) with hEdef
  set r : ℝ := 2 * (L0 : ℝ) + 6 * ((3 * n / p : ℕ) : ℝ) - Tp with hr
  have hTpM : Tp ≤ 3 * M := by rw [hTp]; exact_mod_cast hT
  have hTp0 : 0 ≤ Tp := Nat.cast_nonneg _
  have hL0aR : 2 * (M : ℝ) ≤ L0 := by exact_mod_cast hL0a
  have hL0bR : (L0 : ℝ) ≤ 13 * M + 10 := by exact_mod_cast hL0b
  have hqR : ((3 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hq.le
  have hqR0 : (0 : ℝ) ≤ ((3 * n / p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQR : ((40 * n / p : ℕ) : ℝ) ≤ M := by exact_mod_cast hQ.le
  have hQR0 : (0 : ℝ) ≤ ((40 * n / p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have hpMR : 200 * (M : ℝ) < p := by exact_mod_cast hpM
  have hER : 2 * E + 3 ≤ p := by
    have : 2 * innerE p n L0 + 3 ≤ p := by omega
    rw [hEdef]; exact_mod_cast this
  have hE0 : 0 ≤ E := Nat.cast_nonneg _
  have hr1 : (M : ℝ) ≤ r := by rw [hr]; linarith
  have hr2 : r ≤ 33 * M := by rw [hr]; linarith
  -- p (2Hx - T_p) = 2E + r
  have hkey : (p : ℝ) * (2 * (23 / 20) * x - Tp) = 2 * E + r := by
    have : (p : ℝ) * (2 * (23 / 20) * x) = 92 * n := by nlinarith [hx]
    nlinarith [htotR, this]
  have hD0 : 0 < 2 * (23 / 20) * x - Tp := by
    by_contra hc
    push Not at hc
    have : (p : ℝ) * (2 * (23 / 20) * x - Tp) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpR.le hc
    rw [hkey] at this
    linarith
  have hD2 : 2 * (23 / 20) * x - Tp < 2 := by
    by_contra hc
    push Not at hc
    have : (p : ℝ) * 2 ≤ (p : ℝ) * (2 * (23 / 20) * x - Tp) := mul_le_mul_of_nonneg_left hc hpR.le
    rw [hkey] at this
    linarith
  -- the floor `T = ⌊2Hx⌋`
  have hTfle : (Tf x : ℝ) ≤ 2 * (23 / 20) * x := Int.floor_le _
  have hTflt : 2 * (23 / 20) * x < (Tf x : ℝ) + 1 := Int.lt_floor_add_one _
  have hT1 : ((innerT p n L0 : ℕ) : ℤ) ≤ Tf x := by
    unfold Tf
    exact Int.le_floor.mpr (by push_cast; linarith)
  have hT2 : Tf x < (innerT p n L0 : ℤ) + 2 := by
    have : (Tf x : ℝ) < (innerT p n L0 : ℤ) + 2 := by push_cast; linarith
    exact_mod_cast this
  have hu0 := uf_nonneg x
  have hu1 := uf_lt_half x
  have hTeq := Tf_eq x
  have hQfl : ((⌊x⌋ : ℤ) : ℝ) = ((40 * n / p : ℕ) : ℝ) := by
    rw [hxdef, x_floor hp0, Int.cast_natCast]
  -- Lipschitz in `e`, scaled by `p`
  have step : ∀ T e e' : ℝ, 0 ≤ T → T ≤ 3 * M + 1 →
      |(p : ℝ) * Phi x T e - (p : ℝ) * Phi x T e'| ≤ 7 * M * |(p : ℝ) * e - (p : ℝ) * e'| := by
    intro T e e' hT0 hT1
    have hl := Phi_lip x T e e'
    have hc := lip_const_le (T := T) (Q := ((40 * n / p : ℕ) : ℝ)) (M := M) hMR hT0 hT1 hQR0 hQR
    rw [hQfl] at hl
    have e1 : (p : ℝ) * Phi x T e - (p : ℝ) * Phi x T e' = (p : ℝ) * (Phi x T e - Phi x T e') := by ring
    have e2 : (p : ℝ) * e - (p : ℝ) * e' = (p : ℝ) * (e - e') := by ring
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos hpR]
    calc (p : ℝ) * |Phi x T e - Phi x T e'| ≤ (p : ℝ) * ((7 * M) * |e - e'|) := by
          refine mul_le_mul_of_nonneg_left (hl.trans ?_) hpR.le
          exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
      _ = 7 * M * ((p : ℝ) * |e - e'|) := by ring
  have hpE : (p : ℝ) * ((innerE p n L0 : ℝ) / p) = E := by
    rw [hEdef]; field_simp
  rw [Gam_eq_Phi x]
  rcases (by omega : Tf x = innerT p n L0 ∨ Tf x = (innerT p n L0 : ℤ) + 1) with hA | hB
  · -- `T = T_p`
    have hTfR : (Tf x : ℝ) = Tp := by rw [hA]; simp [hTp]
    rw [hTfR]
    have hpu : (p : ℝ) * uf x = E + r / 2 := by
      have : uf x = (2 * (23 / 20) * x - Tp) / 2 := by
        have h := hTeq; rw [hTfR] at h; linarith
      rw [this]
      calc (p : ℝ) * ((2 * (23 / 20) * x - Tp) / 2) = ((p : ℝ) * (2 * (23 / 20) * x - Tp)) / 2 := by ring
        _ = E + r / 2 := by rw [hkey]; ring
    refine (step Tp ((innerE p n L0 : ℝ) / p) (uf x) hTp0 (by linarith)).trans ?_
    rw [hpE, hpu]
    have : |E - (E + r / 2)| = r / 2 := by
      rw [show E - (E + r / 2) = -(r / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    rw [this]
    nlinarith
  · -- `T = T_p + 1`
    have hTfR : (Tf x : ℝ) = Tp + 1 := by rw [hB]; simp [hTp]
    rw [hTfR]
    have hpu : (p : ℝ) * uf x = (2 * E + r - p) / 2 := by
      have : uf x = (2 * (23 / 20) * x - Tp - 1) / 2 := by
        have h := hTeq; rw [hTfR] at h; linarith
      rw [this]
      calc (p : ℝ) * ((2 * (23 / 20) * x - Tp - 1) / 2) = ((p : ℝ) * (2 * (23 / 20) * x - Tp) - p) / 2 := by ring
        _ = (2 * E + r - p) / 2 := by rw [hkey]
    have hD1 : 1 ≤ 2 * (23 / 20) * x - Tp := by
      have : (Tf x : ℝ) ≤ 2 * (23 / 20) * x := hTfle
      linarith
    have hge : (p : ℝ) ≤ 2 * E + r := by
      have : (p : ℝ) * 1 ≤ (p : ℝ) * (2 * (23 / 20) * x - Tp) := mul_le_mul_of_nonneg_left hD1 hpR.le
      rw [hkey] at this; linarith
    have s1 := step Tp ((innerE p n L0 : ℝ) / p) (1 / 2) hTp0 (by linarith)
    have s2 := step (Tp + 1) 0 (uf x) (by linarith) (by linarith)
    have hc := Phi_cont x Tp
    rw [hpE] at s1
    have e1 : (p : ℝ) * (1 / 2 : ℝ) = p / 2 := by ring
    have e2 : (p : ℝ) * (0 : ℝ) = 0 := by ring
    rw [e1] at s1
    rw [e2, hpu] at s2
    have b1 : |E - p / 2| ≤ r / 2 := by
      rw [abs_le]; constructor <;> linarith
    have b2 : |(0 : ℝ) - (2 * E + r - p) / 2| ≤ r / 2 := by
      rw [abs_le]; constructor <;> linarith
    have t1 : |(p : ℝ) * Phi x Tp ((innerE p n L0 : ℝ) / p) - (p : ℝ) * Phi x Tp (1 / 2)| ≤
        7 * M * (r / 2) := s1.trans (mul_le_mul_of_nonneg_left b1 (by linarith))
    have t2 : |(p : ℝ) * Phi x (Tp + 1) 0 - (p : ℝ) * Phi x (Tp + 1) (uf x)| ≤ 7 * M * (r / 2) :=
      s2.trans (mul_le_mul_of_nonneg_left b2 (by linarith))
    rw [hc] at t2
    have : |(p : ℝ) * Phi x Tp ((innerE p n L0 : ℝ) / p) - (p : ℝ) * Phi x (Tp + 1) (uf x)| ≤
        7 * M * (r / 2) + 7 * M * (r / 2) := by
      calc _ = |((p : ℝ) * Phi x Tp ((innerE p n L0 : ℝ) / p) - (p : ℝ) * Phi x Tp (1 / 2))
              + ((p : ℝ) * Phi x Tp (1 / 2) - (p : ℝ) * Phi x (Tp + 1) (uf x))| := by ring_nf
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add t1 t2)
    refine this.trans ?_
    nlinarith

/-- **ZC17 for a general reserve `L₀`**: `-v_p(S_K) - 2∑w = p R(K/p) + O(M²)` with the explicit
constant `7500`, where `R = Rg` is the closed profile (`-Γ - N₀ = Rg`). -/
theorem zc17_wsum :
    |-(vSK n p : ℝ) - ((2 * Wsum H : ℚ) : ℝ) -
        (p : ℝ) * CatalanCore.Zeta5.Profile.Rg (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤
      7500 * (M : ℝ) ^ 2 := by
  have hp0 : 0 < p := H.prime.pos
  have hn : 0 < n := H.n_pos
  have hp2 : 2 * (40 * n) < p ^ 2 := by have := H.p_sq; omega
  obtain ⟨hv0, hv1⟩ := vSK_approx H.prime hn hp2
  have hdiv : 2 * (37 * n) / p < 2 * M := by
    rw [Nat.div_lt_iff_lt_mul hp0]
    have := H.hpM
    nlinarith
  have hdivR : ((2 * (37 * n) / p : ℕ) : ℝ) ≤ 2 * M := by exact_mod_cast hdiv.le
  set x : ℝ := ((40 * n : ℕ) : ℝ) / (p : ℝ) with hxdef
  have hR := neg_Gam_sub_N0 x
  have hZ := Zsum_abs H
  have hZR : |((Zsum H : ℚ) : ℝ)| ≤ 462 * (M : ℝ) ^ 2 := by exact_mod_cast hZ
  have hC := class_vs_Phi H
  have hF := Phi_compare H
  rw [← hxdef] at hC hF
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast H.hM
  have hM2 : (2 : ℝ) * M ≤ 35 * (M : ℝ) ^ 2 := by nlinarith
  have e1 : -(vSK n p : ℝ) - ((2 * Wsum H : ℚ) : ℝ) - (p : ℝ) * CatalanCore.Zeta5.Profile.Rg x =
      -((vSK n p : ℝ) - (p : ℝ) * N0 x) -
        (((2 * Wsum H : ℚ) : ℝ) - 2 * ((Zsum H : ℚ) : ℝ) - (p : ℝ) * Phi x (innerT p n L0 : ℝ)
          ((innerE p n L0 : ℝ) / p))
        - 2 * ((Zsum H : ℚ) : ℝ)
        - ((p : ℝ) * Phi x (innerT p n L0 : ℝ) ((innerE p n L0 : ℝ) / p) - (p : ℝ) * Gam x) := by
    rw [← hR]; ring
  rw [e1]
  rw [abs_le] at hC hF hZR ⊢
  constructor <;> linarith [hC.1, hC.2, hF.1, hF.2, hZR.1, hZR.2]

end cmp


section final

/-- The inner hypotheses for the reserve `L₀ = 4M + 10` used in `gammaIn`. -/
lemma innerHyp_gammaIn {M n p : ℕ} (hp : p.Prime) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n)
    (hpM : 40 * n < p * M) (hp3 : 3 * p ≤ 40 * n) : InnerHyp p n M (4 * M + 10) :=
  ⟨hp, hM, hK, hpM, hp3, by omega, by omega⟩

/-- **ZC17, `γ_p^in` as defined in `Normalizer.gammaIn`** (floor of `2∑w`, reserve `4M + 10`):
`|-v_p(S_K) - γ_p^in - p R(K/p)| ≤ 7501 M²`, uniformly for `K/M < p ≤ K/3`, `M ≥ 40`, `200 M² ≤ K`. -/
theorem zc17_gammaIn {M n p : ℕ} (hp : p.Prime) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n)
    (hpM : 40 * n < p * M) (hp3 : 3 * p ≤ 40 * n) :
    |-(vSK n p : ℝ) - (gammaIn M n p : ℝ) -
        (p : ℝ) * CatalanCore.Zeta5.Profile.Rg (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤
      7501 * (M : ℝ) ^ 2 := by
  have H := innerHyp_gammaIn hp hM hK hpM hp3
  have h1 := zc17_wsum H
  have hg : gammaIn M n p = ⌊(2 * Wsum H : ℚ)⌋ := by
    unfold gammaIn
    rw [dif_pos H]
    rfl
  have hfl1 : ((⌊(2 * Wsum H : ℚ)⌋ : ℤ) : ℝ) ≤ ((2 * Wsum H : ℚ) : ℝ) := by
    have := Int.floor_le (2 * Wsum H : ℚ)
    exact_mod_cast this
  have hfl2 : ((2 * Wsum H : ℚ) : ℝ) < ((⌊(2 * Wsum H : ℚ)⌋ : ℤ) : ℝ) + 1 := by
    have := Int.lt_floor_add_one (2 * Wsum H : ℚ)
    exact_mod_cast this
  rw [hg]
  rw [abs_le] at h1 ⊢
  have hM2 : (1 : ℝ) ≤ (M : ℝ) ^ 2 := by
    have : (40 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  constructor <;> linarith [h1.1, h1.2]

/-- **ZC17** in the form used by the normaliser: for `p` prime with `K/M < p ≤ K/3`,
`|-L_p - p R(K/p)| ≤ 190 M³`, where `L_p = v_p(S_K) + γ_p^in` is `Normalizer.LpKM`
and `R = Profile.Rg` equals `-Γ - N₀` (`neg_Gam_sub_N0`). -/
theorem zc17 {M n p : ℕ} (hp : p.Prime) (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n)
    (hpM : 40 * n < p * M) (hp3 : 3 * p ≤ 40 * n) :
    |-(LpKM M n p : ℝ) - (p : ℝ) * CatalanCore.Zeta5.Profile.Rg (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤
      190 * (M : ℝ) ^ 3 := by
  have h := zc17_gammaIn hp hM hK hpM hp3
  have hL : LpKM M n p = vSK n p + gammaIn M n p := by
    unfold LpKM
    rw [if_neg (not_le.mpr hpM), if_pos hp3]
  rw [hL, Int.cast_add]
  have hMR : (40 : ℝ) ≤ M := by exact_mod_cast hM
  have e : -((vSK n p : ℝ) + (gammaIn M n p : ℝ)) = -(vSK n p : ℝ) - (gammaIn M n p : ℝ) := by ring
  rw [e]
  refine h.trans ?_
  nlinarith [sq_nonneg (M : ℝ)]

/-- The ledger form of ZC17: there is an absolute constant `C` with
`|-L_p - p R(K/p)| ≤ C M³` for all `M ≥ 40`, `K = 40 n ≥ 200 M²`, `K/M < p ≤ K/3`. -/
theorem zc17_exists : ∃ C : ℝ, ∀ {M n p : ℕ}, p.Prime → 40 ≤ M → 200 * M ^ 2 ≤ 40 * n →
    40 * n < p * M → 3 * p ≤ 40 * n →
    |-(LpKM M n p : ℝ) - (p : ℝ) * CatalanCore.Zeta5.Profile.Rg (((40 * n : ℕ) : ℝ) / (p : ℝ))| ≤
      C * (M : ℝ) ^ 3 :=
  ⟨190, fun hp hM hK hpM hp3 => zc17 hp hM hK hpM hp3⟩

end final

end Apery.CostIn
