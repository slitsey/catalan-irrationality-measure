module

public import CatalanCore.ThmA.UnitLU
public import CatalanCore.Linalg.ProdWindow
public import CatalanCore.ThmA.ChainKdet
public import CatalanCore.ThmA.ChainY

/-!
# `ℓ`-adic units among the chain Krylov determinants (over `ℚ`)
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {l : ℕ} [hl : Fact l.Prime]

lemma charGt_rat (N : ℕ) : CharGt ℚ N := fun n hn _ => Nat.cast_ne_zero.2 hn.ne'

lemma LU_sub_nat {a b : ℕ} (hab : a ≠ b) (ha : a < l) (hb : b < l) :
    LU l ((a : ℚ) - (b : ℚ)) := by
  have : (a : ℚ) - (b : ℚ) = (((a : ℤ) - (b : ℤ) : ℤ) : ℚ) := by push_cast; ring
  rw [this]
  exact LU_intCast_lt (by omega) (by omega)

/-- `LU` of a natural-number expression given as a cast identity. -/
lemma LU_of_eq_nat {q : ℚ} {n : ℕ} (h : q = (n : ℚ)) (h0 : 0 < n) (hn : n < l) : LU l q := by
  rw [h]; exact LU_natCast_lt h0 hn

lemma LU_small_div_prod {n : ℕ} (x y : Fin n → ℚ)
    (hnum : ∀ i j : Fin n, i < j → LU l ((x j - x i) * (y j - y i)))
    (hden : ∀ i j : Fin n, LU l (x i + y j)) :
    LU l ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((x j - x i) * (y j - y i))) /
      ∏ i : Fin n, ∏ j : Fin n, (x i + y j)) :=
  LU.div (LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => hnum i j (mem_Ioi.1 hj))
    (LU.prod _ _ fun i _ => LU.prod _ _ fun j _ => hden i j)

lemma LU_bb_nat {K σ m : ℕ} (hm : 0 < m) (hmK : m + K < l) (hmσ : m < σ) (hσ : σ < l) :
    LU l (bb (K : ℚ) (σ : ℚ) (m : ℚ)) := by
  unfold bb
  have h1 : LU l (m : ℚ) := LU_natCast_lt hm (by omega)
  have h2 : LU l ((m : ℚ) + K) := LU_of_eq_nat (n := m + K) (by push_cast; ring) (by omega) hmK
  have h3 : LU l ((σ : ℚ) - m) := LU_of_eq_nat (n := σ - m) (by
    rw [Nat.cast_sub hmσ.le]) (by omega) (by omega)
  exact (h1.pow 2).mul h2 |>.mul h3

lemma LU_bt_nat {K σ j : ℕ} (hj : j + 1 < K) (hσ : σ + j + 1 < l) (hK : K < l) :
    LU l (bt (K : ℚ) (σ : ℚ) (j : ℚ)) := by
  unfold bt
  have h1 : LU l ((j : ℚ) + 1) := LU_of_eq_nat (n := j + 1) (by push_cast; ring) (by omega) (by omega)
  have h2 : LU l ((K : ℚ) - 1 - j) := LU_of_eq_nat (n := K - (j + 1)) (by
    rw [Nat.cast_sub (by omega)]; push_cast; ring) (by omega) (by omega)
  have h3 : LU l ((σ : ℚ) + j + 1) := LU_of_eq_nat (n := σ + j + 1) (by push_cast; ring) (by omega) hσ
  exact ((h1.pow 2).mul h2).mul h3

/-- `u(T, c_σ)` is an `ℓ`-unit (all integers involved are below `ℓ`). -/
theorem LU_T_down (K σ : ℕ) (hK : 1 ≤ K) (hσ : K ≤ σ) (hl' : σ + K ≤ l) :
    LU l (kdet (Tmat ℚ K σ) (cvec ℚ K (σ : ℚ))) := by
  rw [kdet_T_down_eq (charGt_rat (σ + 2 * K)) K σ hK hσ (by omega)]
  refine LU.mul (LU.prod _ _ fun k _ => LU.prod _ _ fun j hj => ?_) (LU_small_div_prod _ _ ?_ ?_)
  · have hj' := mem_range.1 hj
    have hk := k.2
    have e : yDown ℚ σ j - 1 = ((σ - (j + 1) : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    show LU l (bb (K : ℚ) (σ : ℚ) (yDown ℚ σ j - 1))
    rw [e]
    exact LU_bb_nat (by omega) (by omega) (by omega) (by omega)
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.2
    have h1 : LU l (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := LU_sub_nat (by omega) (by omega) (by omega)
    have h2 : LU l (yDown ℚ σ j - yDown ℚ σ i) := by
      have : yDown ℚ σ j - yDown ℚ σ i = -(((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := by
        unfold yDown; ring
      rw [this]; exact h1.neg
    exact h1.mul h2
  · intro i j
    have hi := i.2
    have hj := j.2
    have e : ((i : ℕ) : ℚ) + yDown ℚ σ j = (((i : ℕ) + σ - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub (by omega)]; unfold yDown; push_cast; ring
    exact LU_of_eq_nat e (by omega) (by omega)

lemma cancel_aux (U Num SS PP : ℚ) (hPP : PP ≠ 0) (hSS : SS ≠ 0) :
    U * PP * (Num / (SS * PP)) = U * (Num / SS) := by
  field_simp

/-- `u(T, c_{σ+1})` is an `ℓ`-unit when `σ + K < ℓ`: the unit-ratio ledger (window identity). -/
theorem LU_T_up (K σ : ℕ) (hK : 1 ≤ K) (hσ : 1 ≤ σ) (hl' : σ + K + 1 ≤ l) :
    LU l (kdet (Tmat ℚ K σ) (cvec ℚ K ((σ : ℚ) + 1))) := by
  rw [kdet_T_up_eq (charGt_rat (σ + 2 * K)) K σ hK hσ (by omega)]
  set g : ℕ → ℚ := fun j => bb (K : ℚ) (σ : ℚ) (yUp ℚ σ j) with hg
  have hP0 : (∏ k : Fin K, ∏ j ∈ Finset.range (k : ℕ), g j) =
      (∏ j ∈ range K, (-((((σ + 1 + j : ℕ) : ℚ)) ^ 2 * ((1 + j : ℕ) : ℚ))) ^ (K - 1 - j)) *
        PP ℚ K (σ + 1) := by
    rw [Fin.prod_univ_eq_prod_range (fun k => ∏ j ∈ range k, g j) K, prod_prod_range_eq K g, PP,
      ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [← mul_pow]
    congr 1
    simp only [hg, bb, yUp]; push_cast; ring
  have hDen : (∏ i : Fin K, ∏ j : Fin K, (((i : ℕ) : ℚ) + yUp ℚ σ j)) =
      SS ℚ K (σ + 1) * PP ℚ K (σ + 1) := by
    rw [← QQ_eq, QQ]
    rw [← Fin.prod_univ_eq_prod_range (fun a => ∏ b ∈ range K, (((σ + 1 + a + b : ℕ)) : ℚ)) K]
    refine prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun b => (((σ + 1 + (i : ℕ) + b : ℕ)) : ℚ)) K]
    refine prod_congr rfl fun j _ => ?_
    simp only [yUp]; push_cast; ring
  rw [hP0, hDen]
  have hPP : PP ℚ K (σ + 1) ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hSS : LU l (SS ℚ K (σ + 1)) :=
    LU.prod _ _ fun t ht => (LU_natCast_lt (by omega) (by have := mem_range.1 ht; omega)).pow _
  have hU : LU l (∏ j ∈ range K, (-((((σ + 1 + j : ℕ) : ℚ)) ^ 2 * ((1 + j : ℕ) : ℚ))) ^ (K - 1 - j)) :=
    LU.prod _ _ fun j hj => by
      have hj' := mem_range.1 hj
      exact ((((LU_natCast_lt (by omega) (by omega)).pow 2).mul
        (LU_natCast_lt (by omega) (by omega))).neg).pow _
  have hNum : LU l (∏ i : Fin K, ∏ j ∈ Finset.Ioi i,
      ((((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) * (yUp ℚ σ j - yUp ℚ σ i))) :=
    LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => by
      have hij0 : i < j := mem_Ioi.1 hj
      have hij : (i : ℕ) < j := hij0
      have hj2 := j.2
      have h1 : LU l (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := LU_sub_nat (by omega) (by omega) (by omega)
      have : yUp ℚ σ j - yUp ℚ σ i = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by unfold yUp; ring
      rw [this]; exact h1.mul h1
  rw [cancel_aux _ _ _ _ hPP hSS.1]
  exact hU.mul (hNum.div hSS)

end CatalanCore.ThmA
