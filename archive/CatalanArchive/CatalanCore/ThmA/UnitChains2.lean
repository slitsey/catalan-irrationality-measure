module

public import CatalanCore.ThmA.UnitChains
public import CatalanCore.ThmA.KStep

/-!
# `ℓ`-adic units among the remaining K-step determinants (over `ℚ`)
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable {l : ℕ} [hl : Fact l.Prime]

/-- The window ledger: a chain product with weighted factors `(c+n+j)^(n-1-j)` over a Cauchy
denominator `∏_{a,b<n}(c+a+b)` is an `ℓ`-unit when `c + n ≤ ℓ`. -/
lemma LU_ledger (n c : ℕ) (hc : 1 ≤ c) (hcn : c + n ≤ l) (g A : ℕ → ℚ) (Num Den : ℚ)
    (hg : ∀ j, j < n → g j = -(A j) * (((c + n + j : ℕ)) : ℚ))
    (hA : ∀ j, j < n → LU l (A j)) (hNum : LU l Num) (hDen : Den = QQ ℚ n c) :
    LU l ((∏ k : Fin n, ∏ j ∈ range (k : ℕ), g j) * (Num / Den)) := by
  have hP0 : (∏ k : Fin n, ∏ j ∈ range (k : ℕ), g j) =
      (∏ j ∈ range n, (-(A j)) ^ (n - 1 - j)) * PP ℚ n c := by
    rw [Fin.prod_univ_eq_prod_range (fun k => ∏ j ∈ range k, g j) n, prod_prod_range_eq n g, PP,
      ← prod_mul_distrib]
    refine prod_congr rfl fun j hj => ?_
    rw [← mul_pow, hg j (mem_range.1 hj)]
  have hPP : PP ℚ n c ≠ 0 :=
    prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  have hSS : LU l (SS ℚ n c) :=
    LU.prod _ _ fun t ht => (LU_natCast_lt (by omega) (by have := mem_range.1 ht; omega)).pow _
  have hU : LU l (∏ j ∈ range n, (-(A j)) ^ (n - 1 - j)) :=
    LU.prod _ _ fun j hj => ((hA j (mem_range.1 hj)).neg).pow _
  rw [hP0, hDen, QQ_eq, cancel_aux _ _ _ _ hPP hSS.1]
  exact hU.mul (hNum.div hSS)

/-- `u(T, e₀)` is an `ℓ`-unit. -/
theorem LU_Te0 (K σ : ℕ) (hKl : K < l) (hl' : σ + K ≤ l) :
    LU l (kdet (Tmat ℚ K σ) (ev K 0)) := by
  unfold Tmat
  rw [kdet_tri_ev_eq]
  exact LU.prod _ _ fun k _ => LU.prod _ _ fun j hj => by
    have hj' := mem_range.1 hj
    have hk := k.2
    exact LU_bt_nat (K := K) (σ := σ) (j := j) (by omega) (by omega) hKl

/-- `det [e₀ | C]` is an `ℓ`-unit. -/
theorem LU_border (m : ℕ) (hl' : 2 * m < l) :
    LU l (border (Cmat ℚ (m + 1) m) (ev (m + 1) 0)).det := by
  have hxy : ∀ i j : Fin m, (((i : ℕ) : ℚ) + 1) + (((j : ℕ) : ℚ) + 1) ≠ 0 := fun i j => by
    have : (0 : ℚ) < (((i : ℕ) : ℚ) + 1) + (((j : ℕ) : ℚ) + 1) := by positivity
    exact this.ne'
  have key := cauchy_det (fun a : Fin m => ((a : ℕ) : ℚ) + 1) (fun b : Fin m => ((b : ℕ) : ℚ) + 1) hxy
  rw [border_det_eq, key]
  refine (LU_small_div_prod (l := l) (fun a : Fin m => ((a : ℕ) : ℚ) + 1)
    (fun b : Fin m => ((b : ℕ) : ℚ) + 1) ?_ ?_)
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.2
    have h1 : LU l (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := LU_sub_nat (by omega) (by omega) (by omega)
    have e : ((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by ring
    show LU l ((((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1)) * (((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1)))
    rw [e]; exact h1.mul h1
  · intro i j
    have hi := i.2
    have hj := j.2
    exact LU_of_eq_nat (n := (i : ℕ) + (j : ℕ) + 2) (by push_cast; ring) (by omega) (by omega)

/-- `u(Y, c̃₀)` is an `ℓ`-unit (`K = m+1`, `s = m`). -/
theorem LU_Y0 (m : ℕ) (hm : 1 ≤ m) (hl' : 2 * m < l) :
    LU l (kdet (Ymat ℚ (m + 1) m) (ctil ℚ m 0)) := by
  have hl0 : bt ((m + 1 : ℕ) : ℚ) (m : ℚ) (((0 : ℕ) : ℚ) - 1) = 0 := by simp [bt_neg_one]
  have := kdet_Y_eq (charGt_rat (m + 1 + 2 * m)) (m + 1) m 0 hl0 (by omega) hm
  simp only [Nat.cast_zero] at this
  rw [this]
  refine LU.mul (LU.prod _ _ fun k _ => LU.prod _ _ fun j hj => ?_) (LU_small_div_prod _ _ ?_ ?_)
  · have hj' := mem_range.1 hj
    have hk := k.2
    have e : (((0 + j : ℕ)) : ℚ) = (j : ℚ) := by simp
    rw [e]
    exact LU_bt_nat (K := m + 1) (σ := m) (j := j) (by omega) (by omega) (by omega)
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    have hj := j.2
    have h1 : LU l (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := LU_sub_nat (by omega) (by omega) (by omega)
    have e : ((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by ring
    have e2 : (((0 + (j : ℕ) : ℕ)) : ℚ) - (((0 + (i : ℕ) : ℕ)) : ℚ) =
        ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by simp
    show LU l ((((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1)) *
      ((((0 + (j : ℕ) : ℕ)) : ℚ) - (((0 + (i : ℕ) : ℕ)) : ℚ)))
    rw [e, e2]; exact h1.mul h1
  · intro i j
    have hi := i.2
    have hj := j.2
    exact LU_of_eq_nat (n := (i : ℕ) + 1 + (0 + (j : ℕ))) (by push_cast; ring) (by omega) (by omega)

/-- `u(Y, c̃_K)` is an `ℓ`-unit when `2K ≤ ℓ` (`K = m+1`, `s = m`): window ledger. -/
theorem LU_Yk (m : ℕ) (hm : 1 ≤ m) (hl' : 2 * (m + 1) ≤ l) :
    LU l (kdet (Ymat ℚ (m + 1) m) (ctil ℚ m (((m + 1 : ℕ)) : ℚ))) := by
  have hl0 : bt ((m + 1 : ℕ) : ℚ) (m : ℚ) ((((m + 1 : ℕ)) : ℚ) - 1) = 0 := by
    unfold bt; push_cast; ring
  rw [kdet_Y_eq (charGt_rat (m + 1 + 2 * m + (m + 1))) (m + 1) m (m + 1) hl0 (by omega) hm]
  refine LU_ledger m (m + 2) (by omega) (by omega)
    (fun j => bt ((m + 1 : ℕ) : ℚ) (m : ℚ) (((m + 1 + j : ℕ)) : ℚ))
    (fun j => (((m + 2 + j : ℕ) : ℚ)) ^ 2 * ((1 + j : ℕ) : ℚ)) _ _ ?_ ?_ ?_ ?_
  · intro j hj
    show bt ((m + 1 : ℕ) : ℚ) (m : ℚ) (((m + 1 + j : ℕ)) : ℚ) = _
    unfold bt; push_cast; ring
  · intro j hj
    exact ((LU_natCast_lt (by omega) (by omega)).pow 2).mul (LU_natCast_lt (by omega) (by omega))
  · refine LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => ?_
    have hij : i < j := mem_Ioi.1 hj
    have hij' : (i : ℕ) < j := hij
    have hj2 := j.2
    have h1 : LU l (((j : ℕ) : ℚ) - ((i : ℕ) : ℚ)) := LU_sub_nat (by omega) (by omega) (by omega)
    have e : ((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1) = ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by ring
    have e2 : (((m + 1 + (j : ℕ) : ℕ)) : ℚ) - (((m + 1 + (i : ℕ) : ℕ)) : ℚ) =
        ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) := by push_cast; ring
    show LU l ((((j : ℕ) : ℚ) + 1 - (((i : ℕ) : ℚ) + 1)) *
      ((((m + 1 + (j : ℕ) : ℕ)) : ℚ) - (((m + 1 + (i : ℕ) : ℕ)) : ℚ)))
    rw [e, e2]; exact h1.mul h1
  · rw [QQ]
    rw [← Fin.prod_univ_eq_prod_range (fun a => ∏ b ∈ range m, (((m + 2 + a + b : ℕ)) : ℚ)) m]
    refine prod_congr rfl fun i _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun b => (((m + 2 + (i : ℕ) + b : ℕ)) : ℚ)) m]
    refine prod_congr rfl fun j _ => ?_
    push_cast; ring

end CatalanCore.ThmA
