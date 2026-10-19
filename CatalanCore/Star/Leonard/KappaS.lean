module

public import CatalanCore.Bordered.Hankel.HahnUnit
public import CatalanCore.Bordered.Hankel.Basis
public import CatalanCore.Star.Leonard.DeltaHunif

/-!
# `κ_S` is an `ℓ`-unit (GI closed form, units part)

`κ_S = (∏_{i≤m} 2i)^n · ∏_{i=1}^{n-1} H_i(w) · ∏_{r=1}^{n-1} H_r(v) / H_n(w)^{n-1}` with
`n = K - m`, node weights `w_a = 1/(a!(K-1-a)!)²` on `{0..K-1}` (a binomial weight, `LU_hk`) and column
weights `v_j = (S-j)(S+1-j)_{2m}` on `{1..S-1}` (a Hahn weight `(2m+1)!·W_{2m+1,0,S-2}`, `LU_hkH`).
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA CatalanCore.Bordered.Hankel

namespace CatalanCore.Star.Leonard

lemma momH_smul (s : Finset ℕ) (w e : ℕ → ℚ) (c : ℚ) (k : ℕ) :
    momH s (fun x => c * w x) e k = c ^ k * momH s w e k := by
  unfold momH
  have : (Matrix.of fun a b : Fin k => ∑ x ∈ s, c * w x * e x ^ ((a : ℕ) + b)) =
      c • (Matrix.of fun a b : Fin k => ∑ x ∈ s, w x * e x ^ ((a : ℕ) + b)) := by
    ext a b
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [this, Matrix.det_smul, Fintype.card_fin]

lemma momH_congr (s : Finset ℕ) (w w' e : ℕ → ℚ) (h : ∀ x ∈ s, w x = w' x) (k : ℕ) :
    momH s w e k = momH s w' e k := by
  unfold momH
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl fun x hx => by rw [h x hx]

/-- node weights `1/(a!(K-1-a)!)²` -/
def wnodeK (K a : ℕ) : ℚ := (((a.factorial * (K - 1 - a).factorial : ℕ) : ℚ)⁻¹) ^ 2

/-- column weights `v_j = (S-j)(S+1-j)_{2m}` -/
def vcolS (m S j : ℕ) : ℚ := ((S : ℚ) - j) * pochr ((S : ℚ) + 1 - j) (2 * m)

variable {ℓ : ℕ} [Fact ℓ.Prime]

lemma wnode_eq (K a : ℕ) (ha : a < K) :
    wnodeK K a = (((K - 1).factorial : ℚ) ^ 2)⁻¹ * Wt (K - 1) (K - 1) a := by
  have h := Nat.choose_mul_factorial_mul_factorial (show a ≤ K - 1 by omega)
  have h' : ((K - 1).choose a : ℚ) * ((a.factorial * (K - 1 - a).factorial : ℕ) : ℚ) =
      ((K - 1).factorial : ℚ) := by exact_mod_cast (by rw [mul_assoc] at h; exact h)
  have hne : ((a.factorial * (K - 1 - a).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)).ne'
  have hf : ((K - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hc : ((K - 1).choose a : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  unfold wnodeK Wt
  rw [← h']
  field_simp

theorem LU_nodeH (K i : ℕ) (hK : 1 ≤ K) (hi : i ≤ K) (hl : 2 * K ≤ ℓ + 1) :
    LU ℓ (momH (range K) (wnodeK K) (fun x => (x : ℚ)) i) := by
  have e1 : momH (range K) (wnodeK K) (fun x => (x : ℚ)) i =
      momH (range K) (fun x => (((K - 1).factorial : ℚ) ^ 2)⁻¹ * Wt (K - 1) (K - 1) x)
        (fun x => (x : ℚ)) i :=
    momH_congr _ _ _ _ (fun x hx => wnode_eq K x (Finset.mem_range.1 hx)) i
  rw [e1, momH_smul]
  obtain ⟨N, rfl⟩ : ∃ N, K = N + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← hk_eq_momH]
  refine LU.mul (LU.pow (LU.inv (LU.pow (LU_factorial (by omega)) 2)) i) ?_
  exact LU_hk ℓ i N N le_rfl (by omega) (by omega)

lemma hkH_eq_momH (α β N k : ℕ) :
    hkH α β N k = momH (range (N + 1)) (WtH α β N) (fun x => (x : ℚ)) k := by
  rw [← gram_monic (range (N + 1)) (WtH α β N) (fun x => (x : ℚ))
    (fun i => descPochhammer ℚ i) (fun i => monic_descPochhammer ℚ i)
    (fun i => descPochhammer_natDegree ℚ i) k]
  rfl

lemma pochr_nat_eq (y L : ℕ) :
    pochr (((y + 1 : ℕ) : ℚ)) L = (L.factorial : ℚ) * ((L + y).choose y : ℚ) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose y L
  have h2 : (y + 1).ascFactorial L = ∏ i ∈ range L, (y + 1 + i) := Nat.ascFactorial_eq_prod_range _ _
  have e : (y + L).choose L = (L + y).choose y := by
    rw [add_comm y L]; exact Nat.choose_symm_add
  unfold pochr
  have : ((∏ i ∈ range L, (y + 1 + i) : ℕ) : ℚ) = (L.factorial : ℚ) * ((L + y).choose y : ℚ) := by
    rw [← h2, h, e]; push_cast; ring
  rw [← this]; push_cast; rfl

lemma vcol_eq (m N y : ℕ) (hy : y ≤ N) :
    vcolS m (N + 2) (N + 1 - y) = ((2 * m + 1).factorial : ℚ) * WtH (2 * m + 1) 0 N y := by
  unfold vcolS WtH
  have e1 : ((N + 1 - y : ℕ) : ℚ) = (N : ℚ) + 1 - y := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (((N + 2 : ℕ) : ℚ) - ((N + 1 - y : ℕ) : ℚ)) = (y : ℚ) + 1 := by rw [e1]; push_cast; ring
  have e3 : (((N + 2 : ℕ) : ℚ) + 1 - ((N + 1 - y : ℕ) : ℚ)) = (y : ℚ) + 1 + 1 := by
    rw [e1]; push_cast; ring
  rw [e2, e3]
  have h := pochr_nat_eq y (2 * m + 1)
  rw [pochr_succ_left] at h
  have e4 : ((y + 1 : ℕ) : ℚ) = (y : ℚ) + 1 := by push_cast; ring
  rw [e4] at h
  have e5 : (0 + N - y).choose (N - y) = 1 := by
    rw [zero_add]; exact Nat.choose_self _
  rw [h, e5]
  push_cast
  ring

lemma sum_Icc_reflect (F : ℕ → ℚ) (N : ℕ) :
    ∑ j ∈ Icc 1 (N + 1), F j = ∑ y ∈ range (N + 1), F (N + 1 - y) := by
  refine Finset.sum_nbij' (fun j => N + 1 - j) (fun y => N + 1 - y) ?_ ?_ ?_ ?_ ?_
  · intro j hj; simp only [Finset.mem_Icc, Finset.mem_range] at hj ⊢; omega
  · intro y hy; simp only [Finset.mem_Icc, Finset.mem_range] at hy ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj; omega
  · intro y hy; simp only [Finset.mem_range] at hy; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj
    congr 1; omega

lemma colsH_eq (m N r : ℕ) :
    momH (Icc 1 (N + 1)) (vcolS m (N + 2)) (fun x => (x : ℚ)) r =
      ((2 * m + 1).factorial : ℚ) ^ r * hkH (2 * m + 1) 0 N r := by
  rw [hkH_eq_momH, ← momH_smul]
  set Wv : ℕ → ℚ := fun y => ((2 * m + 1).factorial : ℚ) * WtH (2 * m + 1) 0 N y with hWv
  -- monic basis in the variable `y`
  have h2 := gram_monic (range (N + 1)) Wv (fun x => (x : ℚ))
    (fun i => (Polynomial.X - Polynomial.C ((N : ℚ) + 1)) ^ i)
    (fun i => (Polynomial.monic_X_sub_C _).pow _)
    (fun i => by rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]) r
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    mul_assoc] at h2
  rw [← h2]
  have e1 : (Matrix.of fun a b : Fin r => ∑ x ∈ Icc 1 (N + 1), vcolS m (N + 2) x * (x : ℚ) ^ ((a : ℕ) + b)) =
      Matrix.diagonal (fun a : Fin r => (-1 : ℚ) ^ (a : ℕ)) *
        (Matrix.of fun a b : Fin r => ∑ x ∈ range (N + 1), Wv x * (((x : ℚ) - ((N : ℚ) + 1)) ^ (a : ℕ) *
          ((x : ℚ) - ((N : ℚ) + 1)) ^ (b : ℕ))) *
        Matrix.diagonal (fun a : Fin r => (-1 : ℚ) ^ (a : ℕ)) := by
    ext a b
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    rw [sum_Icc_reflect (fun x => vcolS m (N + 2) x * (x : ℚ) ^ ((a : ℕ) + b)) N]
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := Finset.mem_range.1 hy
    simp only [hWv]
    rw [vcol_eq m N y (by omega), Nat.cast_sub (by omega)]
    push_cast
    have hu : ((N : ℚ) + 1 - (y : ℚ)) = -((y : ℚ) - ((N : ℚ) + 1)) := by ring
    rw [hu, neg_pow, pow_add, pow_add]
    ring
  unfold momH
  rw [e1, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hs : (∏ a : Fin r, (-1 : ℚ) ^ (a : ℕ)) * (∏ a : Fin r, (-1 : ℚ) ^ (a : ℕ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun a _ => ?_
    rw [← pow_add, ← two_mul, pow_mul]; simp
  linear_combination (Matrix.det (Matrix.of fun a b : Fin r => ∑ x ∈ range (N + 1),
    Wv x * (((x : ℚ) - ((N : ℚ) + 1)) ^ (a : ℕ) * ((x : ℚ) - ((N : ℚ) + 1)) ^ (b : ℕ)))) * hs

theorem LU_colsH (m S r : ℕ) (hr1 : 1 ≤ r) (hrS : r ≤ S - 1) (hl : S + 2 * m + r ≤ ℓ) :
    LU ℓ (momH (Icc 1 (S - 1)) (vcolS m S) (fun x => (x : ℚ)) r) := by
  obtain ⟨N, rfl⟩ : ∃ N, S = N + 2 := ⟨S - 2, by omega⟩
  have e : N + 2 - 1 = N + 1 := by omega
  rw [e, colsH_eq]
  refine LU.mul (LU.pow (LU_factorial (by omega)) r) ?_
  exact LU_hkH ℓ r (2 * m + 1) 0 N (by omega) (by omega)

/-- `κ_S` of the GI closed form (`n = K - m`). -/
noncomputable def kappaS (K m S : ℕ) : ℚ :=
  (∏ i ∈ Icc 1 m, (2 * (i : ℚ))) ^ (K - m) *
    (∏ i ∈ Ico 1 (K - m), momH (range K) (wnodeK K) (fun x => (x : ℚ)) i) *
    (∏ r ∈ Ico 1 (K - m), momH (Icc 1 (S - 1)) (vcolS m S) (fun x => (x : ℚ)) r) /
    (momH (range K) (wnodeK K) (fun x => (x : ℚ)) (K - m)) ^ (K - m - 1)

/-- **`κ_S` is an `ℓ`-unit** for `m < K`, `K - m ≤ S`, `S + K + 2m ≤ ℓ`. -/
theorem kappaS_LU (K m S : ℕ) (hmK : m < K) (hS : K - m ≤ S) (hl : S + K + 2 * m ≤ ℓ) :
    LU ℓ (kappaS K m S) := by
  unfold kappaS
  refine LU.div (LU.mul (LU.mul (LU.pow ?_ _) ?_) ?_) (LU.pow ?_ _)
  · refine LU.prod _ _ fun i hi => ?_
    have hi' := Finset.mem_Icc.1 hi
    have := LU_natCast_lt (l := ℓ) (n := 2 * i) (by omega) (by omega)
    simpa using this
  · refine LU.prod _ _ fun i hi => ?_
    have hi' := Finset.mem_Ico.1 hi
    exact LU_nodeH K i (by omega) (by omega) (by omega)
  · refine LU.prod _ _ fun r hr => ?_
    have hr' := Finset.mem_Ico.1 hr
    exact LU_colsH m S r hr'.1 (by omega) (by omega)
  · exact LU_nodeH K (K - m) (by omega) (by omega) (by omega)

end CatalanCore.Star.Leonard
