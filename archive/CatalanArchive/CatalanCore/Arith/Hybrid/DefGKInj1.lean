module

public import CatalanArchive.CatalanCore.Arith.Hybrid.DefGKQz1
public import CatalanArchive.CatalanCore.Arith.Hybrid.DefGKInj3

@[expose] public section

/-!
# GK, class 1: the `p²` reduction `Qm1 = (Qz1 c c')` is invertible mod `p`

`Qm1_inj`: `Qm1 *ᵥ v = 0 → v = 0` for `p` with `GKS1`.  The chains `(a, a+p, a+2p) ∩ [0, r)` have the
three types `(B0,B2,B4)`, `(B0,B2)`, `(B1,B3)` with determinants (scaled by `56448`)
`-2⁵3²7⁴·8663`, `-2⁶3²7⁴`, `2⁶7³·1009`.
-/

open Finset CatalanCore Matrix

namespace CatalanCore.Arith.Hybrid.GK1

open CatalanCore.Arith.Hybrid

section Inj1

variable {o p : ℕ} [Fact p.Prime] {k : ℕ}

/-- The `r × r` integer-scaled reduction. -/
def Qm1 (p k r : ℕ) : Matrix (Fin r) (Fin r) (ZMod p) :=
  Matrix.of fun c c' => ((Qz1 p k (c : ℕ) (c' : ℕ) : ℤ) : ZMod p)

lemma rowsum1 {r : ℕ} (hr : r ≤ 3 * p) (a R : ℕ) (ha : a < p)
    (hR : R = a ∨ R = a + p ∨ R = a + 2 * p) (w : ℕ → ZMod p) (hw : ∀ n, r ≤ n → w n = 0) :
    ∑ n ∈ range r, ((Qz1 p k R n : ℤ) : ZMod p) * w n =
      ((Qz1 p k R a : ℤ) : ZMod p) * w a + ((Qz1 p k R (a + p) : ℤ) : ZMod p) * w (a + p) +
        ((Qz1 p k R (a + 2 * p) : ℤ) : ZMod p) * w (a + 2 * p) := by
  have hz : ∀ n, n < 3 * p → n ≠ a → n ≠ a + p → n ≠ a + 2 * p → Qz1 p k R n = 0 := by
    intro n hn h1 h2 h3
    apply Qz1_zero <;> omega
  set T : Finset ℕ := {a, a + p, a + 2 * p} with hT
  have hpos := (Fact.out : p.Prime).pos
  have e1 : ∑ n ∈ range r, ((Qz1 p k R n : ℤ) : ZMod p) * w n =
      ∑ n ∈ range r ∪ T, ((Qz1 p k R n : ℤ) : ZMod p) * w n := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro n hn hnr
    have hn' : r ≤ n := by
      by_contra h; exact hnr (Finset.mem_range.2 (by omega))
    rw [hw n hn', mul_zero]
  have e2 : ∑ n ∈ range r ∪ T, ((Qz1 p k R n : ℤ) : ZMod p) * w n =
      ∑ n ∈ T, ((Qz1 p k R n : ℤ) : ZMod p) * w n := by
    symm
    refine Finset.sum_subset Finset.subset_union_right ?_
    intro n hn hnT
    have hnr : n < r := by
      rcases Finset.mem_union.1 hn with h | h
      · exact Finset.mem_range.1 h
      · exact absurd h hnT
    have hnT' : n ≠ a ∧ n ≠ a + p ∧ n ≠ a + 2 * p := by
      simp only [hT, Finset.mem_insert, Finset.mem_singleton, not_or] at hnT; exact hnT
    rw [hz n (by omega) hnT'.1 hnT'.2.1 hnT'.2.2]; simp
  rw [e1, e2, hT, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp; omega),
    Finset.sum_singleton]
  ring

lemma chain1_vals (a : ℕ) (hp0 : 0 < p) (L0 L1 L2 P0 P1 P2 : ℤ)
    (hL0 : Lz1 p k a = L0) (hL1 : Lz1 p k (a + p) = L1) (hL2 : Lz1 p k (a + 2 * p) = L2)
    (hP0 : Pz1 p k a = P0) (hP1 : Pz1 p k (a + p) = P1) (hP2 : Pz1 p k (a + 2 * p) = P2) :
    Qz1 p k a a = -2 * P0 ∧ Qz1 p k (a + p) (a + p) = -2 * P1 ∧
    Qz1 p k (a + 2 * p) (a + 2 * p) = -2 * P2 ∧
    Qz1 p k a (a + p) = 42 * (L1 - L0) ∧ Qz1 p k a (a + 2 * p) = 21 * (L2 - L0) ∧
    Qz1 p k (a + p) (a + 2 * p) = 42 * (L2 - L1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Qz1_diag, hP0]
  · rw [Qz1_diag, hP1]
  · rw [Qz1_diag, hP2]
  · rw [Qz1_p p k a hp0, hL1, hL0]
  · rw [Qz1_2p p k a hp0, hL2, hL0]
  · have := Qz1_p p k (a + p) hp0
    rw [show a + p + p = a + 2 * p by ring] at this
    rw [this, hL2, hL1]

lemma ndvd_smooth7 (hp : p.Prime) (h13 : 13 ≤ p) (a b c : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b * 7 ^ c := by
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

lemma int_neg_ne {N : ℕ} (h : ¬ p ∣ N) : (((-(N : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
  have h1 := int_ne_zero_of_ndvd (p := p) h
  intro h0
  apply h1
  have h2 : (((-(N : ℤ)) : ℤ) : ZMod p) = -((N : ℤ) : ZMod p) := Int.cast_neg _
  rw [h2] at h0
  exact neg_eq_zero.1 h0

lemma nz1_I (h13 : 13 ≤ p) (h8663 : p ≠ 8663) :
    ((-5990360544 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have h1 := int_neg_ne (p := p) (N := 2 ^ 5 * 3 ^ 2 * 7 ^ 4 * 8663)
    (ndvd_mul hp (ndvd_smooth7 hp h13 5 2 4) (by norm_num) h8663)
  norm_num at h1 ⊢; exact h1

lemma nz1_II (h13 : 13 ≤ p) : ((-1382976 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have h1 := int_neg_ne (p := p) (N := 2 ^ 6 * 3 ^ 2 * 7 ^ 4) (ndvd_smooth7 hp h13 6 2 4)
  norm_num at h1 ⊢; exact h1

lemma nz1_III (h13 : 13 ≤ p) (h1009 : p ≠ 1009) : ((22149568 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have h1 := int_ne_zero_of_ndvd (p := p) (N := 2 ^ 6 * 3 ^ 0 * 7 ^ 3 * 1009)
    (ndvd_mul hp (ndvd_smooth7 hp h13 6 0 3) (by norm_num) h1009)
  norm_num at h1 ⊢; exact h1

variable {r m : ℕ}

theorem Qm1_inj (S : GKS1 o p r m k) (v : Fin r → ZMod p) (hv : Qm1 p k r *ᵥ v = 0) : v = 0 := by
  classical
  have h13 := S.p13
  have hk := S.hk
  have hkp := S.kp
  have hr := S.hr
  have hN := S.hN; have hkk := S.hk
  have hm := S.hm
  have hr3 : r ≤ 3 * p := by omega
  have hp0 : 0 < p := by omega
  set w : ℕ → ZMod p := fun n => if h : n < r then v ⟨n, h⟩ else 0 with hwdef
  have hw : ∀ n, r ≤ n → w n = 0 := fun n hn => by simp [hwdef, not_lt.2 hn]
  have hrow : ∀ R, R < r → ∑ n ∈ range r, ((Qz1 p k R n : ℤ) : ZMod p) * w n = 0 := by
    intro R hR
    have := congrFun hv ⟨R, hR⟩
    simp only [Matrix.mulVec, dotProduct, Qm1, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun n => ((Qz1 p k R n : ℤ) : ZMod p) * w n) r]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp [hwdef, c.2]
  have loc : ∀ a, a < p → ∀ R, (R = a ∨ R = a + p ∨ R = a + 2 * p) → R < r →
      ((Qz1 p k R a : ℤ) : ZMod p) * w a + ((Qz1 p k R (a + p) : ℤ) : ZMod p) * w (a + p) +
        ((Qz1 p k R (a + 2 * p) : ℤ) : ZMod p) * w (a + 2 * p) = 0 := by
    intro a ha R hR hRr
    rw [← rowsum1 hr3 a R ha hR w hw]
    exact hrow R hRr
  have key : ∀ a, a < p → w a = 0 ∧ w (a + p) = 0 ∧ w (a + 2 * p) = 0 := by
    intro a ha
    have eA := loc a ha a (Or.inl rfl) (by omega)
    have eB := loc a ha (a + p) (Or.inr (Or.inl rfl)) (by omega)
    by_cases h2 : a + 2 * p < r
    · -- type (B0, B2, B4)
      have eC := loc a ha (a + 2 * p) (Or.inr (Or.inr rfl)) h2
      obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain1_vals (k := k) a hp0 0 (-28) (-34) 0
        (-1372) (-1507) (Lz_B0 h13 hk (by omega)) (Lz_B2 h13 hk (by omega) (by omega))
        (Lz_B4 h13 hk (by omega)) (Pz_B0 h13 hk (by omega))
        (Pz_B2 h13 hk (by omega) (by omega)) (Pz_B4 h13 hk (by omega))
      rw [Qz1_symm p k (a + p) a] at eB
      rw [Qz1_symm p k (a + 2 * p) a, Qz1_symm p k (a + 2 * p) (a + p)] at eC
      rw [v00, v01, v02] at eA
      rw [v11, v01, v12] at eB
      rw [v22, v02, v12] at eC
      exact solve3_sym _ _ _ _ _ _ (-5990360544) _ _ _ (by norm_num) (nz1_I h13 S.h8663) eA eB eC
    · have hz : w (a + 2 * p) = 0 := hw _ (by omega)
      by_cases h1 : a < k
      · -- type (B0, B2)
        obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain1_vals (k := k) a hp0 0 (-28)
          (Lz1 p k (a + 2 * p)) 0 (-1372) (Pz1 p k (a + 2 * p))
          (Lz_B0 h13 hk (by omega)) (Lz_B2 h13 hk (by omega) (by omega)) rfl
          (Pz_B0 h13 hk (by omega)) (Pz_B2 h13 hk (by omega) (by omega)) rfl
        rw [Qz1_symm p k (a + p) a] at eB
        rw [v00, v01, hz] at eA
        rw [v11, v01, hz] at eB
        simp only [mul_zero, add_zero] at eA eB
        obtain ⟨x0, x1⟩ := solve2_sym _ _ _ (-1382976) _ _ (by norm_num) (nz1_II h13) eA eB
        exact ⟨x0, x1, hz⟩
      · -- type (B1, B3)
        obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain1_vals (k := k) a hp0 (-112) (-76)
          (Lz1 p k (a + 2 * p)) (-3136) (-1948) (Pz1 p k (a + 2 * p))
          (Lz_B1 h13 hk (by omega) (by omega)) (Lz_B3 h13 hk (by omega) (by omega)) rfl
          (Pz_B1 h13 hk (by omega) (by omega)) (Pz_B3 h13 hk (by omega) (by omega)) rfl
        rw [Qz1_symm p k (a + p) a] at eB
        rw [v00, v01, hz] at eA
        rw [v11, v01, hz] at eB
        simp only [mul_zero, add_zero] at eA eB
        obtain ⟨x0, x1⟩ := solve2_sym _ _ _ 22149568 _ _ (by norm_num) (nz1_III h13 S.h1009) eA eB
        exact ⟨x0, x1, hz⟩
  funext c
  have hc := c.2
  have hcw : w (c : ℕ) = 0 := by
    rcases (by omega : (c : ℕ) < p ∨ (p ≤ c ∧ (c : ℕ) < 2 * p) ∨ 2 * p ≤ (c : ℕ)) with h | h | h
    · exact (key c h).1
    · have := (key (c - p) (by omega)).2.1
      rwa [show (c : ℕ) - p + p = c by omega] at this
    · have := (key (c - 2 * p) (by omega)).2.2
      rwa [show (c : ℕ) - 2 * p + 2 * p = c by omega] at this
  simpa [hwdef, hc] using hcw

end Inj1

end CatalanCore.Arith.Hybrid.GK1
