module

public import CatalanCore.Arith.Hybrid.DefGKQz3
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# GK, class 3: the `p²` reduction `Qm3 = (Qz3 c c')` is invertible mod `p`

`Qm3_inj`: `Qm3 *ᵥ v = 0 → v = 0` for `p` with `GKS3`.  `Qm3` is block diagonal by the class
`c mod p` with chains `(a, a+p, a+2p) ∩ [0, r)`; the three block types are
`(B0,B2,B4)`, `(B1,B3,B5)`, `(B1,B3)` with determinants `-2²3¹⁵5⁴·37·73`, `2²3¹⁰5²·350972849`,
`2⁴3¹⁰5³·139` (scaled by `129600`).
-/

open Finset CatalanCore Matrix

namespace CatalanCore.Arith.Hybrid

section Inj3

variable {o p : ℕ} [Fact p.Prime] {k : ℕ}

/-- The `r × r` integer-scaled reduction. -/
def Qm3 (p k r : ℕ) : Matrix (Fin r) (Fin r) (ZMod p) :=
  Matrix.of fun c c' => ((Qz3 p k (c : ℕ) (c' : ℕ) : ℤ) : ZMod p)

lemma rowsum3 {r : ℕ} (hr : r ≤ 3 * p) (a R : ℕ) (ha : a < p)
    (hR : R = a ∨ R = a + p ∨ R = a + 2 * p) (w : ℕ → ZMod p) (hw : ∀ n, r ≤ n → w n = 0) :
    ∑ n ∈ range r, ((Qz3 p k R n : ℤ) : ZMod p) * w n =
      ((Qz3 p k R a : ℤ) : ZMod p) * w a + ((Qz3 p k R (a + p) : ℤ) : ZMod p) * w (a + p) +
        ((Qz3 p k R (a + 2 * p) : ℤ) : ZMod p) * w (a + 2 * p) := by
  have hz : ∀ n, n < 3 * p → n ≠ a → n ≠ a + p → n ≠ a + 2 * p → Qz3 p k R n = 0 := by
    intro n hn h1 h2 h3
    apply Qz3_zero <;> omega
  set T : Finset ℕ := {a, a + p, a + 2 * p} with hT
  have hpos := (Fact.out : p.Prime).pos
  have e1 : ∑ n ∈ range r, ((Qz3 p k R n : ℤ) : ZMod p) * w n =
      ∑ n ∈ range r ∪ T, ((Qz3 p k R n : ℤ) : ZMod p) * w n := by
    refine Finset.sum_subset Finset.subset_union_left ?_
    intro n hn hnr
    have hn' : r ≤ n := by
      by_contra h; exact hnr (Finset.mem_range.2 (by omega))
    rw [hw n hn', mul_zero]
  have e2 : ∑ n ∈ range r ∪ T, ((Qz3 p k R n : ℤ) : ZMod p) * w n =
      ∑ n ∈ T, ((Qz3 p k R n : ℤ) : ZMod p) * w n := by
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

lemma solve3_sym (m00 m01 m02 m11 m12 m22 N : ℤ) (x0 x1 x2 : ZMod p)
    (hN : N = m00 * (m11 * m22 - m12 * m12) - m01 * (m01 * m22 - m12 * m02) +
      m02 * (m01 * m12 - m11 * m02))
    (hd : (N : ZMod p) ≠ 0)
    (e0 : (m00 : ZMod p) * x0 + m01 * x1 + m02 * x2 = 0)
    (e1 : (m01 : ZMod p) * x0 + m11 * x1 + m12 * x2 = 0)
    (e2 : (m02 : ZMod p) * x0 + m12 * x1 + m22 * x2 = 0) :
    x0 = 0 ∧ x1 = 0 ∧ x2 = 0 := by
  subst hN
  push_cast at hd
  refine ⟨?_, ?_, ?_⟩
  · have : ((m00 : ZMod p) * (m11 * m22 - m12 * m12) - m01 * (m01 * m22 - m12 * m02) +
        m02 * (m01 * m12 - m11 * m02)) * x0 = 0 := by
      linear_combination ((m11 : ZMod p) * m22 - m12 * m12) * e0 -
        ((m01 : ZMod p) * m22 - m02 * m12) * e1 + ((m01 : ZMod p) * m12 - m02 * m11) * e2
    exact (mul_eq_zero.1 this).resolve_left hd
  · have : ((m00 : ZMod p) * (m11 * m22 - m12 * m12) - m01 * (m01 * m22 - m12 * m02) +
        m02 * (m01 * m12 - m11 * m02)) * x1 = 0 := by
      linear_combination (-((m01 : ZMod p) * m22 - m12 * m02)) * e0 +
        ((m00 : ZMod p) * m22 - m02 * m02) * e1 - ((m00 : ZMod p) * m12 - m02 * m01) * e2
    exact (mul_eq_zero.1 this).resolve_left hd
  · have : ((m00 : ZMod p) * (m11 * m22 - m12 * m12) - m01 * (m01 * m22 - m12 * m02) +
        m02 * (m01 * m12 - m11 * m02)) * x2 = 0 := by
      linear_combination ((m01 : ZMod p) * m12 - m11 * m02) * e0 -
        ((m00 : ZMod p) * m12 - m01 * m02) * e1 + ((m00 : ZMod p) * m11 - m01 * m01) * e2
    exact (mul_eq_zero.1 this).resolve_left hd

lemma solve2_sym (m00 m01 m11 N : ℤ) (x0 x1 : ZMod p)
    (hN : N = m00 * m11 - m01 * m01) (hd : (N : ZMod p) ≠ 0)
    (e0 : (m00 : ZMod p) * x0 + m01 * x1 = 0) (e1 : (m01 : ZMod p) * x0 + m11 * x1 = 0) :
    x0 = 0 ∧ x1 = 0 := by
  subst hN
  push_cast at hd
  refine ⟨?_, ?_⟩
  · have : ((m00 : ZMod p) * m11 - m01 * m01) * x0 = 0 := by
      linear_combination (m11 : ZMod p) * e0 - (m01 : ZMod p) * e1
    exact (mul_eq_zero.1 this).resolve_left hd
  · have : ((m00 : ZMod p) * m11 - m01 * m01) * x1 = 0 := by
      linear_combination (m00 : ZMod p) * e1 - (m01 : ZMod p) * e0
    exact (mul_eq_zero.1 this).resolve_left hd

lemma chain_vals (a : ℕ) (hp0 : 0 < p) (L0 L1 L2 P0 P1 P2 : ℤ)
    (hL0 : Lz3 p k a = L0) (hL1 : Lz3 p k (a + p) = L1) (hL2 : Lz3 p k (a + 2 * p) = L2)
    (hP0 : Pz3 p k a = P0) (hP1 : Pz3 p k (a + p) = P1) (hP2 : Pz3 p k (a + 2 * p) = P2) :
    Qz3 p k a a = -P0 ∧ Qz3 p k (a + p) (a + p) = -P1 ∧ Qz3 p k (a + 2 * p) (a + 2 * p) = -P2 ∧
    Qz3 p k a (a + p) = 90 * (L1 - L0) ∧ Qz3 p k a (a + 2 * p) = 45 * (L2 - L0) ∧
    Qz3 p k (a + p) (a + 2 * p) = 90 * (L2 - L1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Qz3_diag, hP0]
  · rw [Qz3_diag, hP1]
  · rw [Qz3_diag, hP2]
  · rw [Qz3_p p k a hp0, hL1, hL0]
  · rw [Qz3_2p p k a hp0, hL2, hL0]
  · have := Qz3_p p k (a + p) hp0
    rw [show a + p + p = a + 2 * p by ring] at this
    rw [this, hL2, hL1]

lemma ndvd_mul (hp : p.Prime) {x q : ℕ} (hx : ¬ p ∣ x) (hq : q.Prime) (hqp : p ≠ q) :
    ¬ p ∣ x * q := fun h =>
  ((hp.dvd_mul).1 h).elim hx (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 h))

lemma ndvd_smooth (hp : p.Prime) (h13 : 13 ≤ p) (a b c : ℕ) : ¬ p ∣ 2 ^ a * 3 ^ b * 5 ^ c := by
  intro h
  rcases (hp.dvd_mul).1 h with h | h
  · rcases (hp.dvd_mul).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h); omega

lemma int_ne_zero_of_ndvd {N : ℕ} (hN : ¬ p ∣ N) : ((N : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro h
  exact hN (by exact_mod_cast h)

lemma nz_I (h13 : 13 ≤ p) (h37 : p ≠ 37) (h73 : p ≠ 73) :
    ((-96890994517500 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have : ((96890994517500 : ℕ) : ZMod p) ≠ 0 := by
    have := int_ne_zero_of_ndvd (p := p) (N := 2 ^ 2 * 3 ^ 15 * 5 ^ 4 * 37 * 73) ?_
    · norm_num at this ⊢; exact this
    · exact ndvd_mul hp (ndvd_mul hp (ndvd_smooth hp h13 2 15 4) (by norm_num) h37)
        (by norm_num) h73
  intro h
  apply this
  have : ((-96890994517500 : ℤ) : ZMod p) = -((96890994517500 : ℕ) : ZMod p) := by push_cast; ring
  rw [this] at h
  simpa using h

set_option maxRecDepth 200000 in
lemma prime_350972849 : Nat.Prime 350972849 := by norm_num

lemma nz_II (h13 : 13 ≤ p) (hbig : p ≠ 350972849) :
    ((2072459576060100 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have h1 := int_ne_zero_of_ndvd (p := p) (N := 2 ^ 2 * 3 ^ 10 * 5 ^ 2 * 350972849)
    (ndvd_mul hp (ndvd_smooth hp h13 2 10 2) prime_350972849 hbig)
  norm_num at h1 ⊢; exact h1

lemma nz_III (h13 : 13 ≤ p) (h139 : p ≠ 139) :
    ((16415622000 : ℤ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  have h1 := int_ne_zero_of_ndvd (p := p) (N := 2 ^ 4 * 3 ^ 10 * 5 ^ 3 * 139)
    (ndvd_mul hp (ndvd_smooth hp h13 4 10 3) (by norm_num) h139)
  norm_num at h1 ⊢; exact h1


variable {r m : ℕ}

theorem Qm3_inj (S : GKS3 o p r m k) (v : Fin r → ZMod p) (hv : Qm3 p k r *ᵥ v = 0) : v = 0 := by
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
  have hrow : ∀ R, R < r → ∑ n ∈ range r, ((Qz3 p k R n : ℤ) : ZMod p) * w n = 0 := by
    intro R hR
    have := congrFun hv ⟨R, hR⟩
    simp only [Matrix.mulVec, dotProduct, Qm3, Matrix.of_apply, Pi.zero_apply] at this
    rw [← this, ← Fin.sum_univ_eq_sum_range (fun n => ((Qz3 p k R n : ℤ) : ZMod p) * w n) r]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    simp [hwdef, c.2]
  have loc : ∀ a, a < p → ∀ R, (R = a ∨ R = a + p ∨ R = a + 2 * p) → R < r →
      ((Qz3 p k R a : ℤ) : ZMod p) * w a + ((Qz3 p k R (a + p) : ℤ) : ZMod p) * w (a + p) +
        ((Qz3 p k R (a + 2 * p) : ℤ) : ZMod p) * w (a + 2 * p) = 0 := by
    intro a ha R hR hRr
    rw [← rowsum3 hr3 a R ha hR w hw]
    exact hrow R hRr
  have key : ∀ a, a < p → w a = 0 ∧ w (a + p) = 0 ∧ w (a + 2 * p) = 0 := by
    intro a ha
    have eA := loc a ha a (Or.inl rfl) (by omega)
    have eB := loc a ha (a + p) (Or.inr (Or.inl rfl)) (by omega)
    by_cases h1 : a < k
    · have eC := loc a ha (a + 2 * p) (Or.inr (Or.inr rfl)) (by omega)
      obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain_vals (k := k) a hp0 0 (-270) (-297) 0
        (-121500) (-124659) (Lz_B0 h13 hk h1) (Lz_B2 h13 hk (by omega) (by omega))
        (Lz_B4 h13 hk (by omega) (by omega)) (Pz_B0 h13 hk h1)
        (Pz_B2 h13 hk (by omega) (by omega)) (Pz_B4 h13 hk (by omega) (by omega))
      rw [Qz3_symm p k (a + p) a] at eB
      rw [Qz3_symm p k (a + 2 * p) a, Qz3_symm p k (a + 2 * p) (a + p)] at eC
      rw [v00, v01, v02] at eA
      rw [v11, v01, v12] at eB
      rw [v22, v02, v12] at eC
      exact solve3_sym _ _ _ _ _ _ (-96890994517500) _ _ _ (by norm_num) (nz_I h13 S.h37 S.h73) eA eB eC
    · by_cases h2 : a + 2 * p < r
      · have eC := loc a ha (a + 2 * p) (Or.inr (Or.inr rfl)) h2
        obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain_vals (k := k) a hp0 (-360) (-342) (-337)
          (-129600) (-126684) (-126259) (Lz_B1 h13 hk (by omega) (by omega))
          (Lz_B3 h13 hk (by omega) (by omega)) (Lz_B5 h13 hk (by omega))
          (Pz_B1 h13 hk (by omega) (by omega)) (Pz_B3 h13 hk (by omega) (by omega))
          (Pz_B5 h13 hk (by omega))
        rw [Qz3_symm p k (a + p) a] at eB
        rw [Qz3_symm p k (a + 2 * p) a, Qz3_symm p k (a + 2 * p) (a + p)] at eC
        rw [v00, v01, v02] at eA
        rw [v11, v01, v12] at eB
        rw [v22, v02, v12] at eC
        exact solve3_sym _ _ _ _ _ _ 2072459576060100 _ _ _ (by norm_num) (nz_II h13 S.hbig) eA eB eC
      · have hz : w (a + 2 * p) = 0 := hw _ (by omega)
        obtain ⟨v00, v11, v22, v01, v02, v12⟩ := chain_vals (k := k) a hp0 (-360) (-342)
          (Lz3 p k (a + 2 * p)) (-129600) (-126684) (Pz3 p k (a + 2 * p))
          (Lz_B1 h13 hk (by omega) (by omega)) (Lz_B3 h13 hk (by omega) (by omega)) rfl
          (Pz_B1 h13 hk (by omega) (by omega)) (Pz_B3 h13 hk (by omega) (by omega)) rfl
        rw [Qz3_symm p k (a + p) a] at eB
        rw [v00, v01, hz, mul_zero, add_zero] at eA
        rw [v11, v01, hz, mul_zero, add_zero] at eB
        obtain ⟨x0, x1⟩ := solve2_sym (- -129600) (90 * (-342 - -360)) (- -126684) 16415622000 _ _
          (by norm_num) (nz_III h13 S.h139) eA eB
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

end Inj3

end CatalanCore.Arith.Hybrid
