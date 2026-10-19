module

public import CatalanCore.Arith.Hybrid.DefC5Inv

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4): the `ℤ_(p)`-reductions of the entries under the D2 weights

Setting (`p ≡ 3 (mod 4)`, `4k = p + 1`, `p < r`, `L = p + k - r ∈ [m, 2m)`, `r + 2m ≤ 2p`).  The
singular indices below `N = r + 2m` are `k`, `p`, `p + k`; they have residues `-4`, `1`, `-4/5` for
`p Δ_t`, and `p² D_t` has residues `-16`, `1` at `k`, `p`.  The D2 weights `wC7` are `0` on
`U = [r - p, k)`, `1` on the rest of `C` and on high zone nodes, and `2` on low zone nodes
(`z < p + k`).

`good_TCgen7`: for `A < B < N`, `p^w Mn A B` is `p`-integral with reduction `TCgen7 w A B`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime]

/-- The hypotheses of the Theorem C7 (j = 3, p ≡ 1 mod 4) setting (`j = 1`). -/
structure CSetup7 (p r m k : ℕ) : Prop where
  p5 : 5 ≤ p
  hk : 4 * k = 3 * p + 1
  hrp : p < r
  hLlo : r + m ≤ p + k
  hLhi : p + k < r + 2 * m
  hN : r + 2 * m ≤ 2 * p

/-- The D2 weight of a label. -/
def wC7 (p r k : ℕ) (A : ℕ) : ℕ :=
  if A < r then (if r - p ≤ A ∧ A < k then 0 else 1) else (if A < p + k then 2 else 1)

/-- Residues of `p Δ_t` at the singular indices `k, p, p + k`. -/
def resS7 (p k t : ℕ) : ZMod p := if t = k then -(4 * (3 : ZMod p)⁻¹) else if t = p then 1 else -(4 * (7 : ZMod p)⁻¹)

/-- Sum of the residues over the singular indices in `(A, B]`. -/
def sing7 (p k A B : ℕ) : ZMod p :=
  (if A < k ∧ k ≤ B then -(4 * (3 : ZMod p)⁻¹) else 0) +
    ((if A < p ∧ p ≤ B then 1 else 0) + (if A < p + k ∧ p + k ≤ B then -(4 * (7 : ZMod p)⁻¹) else 0))

/-- Residues of `p² D_t` at `k` and `p`. -/
def resD7 (p k t : ℕ) : ZMod p := if t = k then -(16 * ((3 : ZMod p)⁻¹) ^ 2) else 1

def singD7 (p k A : ℕ) : ZMod p := (if k ≤ A then -(16 * ((3 : ZMod p)⁻¹) ^ 2) else 0) + (if p ≤ A then 1 else 0)

/-- The residue of `p^w Mn A B`, `A < B`. -/
noncomputable def TCgen7 (p k w A B : ℕ) : ZMod p :=
  if w = 0 then regE p A B
  else if w = 1 then (16 * ((B : ZMod p) - A))⁻¹ * sing7 p k A B
  else if w = 2 ∧ B - A = p then (16 : ZMod p)⁻¹ * sing7 p k A B else 0

/-- The residue of `p^w Mn A A`. -/
noncomputable def TCDgen7 (p : ℕ) [Fact p.Prime] (k w A : ℕ) : ZMod p :=
  if w = 0 then regD p A else if w = 2 then -(1 / 16 : ZMod p) * singD7 p k A else 0

lemma sum_res_eq7 (A B : ℕ) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ∑ t ∈ ({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B), resS7 p k t = sing7 p k A B := by
  have hp0 := (Fact.out : p.Prime).pos
  have h1 : k ∉ ({p, p + k} : Finset ℕ) := by simp; omega
  have h2 : p ∉ ({p + k} : Finset ℕ) := by simp; omega
  rw [Finset.sum_filter, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  simp only [Finset.mem_Ioc, resS7, sing7]
  have e1 : p ≠ k := by omega
  have e2 : p + k ≠ k := by omega
  have e3 : p + k ≠ p := by omega
  have e4 : p ≠ 0 := by omega
  have e5 : k ≠ 0 := by omega
  simp [e1, e2, e3, e4, e5]

lemma reg57 {k : ℕ} (hk : 4 * k = 3 * p + 1) (hp5 : 5 ≤ p) {t : ℕ} (h1 : 1 ≤ t) (ht2 : t < 2 * p)
    (hnk : t ≠ k) (hnp : t ≠ p) (hnkp : t ≠ p + k) : Reg p t := by
  have hp0 := (Fact.out : p.Prime).pos
  have hkp : k < p := by omega
  refine ⟨?_, ?_⟩
  · rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
      omega
  · intro h0
    have h4k : (4 : ZMod p) * (k : ZMod p) = 1 := by
      have : ((4 * k : ℕ) : ZMod p) = ((3 * p + 1 : ℕ) : ZMod p) := by rw [hk]
      push_cast at this
      simpa [ZMod.natCast_self] using this
    have h4 : (4 : ZMod p) ≠ 0 := four_ne_zmod p hp5
    have : (t : ZMod p) = (k : ZMod p) := by
      have : (4 : ZMod p) * ((t : ZMod p) - k) = 0 := by linear_combination h0 - h4k
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h h4
      · exact sub_eq_zero.1 h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hkp] at this; exact hnk this
    · have : t % p = t - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt hkp] at *
      omega

/-- `p Δ_{k'}` at a singular index `4k' = j p + 1`, `p ∤ j`, `p ∤ k'`. -/
lemma good_Delta_gen7 {Fr : Frame} (hL : LamData Fr) {j k : ℕ} (hk : 4 * k = j * p + 1)
    (hj0 : 0 < j) (hjz : ((j : ℕ) : ZMod p) ≠ 0) (hkz : ((k : ℕ) : ZMod p) ≠ 0) :
    Good p ((p : ℚ) * Fr.Delta k) (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  have hk0 : 0 < k := by omega
  rw [hL.delta_eq k hk0]
  have hkQ : 4 * (k : ℚ) - 1 = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + 1 := by exact_mod_cast hk
    linarith
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hjQ : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have hk0Q : (k : ℚ) ≠ 0 := by exact_mod_cast hk0.ne'
  have g1 : Good p ((p : ℚ) * (1 / (k : ℚ))) 0 :=
    ((Good.one (ℓ := p)).div (Good.natCast (ℓ := p) k) hkz).ell_mul
  have g2 : Good p (4 / (j : ℚ)) (4 * ((j : ℕ) : ZMod p)⁻¹) :=
    ((Good.ofNat (ℓ := p) 4).div (Good.natCast (ℓ := p) j) hjz).congr (by simp [div_eq_mul_inv])
  have := g1.sub g2
  refine this.congr' ?_ |>.congr (by ring)
  rw [hkQ]
  field_simp

lemma CSetup7.kp {r m k : ℕ} (S : CSetup7 p r m k) : k < p := by
  have := S.p5; have := S.hk; omega

lemma CSetup7.k0 {r m k : ℕ} (S : CSetup7 p r m k) : 0 < k := by have := S.hk; omega

section Gen7

variable {Fr : Frame} (hL : LamData Fr) {r m k : ℕ} (S : CSetup7 p r m k)

include hL S

lemma good_res_Delta7 {t : ℕ} (ht : t ∈ ({k, p, p + k} : Finset ℕ)) :
    Good p ((p : ℚ) * Fr.Delta t) (resS7 p k t) := by
  have hp5 := S.p5
  have hk := S.hk
  have hkp := S.kp
  have hk0 := S.k0
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hk0 hkp
  have hj3 : (((3 : ℕ)) : ZMod p) ≠ 0 := by simpa using three_ne hp5
  have hj7 : (((7 : ℕ)) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    rintro ⟨c, hc⟩
    rcases c with _ | _ | c
    · omega
    · omega
    · have : p * (c + 1 + 1) ≥ p * 2 := Nat.mul_le_mul_left p (by omega)
      omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · have := good_Delta_gen7 hL (j := 3) (k := t) (by omega) (by omega) hj3 hkz
    refine this.congr ?_
    simp [resS7]
  · have e1 : t ≠ k := by omega
    refine (good_Delta_p hL hp5).congr ?_
    simp [resS7, e1]
  · have e1 : p + k ≠ k := by omega
    have e2 : p + k ≠ p := by omega
    have hz : (((p + k : ℕ)) : ZMod p) ≠ 0 := by
      rw [Nat.cast_add, ZMod.natCast_self, zero_add]; exact hkz
    have := good_Delta_gen7 hL (j := 7) (k := p + k) (by omega) (by omega) hj7 hz
    refine this.congr ?_
    have e4 : p ≠ 0 := by omega
    have e5 : k ≠ 0 := by omega
    simp [resS7, e1, e2, e4, e5]

lemma good_res_Dsq7 {t : ℕ} (ht : t ∈ ({k, p} : Finset ℕ)) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (resD7 p k t) := by
  have hp5 := S.p5
  have hk := S.hk
  have hkp := S.kp
  have hk0 := S.k0
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · have := good_Dsq_k hL (j := 3) (k := t) (by omega) (by omega) (by omega) hk0 hkp
    refine this.congr ?_
    simp [resD7]
  · have e1 : t ≠ k := by omega
    refine (good_Dsq_p hL hp5).congr ?_
    simp [resD7, e1]

omit hL in
lemma reg_C7 {t : ℕ} (h1 : 1 ≤ t) (hN : t < r + 2 * m) (hnk : t ≠ k) (hnp : t ≠ p)
    (hnkp : t ≠ p + k) : Reg p t :=
  reg57 S.hk S.p5 h1 (by have := S.hN; omega) hnk hnp hnkp

/-- **The label-level table of Theorem C7 (j = 3, p ≡ 1 mod 4), off-diagonal.** -/
theorem good_TCgen7 {w A B : ℕ} (hAB : A < B) (hBN : B < r + 2 * m)
    (h0 : w = 0 → B < k) (h1 : w = 1 → B - A ≠ p) :
    Good p ((p : ℚ) ^ w * Fr.Mn A B) (TCgen7 p k w A B) := by
  have hp5 := S.p5
  have hk := S.hk
  have hkp := S.kp
  have hk0 := S.k0
  have hN := S.hN
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hreg : ∀ t ∈ Ioc A B \ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)),
      Reg p t := by
    intro t ht
    obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
    have hI' := Finset.mem_Ioc.1 hI
    refine reg_C7 S (by omega) (by omega) ?_ ?_ ?_ <;> intro e <;> apply hn <;> subst e <;>
      simp [Finset.mem_filter, Finset.mem_Ioc, hI']
  have hsub : (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)) ⊆ Ioc A B :=
    fun t ht => (Finset.mem_filter.1 ht).2
  have h1' : ∀ t ∈ Ioc A B \ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)), 1 ≤ t :=
    fun t ht => by have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
  have hsing : ∀ t ∈ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)),
      Good p ((p : ℚ) * Fr.Delta t) (resS7 p k t) :=
    fun t ht => good_res_Delta7 hL S (Finset.mem_filter.1 ht).1
  have hsum := sum_res_eq7 (p := p) A B hk0 hkp
  by_cases hw0 : w = 0
  · subst hw0
    rw [pow_zero, one_mul]
    unfold TCgen7; rw [if_pos rfl]
    have hBk := h0 rfl
    exact Mn_good0 hL hp5 hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
        exact reg_C7 S (by omega) (by omega) (by omega) (by omega) (by omega))
      (sub_ne_zero_of_lt hAB (by omega))
  by_cases hw1 : w = 1
  · subst hw1
    rw [pow_one]
    unfold TCgen7; rw [if_neg (by omega), if_pos rfl]
    have hBA := h1 rfl
    have := Mn_goodP hL hp5 hAB _ hsub h1' (resS7 p k) hsing hreg
      (sub_ne_zero_of_ne hAB (by omega) hBA)
    rw [hsum] at this
    exact this
  -- w ≥ 2
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
  by_cases hBA : B - A = p
  · have := Mn_goodPP hL hp5 hAB hBA _ hsub h1' (resS7 p k) hsing hreg
    rw [hsum] at this
    by_cases hw2 : w' = 0
    · subst hw2
      unfold TCgen7; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hBA⟩]
      exact this
    · unfold TCgen7
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have := (good_pow_mul_zero this (n := w') (by omega))
      exact this.congr' (by ring)
  · have := Mn_goodP hL hp5 hAB _ hsub h1' (resS7 p k) hsing hreg
      (sub_ne_zero_of_ne hAB (by omega) hBA)
    unfold TCgen7
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := (good_pow_mul_zero this (n := w' + 1) (by omega))
    exact this.congr' (by ring)

/-- **The diagonal entries of `C` under the D2 weights.** -/
theorem good_TCDgen7 {w A : ℕ} (hA : A < r) (hw : w = 0 ∨ w = 2) (h0 : w = 0 → A < k) :
    Good p ((p : ℚ) ^ w * Fr.Mn A A) (TCDgen7 p k w A) := by
  have hp5 := S.p5
  have hk := S.hk
  have hkp := S.kp
  have hk0 := S.k0
  have hN := S.hN
  have hLlo := S.hLlo
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  rcases hw with rfl | rfl
  · rw [pow_zero, one_mul]
    unfold TCDgen7; rw [if_pos rfl]
    have hAk := h0 rfl
    exact Mn_diag_good0 hL hp5 (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
      exact reg_C7 S h1 (by omega) (by omega) (by omega) (by omega))
  · have e20 : ¬ ((2:ℕ) = 0) := by norm_num
    unfold TCDgen7; rw [if_neg e20, if_pos rfl]
    have hsub : (({k, p} : Finset ℕ).filter (fun t => t ∈ Icc 1 A)) ⊆ Icc 1 A :=
      fun t ht => (Finset.mem_filter.1 ht).2
    have := Mn_diag_goodP2 hL hp5 (A := A) _ hsub (resD7 p k)
      (fun t ht => good_res_Dsq7 hL S (Finset.mem_filter.1 ht).1)
      (fun t ht => by
        obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
        have hI' := Finset.mem_Icc.1 hI
        refine reg_C7 S (by omega) (by omega) ?_ ?_ (by omega) <;> intro e <;> apply hn <;>
          subst e <;> simp [Finset.mem_filter, Finset.mem_Icc, hI'])
    refine this.congr ?_
    have hdist : k ∉ ({p} : Finset ℕ) := by simp; omega
    rw [Finset.sum_filter, Finset.sum_insert hdist, Finset.sum_singleton]
    simp only [Finset.mem_Icc, resD7, singD7]
    have e1 : p ≠ k := by omega
    simp [e1, show 1 ≤ k from hk0, show 1 ≤ p from hpp]

end Gen7

end

end CatalanCore.Arith.Hybrid
