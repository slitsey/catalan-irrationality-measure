module

public import CatalanCore.Arith.Hybrid.DefBSchur

@[expose] public section

/-!
# Theorem C5: the `ℤ_(p)`-reductions of the entries under the D2 weights

Setting (`p ≡ 3 (mod 4)`, `4k = p + 1`, `p < r`, `L = p + k - r ∈ [m, 2m)`, `r + 2m ≤ 2p`).  The
singular indices below `N = r + 2m` are `k`, `p`, `p + k`; they have residues `-4`, `1`, `-4/5` for
`p Δ_t`, and `p² D_t` has residues `-16`, `1` at `k`, `p`.  The D2 weights `wC` are `0` on
`U = [r - p, k)`, `1` on the rest of `C` and on high zone nodes, and `2` on low zone nodes
(`z < p + k`).

`good_TCgen`: for `A < B < N`, `p^w Mn A B` is `p`-integral with reduction `TCgen w A B`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime]

/-- The hypotheses of the Theorem C5 setting (`j = 1`). -/
structure CSetup (o p r m k : ℕ) : Prop where
  p5 : 5 ≤ p
  hp6 : 6 ≤ p
  ho0 : 0 < o
  ho3 : o ≤ 3
  hk : 4 * k = p + o
  hrp : p < r
  hLlo : r + m ≤ p + k
  hLhi : p + k < r + 2 * m
  hN : r + 2 * m ≤ 2 * p

/-- The D2 weight of a label. -/
def wC (p r k : ℕ) (A : ℕ) : ℕ :=
  if A < r then (if r - p ≤ A ∧ A < k then 0 else 1) else (if A < p + k then 2 else 1)

/-- Residues of `p Δ_t` at the singular indices `k, p, p + k`. -/
def resS (p k t : ℕ) : ZMod p := if t = k then -4 else if t = p then 1 else -(4 * (5 : ZMod p)⁻¹)

/-- Sum of the residues over the singular indices in `(A, B]`. -/
def sing (p k A B : ℕ) : ZMod p :=
  (if A < k ∧ k ≤ B then -4 else 0) +
    ((if A < p ∧ p ≤ B then 1 else 0) + (if A < p + k ∧ p + k ≤ B then -(4 * (5 : ZMod p)⁻¹) else 0))

/-- Residues of `p² D_t` at `k` and `p`. -/
def resD (p k t : ℕ) : ZMod p := if t = k then -16 else 1

def singD (p k A : ℕ) : ZMod p := (if k ≤ A then -16 else 0) + (if p ≤ A then 1 else 0)

/-- Regular value of `Mn A B` mod `p` (`A < B`). -/
noncomputable def regE (p k A B : ℕ) : ZMod p := (16 * ((B : ZMod p) - A))⁻¹ *
  ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹)

noncomputable def regD (p : ℕ) [Fact p.Prime] (k A : ℕ) : ZMod p := -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 A,
  ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2)

/-- The residue of `p^w Mn A B`, `A < B`. -/
noncomputable def TCgen (p k w A B : ℕ) : ZMod p :=
  if w = 0 then regE p k A B
  else if w = 1 then (16 * ((B : ZMod p) - A))⁻¹ * sing p k A B
  else if w = 2 ∧ B - A = p then (16 : ZMod p)⁻¹ * sing p k A B else 0

/-- The residue of `p^w Mn A A`. -/
noncomputable def TCDgen (p : ℕ) [Fact p.Prime] (k w A : ℕ) : ZMod p :=
  if w = 0 then regD p k A else if w = 2 then -(1 / 16 : ZMod p) * singD p k A else 0

lemma sum_res_eq (A B : ℕ) {k : ℕ} (hk0 : 0 < k) (hkp : k < p) :
    ∑ t ∈ ({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B), resS p k t = sing p k A B := by
  have hp0 := (Fact.out : p.Prime).pos
  have h1 : k ∉ ({p, p + k} : Finset ℕ) := by simp; omega
  have h2 : p ∉ ({p + k} : Finset ℕ) := by simp; omega
  rw [Finset.sum_filter, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  simp only [Finset.mem_Ioc, resS, sing]
  have e1 : p ≠ k := by omega
  have e2 : p + k ≠ k := by omega
  have e3 : p + k ≠ p := by omega
  have e4 : p ≠ 0 := by omega
  have e5 : k ≠ 0 := by omega
  simp [e1, e2, e3, e4, e5]

lemma reg5 {o k : ℕ} (hk : 4 * k = p + o) (ho0 : 0 < o) (ho3 : o ≤ 3) (hp5 : 5 ≤ p) {t : ℕ} (h1 : 1 ≤ t) (ht2 : t < 2 * p)
    (hnk : t ≠ k) (hnp : t ≠ p) (hnkp : t ≠ p + k) : Reg p k t := by
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
    have : (t : ZMod p) = (k : ZMod p) := sub_eq_zero.1 h0
    rw [ZMod.natCast_eq_natCast_iff'] at this
    by_cases htp : t < p
    · rw [Nat.mod_eq_of_lt htp, Nat.mod_eq_of_lt hkp] at this; exact hnk this
    · have : t % p = t - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [Nat.mod_eq_of_lt hkp] at *
      omega

/-- `p Δ_{k'}` at a singular index `4k' = j p + 1`, `p ∤ k'`. -/
lemma good_Delta_gen {Fr : Frame} {o : ℕ} (hL : LamData Fr o) {j k : ℕ} (hk : 4 * k = j * p + o)
    (hj0 : 0 < j) (hjp : j < p) (hkz : ((k : ℕ) : ZMod p) ≠ 0) :
    Good p ((p : ℚ) * Fr.Delta k) (-(4 * ((j : ℕ) : ZMod p)⁻¹)) := by
  have hk0 : 0 < k := by have := hL.o_pos; omega
  rw [hL.delta_eq k hk0]
  have hjz : ((j : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; intro hd; exact absurd (Nat.le_of_dvd hj0 hd) (by omega)
  have hkQ : 4 * (k : ℚ) - (o : ℚ) = (j : ℚ) * p := by
    have : (4 * k : ℚ) = j * p + o := by exact_mod_cast hk
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

lemma CSetup.kp {o r m k : ℕ} (S : CSetup o p r m k) : k < p := by
  have := S.p5; have := S.hk; have := S.ho0; have := S.ho3; have := S.hp6; omega

lemma CSetup.hk4 {o p r m k : ℕ} [Fact p.Prime] (S : CSetup o p r m k) :
    (4 : ZMod p) * (k : ZMod p) = (o : ZMod p) := hk4_of (j := 1) (by rw [one_mul]; exact S.hk)

lemma CSetup.k0 {o r m k : ℕ} (S : CSetup o p r m k) : 0 < k := by have := S.hk; have := S.ho0; have := S.ho3; have := S.hp6; omega

section Gen

variable {Fr : Frame} {o : ℕ} (hL : LamData Fr o) {r m k : ℕ} (S : CSetup o p r m k)

include hL S

lemma good_res_Delta {t : ℕ} (ht : t ∈ ({k, p, p + k} : Finset ℕ)) :
    Good p ((p : ℚ) * Fr.Delta t) (resS p k t) := by
  have hp5 := S.p5
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hkp := S.kp
  have hk0 := S.k0
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hkz : ((k : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero_of_lt hk0 hkp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · have := good_Delta_gen hL (j := 1) (k := t) (by omega) (by omega) (by omega) hkz
    refine this.congr ?_
    simp [resS]
  · have e1 : t ≠ k := by omega
    refine (good_Delta_p hL hp5).congr ?_
    simp [resS, e1]
  · have e1 : p + k ≠ k := by omega
    have e2 : p + k ≠ p := by omega
    have hz : (((p + k : ℕ)) : ZMod p) ≠ 0 := by
      rw [Nat.cast_add, ZMod.natCast_self, zero_add]; exact hkz
    have := good_Delta_gen hL (j := 5) (k := p + k) (by omega) (by omega) (by omega) hz
    refine this.congr ?_
    have e4 : p ≠ 0 := by omega
    have e5 : k ≠ 0 := by omega
    simp [resS, e1, e2, e4, e5]

lemma good_res_Dsq {t : ℕ} (ht : t ∈ ({k, p} : Finset ℕ)) :
    Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (resD p k t) := by
  have hp5 := S.p5
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hkp := S.kp
  have hk0 := S.k0
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · have := good_Dsq_k hL (j := 1) (k := t) (by omega) (by omega) (by omega) hk0 hkp
    refine this.congr ?_
    simp [resD]
  · have e1 : t ≠ k := by omega
    refine (good_Dsq_p hL hp5).congr ?_
    simp [resD, e1]

omit hL in
lemma reg_C {t : ℕ} (h1 : 1 ≤ t) (hN : t < r + 2 * m) (hnk : t ≠ k) (hnp : t ≠ p)
    (hnkp : t ≠ p + k) : Reg p k t :=
  reg5 S.hk S.ho0 S.ho3 S.p5 h1 (by have := S.hN; omega) hnk hnp hnkp

/-- **The label-level table of Theorem C5, off-diagonal.** -/
theorem good_TCgen {w A B : ℕ} (hAB : A < B) (hBN : B < r + 2 * m)
    (h0 : w = 0 → B < k) (h1 : w = 1 → B - A ≠ p) :
    Good p ((p : ℚ) ^ w * Fr.Mn A B) (TCgen p k w A B) := by
  have hp5 := S.p5
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hkp := S.kp
  have hk0 := S.k0
  have hN := S.hN
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hreg : ∀ t ∈ Ioc A B \ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)),
      Reg p k t := by
    intro t ht
    obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
    have hI' := Finset.mem_Ioc.1 hI
    refine reg_C S (by omega) (by omega) ?_ ?_ ?_ <;> intro e <;> apply hn <;> subst e <;>
      simp [Finset.mem_filter, Finset.mem_Ioc, hI']
  have hsub : (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)) ⊆ Ioc A B :=
    fun t ht => (Finset.mem_filter.1 ht).2
  have h1' : ∀ t ∈ Ioc A B \ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)), 1 ≤ t :=
    fun t ht => by have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
  have hsing : ∀ t ∈ (({k, p, p + k} : Finset ℕ).filter (fun t => t ∈ Ioc A B)),
      Good p ((p : ℚ) * Fr.Delta t) (resS p k t) :=
    fun t ht => good_res_Delta hL S (Finset.mem_filter.1 ht).1
  have hsum := sum_res_eq (p := p) A B hk0 hkp
  by_cases hw0 : w = 0
  · subst hw0
    rw [pow_zero, one_mul]
    unfold TCgen; rw [if_pos rfl]
    have hBk := h0 rfl
    exact Mn_good0 hL hp5 S.hk4 hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
        exact reg_C S (by omega) (by omega) (by omega) (by omega) (by omega))
      (sub_ne_zero_of_lt hAB (by omega))
  by_cases hw1 : w = 1
  · subst hw1
    rw [pow_one]
    unfold TCgen; rw [if_neg (by omega), if_pos rfl]
    have hBA := h1 rfl
    have := Mn_goodP hL hp5 S.hk4 hAB _ hsub h1' (resS p k) hsing hreg
      (sub_ne_zero_of_ne hAB (by omega) hBA)
    rw [hsum] at this
    exact this
  -- w ≥ 2
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
  by_cases hBA : B - A = p
  · have := Mn_goodPP hL hp5 S.hk4 hAB hBA _ hsub h1' (resS p k) hsing hreg
    rw [hsum] at this
    by_cases hw2 : w' = 0
    · subst hw2
      unfold TCgen; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨rfl, hBA⟩]
      exact this
    · unfold TCgen
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have := (good_pow_mul_zero this (n := w') (by omega))
      exact this.congr' (by ring)
  · have := Mn_goodP hL hp5 S.hk4 hAB _ hsub h1' (resS p k) hsing hreg
      (sub_ne_zero_of_ne hAB (by omega) hBA)
    unfold TCgen
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have := (good_pow_mul_zero this (n := w' + 1) (by omega))
    exact this.congr' (by ring)

/-- **The diagonal entries of `C` under the D2 weights.** -/
theorem good_TCDgen {w A : ℕ} (hA : A < r) (hw : w = 0 ∨ w = 2) (h0 : w = 0 → A < k) :
    Good p ((p : ℚ) ^ w * Fr.Mn A A) (TCDgen p k w A) := by
  have hp5 := S.p5
  have hk := S.hk; have := S.ho0; have := S.ho3; have := S.hp6
  have hkp := S.kp
  have hk0 := S.k0
  have hN := S.hN
  have hLlo := S.hLlo
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  rcases hw with rfl | rfl
  · rw [pow_zero, one_mul]
    unfold TCDgen; rw [if_pos rfl]
    have hAk := h0 rfl
    exact Mn_diag_good0 hL hp5 S.hk4 (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
      exact reg_C S h1 (by omega) (by omega) (by omega) (by omega))
  · have e20 : ¬ ((2:ℕ) = 0) := by norm_num
    unfold TCDgen; rw [if_neg e20, if_pos rfl]
    have hsub : (({k, p} : Finset ℕ).filter (fun t => t ∈ Icc 1 A)) ⊆ Icc 1 A :=
      fun t ht => (Finset.mem_filter.1 ht).2
    have := Mn_diag_goodP2 hL hp5 S.hk4 (A := A) _ hsub (resD p k)
      (fun t ht => good_res_Dsq hL S (Finset.mem_filter.1 ht).1)
      (fun t ht => by
        obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
        have hI' := Finset.mem_Icc.1 hI
        refine reg_C S (by omega) (by omega) ?_ ?_ (by omega) <;> intro e <;> apply hn <;>
          subst e <;> simp [Finset.mem_filter, Finset.mem_Icc, hI'])
    refine this.congr ?_
    have hdist : k ∉ ({p} : Finset ℕ) := by simp; omega
    rw [Finset.sum_filter, Finset.sum_insert hdist, Finset.sum_singleton]
    simp only [Finset.mem_Icc, resD, singD]
    have e1 : p ≠ k := by omega
    simp [e1, show 1 ≤ k from hk0, show 1 ≤ p from hpp]

end Gen

end

end CatalanCore.Arith.Hybrid
