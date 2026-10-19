module

public import CatalanCore.Arith.Hybrid.LamEntries

@[expose] public section

/-!
# Lemma E, class `p ≡ 1 (4)`: the label-level residue table (rank route)

Setting `p < r`, `4k = jp + 1` (class 1: `j = 3`, `k = (3p+1)/4`), labels `A < r + 2m ≤ k + p`.
The two singular indices below `k + p` are `k` and `p`.  The D-potentials (DQ §3) are
`wE A = 0` on the unpaired low block `U = [r-p, k)`, `1` on the rest of `C`, and `2` on the zone.
The scaled entry `p^{wE A + wE B} Mn A B` is `p`-integral with reduction `TEo`/`TEd`:
* weight `0` (both in `U`, regular): the regular sum;
* weight `1` and `B - A ≠ p`: `(16 (B-A))⁻¹ · (sum of the singular residues in (A,B])`;
* weight `2` and `B - A = p`: `16⁻¹ · (sum of the singular residues)`; all else `0`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {Fr : Frame}

lemma good_Dsq_p (hL : LamData Fr) (hp5 : 5 ≤ p) : Good p ((p : ℚ) ^ 2 * Fr.Dsq p) 1 := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [hL.dsq_eq p hp1]
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h4 : (4 * (p : ℚ) - 1) ≠ 0 := by
    have : (5 : ℚ) ≤ p := by exact_mod_cast hp5
    linarith
  have hl0 : ((p : ℕ) : ZMod p) = 0 := ZMod.natCast_self p
  have hz : (4 * ((p : ℕ) : ZMod p) - 1) ≠ 0 := by rw [hl0]; simp
  have g2 : Good p ((p : ℚ) ^ 2 * (16 / (4 * (p : ℚ) - 1) ^ 2)) 0 := by
    have := ((Good.ofNat (ℓ := p) 16).div
      ((((Good.ofNat (ℓ := p) 4).mul (Good.natCast (ℓ := p) p)).sub Good.one).pow' 2)
      (pow_ne_zero 2 hz)).ell_mul.ell_mul
    refine this.congr' ?_
    ring
  have := (Good.one (ℓ := p)).sub g2
  refine this.congr' ?_ |>.congr (by simp)
  field_simp

/-- The setting of Lemma E, class 1 (`j = 3`). -/
structure ESetup (p r m j k : ℕ) : Prop where
  p5 : 5 ≤ p
  hk : 4 * k = j * p + 1
  hj0 : 0 < j
  hjp : j < p
  hk0 : 0 < k
  hkp : k < p
  hpr : p < r
  hrk : r - p ≤ k
  hN : r + 2 * m ≤ k + p

/-- The potentials. -/
def wE (p r k A : ℕ) : ℕ := if A < r then (if r - p ≤ A ∧ A < k then 0 else 1) else 2

/-- Sum of the singular residues of `Δ` over `(A, B]`. -/
def singE (p j k A B : ℕ) : ZMod p :=
  (if A < k ∧ k ≤ B then -(4 * ((j : ℕ) : ZMod p)⁻¹) else 0) + (if A < p ∧ p ≤ B then 1 else 0)

/-- Sum of the singular residues of `p² D` over `[1, A]`. -/
def singE2 (p j k A : ℕ) : ZMod p :=
  (if k ≤ A then -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) else 0) + (if p ≤ A then 1 else 0)

/-- The residue of `p^w Mn A B` for `A < B`. -/
noncomputable def TEo (p j k w A B : ℕ) [Fact p.Prime] : ZMod p :=
  if w = 0 then (16 * ((B : ZMod p) - A))⁻¹ *
      ∑ t ∈ Ioc A B, (((t : ℕ) : ZMod p)⁻¹ - 4 * (4 * ((t : ℕ) : ZMod p) - 1)⁻¹)
  else if B - A = p then (if w = 2 then (16 : ZMod p)⁻¹ * singE p j k A B else 0)
  else if w = 1 then (16 * ((B : ZMod p) - A))⁻¹ * singE p j k A B else 0

/-- The residue of `p^w Mn A A`. -/
noncomputable def TEd (p j k w A : ℕ) [Fact p.Prime] : ZMod p :=
  if w = 0 then -(1 / 16 : ZMod p) * ∑ t ∈ Icc 1 A,
      ((((t : ℕ) : ZMod p)⁻¹) ^ 2 - 16 * ((4 * ((t : ℕ) : ZMod p) - 1)⁻¹) ^ 2)
  else if w = 2 then -(1 / 16 : ZMod p) * singE2 p j k A else 0

/-- The symmetric residue table on labels. -/
noncomputable def TE (p j r k A B : ℕ) [Fact p.Prime] : ZMod p :=
  if A < B then TEo p j k (wE p r k A + wE p r k B) A B
  else if B < A then TEo p j k (wE p r k A + wE p r k B) B A
  else TEd p j k (wE p r k A + wE p r k A) A

variable {r m j k : ℕ}

lemma ESetup.reg (S : ESetup p r m j k) {t : ℕ} (h1 : 1 ≤ t) (hN : t < r + 2 * m)
    (hnk : t ≠ k) (hnp : t ≠ p) : Reg p t :=
  reg_of S.hk S.p5 S.hkp h1 (by have := S.hN; have := S.hkp; omega)
    (by have := S.hN; omega) hnk hnp

lemma ESetup.pair_w (S : ESetup p r m j k) {A B : ℕ} (hAB : B - A = p) (hlt : A < B)
    (hB : B < r + 2 * m) : 2 ≤ wE p r k A + wE p r k B := by
  have := S.hN; have := S.hpr; have := S.hkp; have := S.hrk
  unfold wE
  split_ifs <;> omega

lemma ESetup.zero_w (S : ESetup p r m j k) {A B : ℕ} (hw : wE p r k A + wE p r k B = 0) :
    r - p ≤ A ∧ A < k ∧ r - p ≤ B ∧ B < k := by
  unfold wE at hw
  split_ifs at hw <;> omega

lemma sumE_S0 (hkp : k < p) (j A B : ℕ) :
    ∑ t ∈ ({k, p} : Finset ℕ).filter (fun t => A < t ∧ t ≤ B),
      (if t = k then -(4 * ((j : ℕ) : ZMod p)⁻¹) else (1 : ZMod p)) = singE p j k A B := by
  have hkne : k ≠ p := by omega
  rw [Finset.sum_filter, Finset.sum_pair hkne]
  unfold singE
  simp [hkne.symm]

lemma sumE_S0' (hkp : k < p) (j A : ℕ) :
    ∑ t ∈ ({k, p} : Finset ℕ).filter (fun t => t ≤ A),
      (if t = k then -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) else (1 : ZMod p)) = singE2 p j k A := by
  have hkne : k ≠ p := by omega
  rw [Finset.sum_filter, Finset.sum_pair hkne]
  unfold singE2
  simp [hkne.symm]

section Table

variable (hL : LamData Fr) (S : ESetup p r m j k)

include hL S

/-- **The off-diagonal table.** -/
theorem good_TEo {A B : ℕ} (hAB : A < B) (hB : B < r + 2 * m) :
    Good p ((p : ℚ) ^ (wE p r k A + wE p r k B) * Fr.Mn A B)
      (TEo p j k (wE p r k A + wE p r k B) A B) := by
  have hp5 := S.p5
  have hkp := S.hkp
  have hN := S.hN
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hkne : k ≠ p := by omega
  generalize hw : wE p r k A + wE p r k B = w
  by_cases hw0 : w = 0
  · subst hw0
    obtain ⟨_, _, _, hBk⟩ := S.zero_w hw
    rw [pow_zero, one_mul]
    unfold TEo; rw [if_pos rfl]
    exact Mn_good0 hL hp5 hAB (fun t ht => by have := Finset.mem_Ioc.1 ht; omega)
      (fun t ht => by
        obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 ht
        exact S.reg (by omega) (by omega) (by omega) (by omega))
      (sub_ne_zero_of_lt hAB (by omega))
  · -- weight ≥ 1: singular indices
    set S0 : Finset ℕ := ({k, p} : Finset ℕ).filter (fun t => A < t ∧ t ≤ B) with hS0
    have hmem : ∀ t, t ∈ S0 ↔ (t = k ∨ t = p) ∧ A < t ∧ t ≤ B := by
      intro t; simp [hS0]
    have hsub : S0 ⊆ Ioc A B := fun t ht => by
      have := (hmem t).1 ht
      exact Finset.mem_Ioc.2 ⟨this.2.1, this.2.2⟩
    have h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t := fun t ht => by
      have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
    have hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t)
        ((fun t => if t = k then -(4 * ((j : ℕ) : ZMod p)⁻¹) else (1 : ZMod p)) t) := by
      intro t ht
      rcases (hmem t).1 ht with ⟨e | e, _⟩
      · subst e; simp only [if_true]
        exact good_Delta_k hL S.hk S.hj0 S.hjp S.hk0 S.hkp
      · subst e; simp only [if_neg hkne.symm]
        exact good_Delta_p hL hp5
    have hr : ∀ t ∈ Ioc A B \ S0, Reg p t := fun t ht => by
      obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
      have hI' := Finset.mem_Ioc.1 hI
      have h2k : t ≠ k := fun e => hn ((hmem t).2 ⟨Or.inl e, hI'⟩)
      have h2p : t ≠ p := fun e => hn ((hmem t).2 ⟨Or.inr e, hI'⟩)
      exact S.reg (by omega) (by omega) h2k h2p
    have hsum := sumE_S0 (p := p) hkp j A B
    by_cases hBA : B - A = p
    · have hw2 := S.pair_w hBA hAB hB
      rw [hw] at hw2
      have key := Mn_goodPP hL hp5 hAB hBA S0 hsub h1 _ hsing hr
      rw [hsum] at key
      unfold TEo
      rw [if_neg hw0, if_pos hBA]
      by_cases h2 : w = 2
      · subst h2; rw [if_pos rfl]; exact key
      · rw [if_neg h2]
        obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
        have := good_pow_mul_zero key (n := w') (by omega)
        refine this.congr' ?_
        ring
    · have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB (by omega) hBA
      have key := Mn_goodP hL hp5 hAB S0 hsub h1 _ hsing hr hd
      rw [hsum] at key
      unfold TEo
      rw [if_neg hw0, if_neg hBA]
      by_cases h1' : w = 1
      · subst h1'; rw [if_pos rfl, pow_one]; exact key
      · rw [if_neg h1']
        obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
        have := good_pow_mul_zero key (n := w') (by omega)
        refine this.congr' ?_ |>.congr (by simp)
        ring

/-- **The diagonal table** (`A < r`). -/
theorem good_TEd {A : ℕ} (hA : A < r) :
    Good p ((p : ℚ) ^ (wE p r k A + wE p r k A) * Fr.Mn A A)
      (TEd p j k (wE p r k A + wE p r k A) A) := by
  have hp5 := S.p5
  have hkp := S.hkp
  have hN := S.hN
  have hpp : 0 < p := (Fact.out : p.Prime).pos
  have hkne : k ≠ p := by omega
  by_cases hU : r - p ≤ A ∧ A < k
  · have hw : wE p r k A + wE p r k A = 0 := by unfold wE; split_ifs <;> omega
    rw [hw, pow_zero, one_mul]
    unfold TEd; rw [if_pos rfl]
    exact Mn_diag_good0 hL hp5 (fun t ht => by
      obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht
      exact S.reg h1 (by omega) (by omega) (by omega))
  · have hw : wE p r k A + wE p r k A = 2 := by unfold wE; split_ifs <;> omega
    rw [hw]
    unfold TEd; rw [if_neg (by omega), if_pos rfl]
    set S0 : Finset ℕ := ({k, p} : Finset ℕ).filter (fun t => t ≤ A) with hS0
    have hmem : ∀ t, t ∈ S0 ↔ (t = k ∨ t = p) ∧ t ≤ A := by
      intro t; simp [hS0]
    have hsub : S0 ⊆ Icc 1 A := fun t ht => by
      have := (hmem t).1 ht
      have hk0 := S.hk0
      rcases this with ⟨e | e, h⟩
      · subst e; exact Finset.mem_Icc.2 ⟨hk0, h⟩
      · subst e; exact Finset.mem_Icc.2 ⟨hpp, h⟩
    have hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t)
        ((fun t => if t = k then -(16 * (((j : ℕ) : ZMod p)⁻¹) ^ 2) else (1 : ZMod p)) t) := by
      intro t ht
      rcases (hmem t).1 ht with ⟨e | e, _⟩
      · subst e; simp only [if_true]
        exact good_Dsq_k hL S.hk S.hj0 S.hjp S.hk0 S.hkp
      · subst e; simp only [if_neg hkne.symm]
        exact good_Dsq_p hL hp5
    have hr : ∀ t ∈ Icc 1 A \ S0, Reg p t := fun t ht => by
      obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
      have hI' := Finset.mem_Icc.1 hI
      have h2k : t ≠ k := fun e => hn ((hmem t).2 ⟨Or.inl e, hI'.2⟩)
      have h2p : t ≠ p := fun e => hn ((hmem t).2 ⟨Or.inr e, hI'.2⟩)
      exact S.reg hI'.1 (by omega) h2k h2p
    have key := Mn_diag_goodP2 hL hp5 (A := A) S0 hsub _ hsing hr
    rw [sumE_S0' hkp j A] at key
    exact key

end Table

end

end CatalanCore.Arith.Hybrid
