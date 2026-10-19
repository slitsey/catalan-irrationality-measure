module

public import CatalanCore.Arith.Hybrid.DefC5Inv
public import CatalanCore.Arith.Hybrid.DefGKCore

@[expose] public section

/-!
# GK: generic residue tables for `p² Mn` and `p Mn` with a finite singular set

For a finite set `Sg` of singular indices with residues `res` of `p Δ_t` and `resD` of `p² D_t`,
and all other indices `1 ≤ t < Nb` regular, with `Lv n = ∑_{t ∈ Sg, t ≤ n} res t`:

* `tab_P1` : `p Mn A B ↦ (16 (B - A))⁻¹ (Lv B - Lv A)` for `p ∤ B - A`;
* `tab_PP` : `p² Mn A B ↦ (Lv B - Lv A) / 16` for `B - A = p`;
* `tab_P2P`: `p² Mn A B ↦ (Lv B - Lv A) / 32` for `B - A = 2p`;
* `tab_D`   : `p² Mn A A ↦ -(Lv A)/16` (with `resD`).
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Gen

variable {o p : ℕ} [Fact p.Prime]

/-- Cumulative residue of the singular indices `≤ n`. -/
def Lv (Sg : Finset ℕ) (res : ℕ → ZMod p) (n : ℕ) : ZMod p :=
  ∑ t ∈ Sg, if t ≤ n then res t else 0

lemma sum_Ioc_Lv (Sg : Finset ℕ) (res : ℕ → ZMod p) {A B : ℕ} (h : A ≤ B) :
    ∑ t ∈ Sg.filter (fun t => t ∈ Ioc A B), res t = Lv Sg res B - Lv Sg res A := by
  rw [Finset.sum_filter]
  unfold Lv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Finset.mem_Ioc]
  split_ifs <;> first | omega | simp

lemma sum_Icc_Lv (Sg : Finset ℕ) (res : ℕ → ZMod p) (hSg : ∀ t ∈ Sg, 1 ≤ t) {A : ℕ} :
    ∑ t ∈ Sg.filter (fun t => t ∈ Icc 1 A), res t = Lv Sg res A := by
  rw [Finset.sum_filter]
  unfold Lv
  apply Finset.sum_congr rfl
  intro t ht
  have := hSg t ht
  simp only [Finset.mem_Icc]
  split_ifs <;> first | rfl | omega

/-- `p² Mn A B` with `B - A = 2p`. -/
lemma Mn_good2PP {Fr : Frame} {o : ℕ} (hL : LamData Fr o) (hp5 : 5 ≤ p) {k : ℕ}
    (hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)) {A B : ℕ} (h : A < B)
    (hBA : B - A = 2 * p) (S0 : Finset ℕ) (hS0 : S0 ⊆ Ioc A B)
    (h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t) (res : ℕ → ZMod p)
    (hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (res t))
    (hr : ∀ t ∈ Ioc A B \ S0, Reg p k t) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((32 : ZMod p)⁻¹ * ∑ t ∈ S0, res t) := by
  rw [Mn_lt hL h]
  have h32 : (32 : ZMod p) ≠ 0 := by
    have : ((32 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have h2 : p ∣ 2 ^ 5 := by norm_num; exact hd
      have := Nat.le_of_dvd (by norm_num) ((Fact.out : p.Prime).dvd_of_dvd_pow h2)
      omega
    simpa using this
  have hBQ : (B : ℚ) - A = 2 * p := by
    have : B = A + 2 * p := by omega
    rw [this]; push_cast; ring
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have g1 : Good p (1 / (32 : ℚ)) ((32 : ZMod p)⁻¹) :=
    ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 32) h32).congr (by simp)
  have := g1.mul (sum_good_p hL hp5 hk4 (Ioc A B) S0 hS0 h1 res hsing hr)
  refine this.congr' ?_
  rw [hBQ]
  field_simp
  ring

/-- The data of a singular set below `Nb`. -/
structure SgData (Fr : Frame) (o p Nb k : ℕ) [Fact p.Prime] (Sg : Finset ℕ) (res resD : ℕ → ZMod p) :
    Prop where
  pos : ∀ t ∈ Sg, 1 ≤ t
  sing : ∀ t ∈ Sg, Good p ((p : ℚ) * Fr.Delta t) (res t)
  singD : ∀ t ∈ Sg, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (resD t)
  reg : ∀ t, 1 ≤ t → t < Nb → t ∉ Sg → Reg p k t
  hk4 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p)

variable {Fr : Frame} {Nb k : ℕ} {Sg : Finset ℕ} {res resD : ℕ → ZMod p}

section Tabs

variable (hL : LamData Fr o) (hp5 : 5 ≤ p) (D : SgData Fr o p Nb k Sg res resD)
include hL hp5 D

private lemma tab_aux {A B : ℕ} (hAB : A < B) (hB : B < Nb) :
    Sg.filter (fun t => t ∈ Ioc A B) ⊆ Ioc A B ∧
    (∀ t ∈ Ioc A B \ Sg.filter (fun t => t ∈ Ioc A B), 1 ≤ t) ∧
    (∀ t ∈ Ioc A B \ Sg.filter (fun t => t ∈ Ioc A B), Reg p k t) := by
  refine ⟨fun t ht => (Finset.mem_filter.1 ht).2, ?_, ?_⟩
  · intro t ht; have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
  · intro t ht
    obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
    have hI' := Finset.mem_Ioc.1 hI
    refine D.reg t (by omega) (by omega) ?_
    intro hs; exact hn (Finset.mem_filter.2 ⟨hs, hI⟩)

theorem tab_P1 {A B : ℕ} (hAB : A < B) (hB : B < Nb) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p ((p : ℚ) * Fr.Mn A B)
      ((16 * ((B : ZMod p) - A))⁻¹ * (Lv Sg res B - Lv Sg res A)) := by
  obtain ⟨h1, h2, h3⟩ := tab_aux hL hp5 D hAB hB
  have := Mn_goodP hL hp5 D.hk4 hAB _ h1 h2 res (fun t ht => D.sing t (Finset.mem_filter.1 ht).1) h3 hd
  rwa [sum_Ioc_Lv Sg res hAB.le] at this

theorem tab_PP {A B : ℕ} (hAB : A < B) (hB : B < Nb) (hBA : B - A = p) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((16 : ZMod p)⁻¹ * (Lv Sg res B - Lv Sg res A)) := by
  obtain ⟨h1, h2, h3⟩ := tab_aux hL hp5 D hAB hB
  have := Mn_goodPP hL hp5 D.hk4 hAB hBA _ h1 h2 res (fun t ht => D.sing t (Finset.mem_filter.1 ht).1) h3
  rwa [sum_Ioc_Lv Sg res hAB.le] at this

theorem tab_P2P {A B : ℕ} (hAB : A < B) (hB : B < Nb) (hBA : B - A = 2 * p) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) ((32 : ZMod p)⁻¹ * (Lv Sg res B - Lv Sg res A)) := by
  obtain ⟨h1, h2, h3⟩ := tab_aux hL hp5 D hAB hB
  have := Mn_good2PP hL hp5 D.hk4 hAB hBA _ h1 h2 res (fun t ht => D.sing t (Finset.mem_filter.1 ht).1) h3
  rwa [sum_Ioc_Lv Sg res hAB.le] at this

theorem tab_P0 {A B : ℕ} (hAB : A < B) (hB : B < Nb) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) 0 := by
  have := (tab_P1 hL hp5 D hAB hB hd).ell_mul
  refine this.congr' ?_
  ring

theorem tab_D {A : ℕ} (hA : A < Nb) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A A) (-(1 / 16 : ZMod p) * Lv Sg resD A) := by
  have hS0 : Sg.filter (fun t => t ∈ Icc 1 A) ⊆ Icc 1 A := fun t ht => (Finset.mem_filter.1 ht).2
  have := Mn_diag_goodP2 hL hp5 D.hk4 (A := A) _ hS0 resD
    (fun t ht => D.singD t (Finset.mem_filter.1 ht).1)
    (fun t ht => by
      obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
      have hI' := Finset.mem_Icc.1 hI
      refine D.reg t hI'.1 (by omega) ?_
      intro hs; exact hn (Finset.mem_filter.2 ⟨hs, hI⟩))
  rwa [sum_Icc_Lv Sg resD D.pos] at this

end Tabs

end Gen

end CatalanCore.Arith.Hybrid
