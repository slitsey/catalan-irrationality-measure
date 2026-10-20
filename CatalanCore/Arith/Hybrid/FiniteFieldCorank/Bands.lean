module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.Interpolation
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

open Finset Polynomial

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

/-- A natural half-open interval, embedded into the prime residue field. -/
def zband (ell lo hi : ℕ) : Finset (ZMod ell) :=
  (Finset.Ico lo hi).image (fun a : ℕ => (a : ZMod ell))

lemma mem_zband_iff {ell lo hi : ℕ} [NeZero ell] (hh : hi ≤ ell) (x : ZMod ell) :
    x ∈ zband ell lo hi ↔ lo ≤ x.val ∧ x.val < hi := by
  constructor
  · intro hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    have h := Finset.mem_Ico.1 ha
    simpa only [ZMod.val_natCast_of_lt (by omega : a < ell)] using h
  · intro hx
    apply Finset.mem_image.2
    exact ⟨x.val, Finset.mem_Ico.2 hx, ZMod.natCast_zmod_val x⟩

lemma card_zband {ell lo hi : ℕ} [NeZero ell] (hh : hi ≤ ell) :
    (zband ell lo hi).card = hi - lo := by
  unfold zband
  rw [Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha b hb hab
  have ha' := Finset.mem_Ico.1 ha
  have hb' := Finset.mem_Ico.1 hb
  have hv := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt (by omega : a < ell),
    ZMod.val_natCast_of_lt (by omega : b < ell)] using hv

lemma zband_disjoint {ell a b c d : ℕ} [NeZero ell]
    (hb : b ≤ ell) (hd : d ≤ ell) (hbc : b ≤ c) :
    Disjoint (zband ell a b) (zband ell c d) := by
  apply Finset.disjoint_left.2
  intro x hx hy
  have h1 := (mem_zband_iff hb x).1 hx
  have h2 := (mem_zband_iff hd x).1 hy
  omega

lemma zband_univ (ell : ℕ) [NeZero ell] : zband ell 0 ell = Finset.univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  apply (mem_zband_iff le_rfl x).2
  exact ⟨Nat.zero_le _, ZMod.val_lt x⟩

lemma rootProduct_univ (ell : ℕ) [Fact ell.Prime] :
    rootProduct (Finset.univ : Finset (ZMod ell)) = X ^ ell - X := by
  have hp : 1 < ell := (Fact.out : ell.Prime).one_lt
  have hm : (X ^ ell - X : (ZMod ell)[X]).Monic :=
    monic_X_pow_sub (by simpa using hp)
  have hr := FiniteField.roots_X_pow_card_sub_X (ZMod ell)
  have hd := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod ell) hp
  simp only [ZMod.card] at hr
  have hc : Multiset.card (X ^ ell - X : (ZMod ell)[X]).roots =
      (X ^ ell - X : (ZMod ell)[X]).natDegree := by
    rw [hr, Finset.card_val, Finset.card_univ, ZMod.card, hd]
  have he := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm hc
  rw [hr] at he
  exact he

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
