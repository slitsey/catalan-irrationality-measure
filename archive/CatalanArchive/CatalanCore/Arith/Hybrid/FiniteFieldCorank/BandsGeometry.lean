module
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.Bands
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.RootFactor
@[expose] public section
open Finset Polynomial
namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

structure BandGeometry (ell K m S g : ℕ) : Prop where
  prime : ell.Prime
  hK : 1 ≤ K
  hS : 1 < S
  hSg : S ≤ g
  room : K + g + 2 * m ≤ ell

variable {ell K m S g : ℕ} [Fact ell.Prime]

def lowBand (ell K : ℕ) : Finset (ZMod ell) := insert 0 (zband ell (ell-K+1) ell)
def highBand (ell g : ℕ) : Finset (ZMod ell) := zband ell 1 (g+1)
def borderBand (ell g m : ℕ) : Finset (ZMod ell) := zband ell (g+1) (g+2*m+1)
def tailBand (ell K g m : ℕ) : Finset (ZMod ell) := zband ell (g+2*m+1) (ell-K+1)
def lowAdjBand (ell K : ℕ) : Finset (ZMod ell) := zband ell (ell-K+1) ell
def highAdjBand (ell S g : ℕ) : Finset (ZMod ell) :=
  zband ell 1 (S-1) ∪ zband ell S g

def bandSign (S : ℕ) (y : ZMod ell) : ZMod ell := if y.val < S then 1 else -2

lemma lowBand_mem (H : BandGeometry ell K m S g) (x : ZMod ell) :
    x ∈ lowBand ell K ↔ x.val = 0 ∨ ell-K+1 ≤ x.val := by
  have hh : ell-K+1 ≤ ell := by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega
  rw [lowBand, mem_insert, mem_zband_iff le_rfl, ← ZMod.val_eq_zero x]
  have hx := x.val_lt
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_lowBand (H : BandGeometry ell K m S g) : (lowBand ell K).card = K := by
  have hK : K ≤ ell := by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega
  have hz : (0 : ZMod ell) ∉ zband ell (ell-K+1) ell := by
    rw [mem_zband_iff le_rfl]; simp only [ZMod.val_zero]; have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega
  rw [lowBand, card_insert_of_notMem hz, card_zband le_rfl]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_highBand (H : BandGeometry ell K m S g) : (highBand ell g).card = g := by
  unfold highBand
  rw [card_zband (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_borderBand (H : BandGeometry ell K m S g) :
    (borderBand ell g m).card = 2*m := by
  unfold borderBand
  rw [card_zband (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_tailBand (H : BandGeometry ell K m S g) :
    (tailBand ell K g m).card = ell-K-g-2*m := by
  unfold tailBand
  rw [card_zband (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_lowAdjBand (H : BandGeometry ell K m S g) :
    (lowAdjBand ell K).card = K-1 := by
  unfold lowAdjBand
  rw [card_zband le_rfl]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma card_highAdjBand (H : BandGeometry ell K m S g) :
    (highAdjBand ell S g).card = g-2 := by
  have hd : Disjoint (zband ell 1 (S-1)) (zband ell S g) :=
    zband_disjoint (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)
  rw [highAdjBand, card_union_of_disjoint hd, card_zband (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega), card_zband (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)]
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma bands_partition (H : BandGeometry ell K m S g) :
    lowBand ell K ∪ highBand ell g ∪ borderBand ell g m ∪ tailBand ell K g m = univ := by
  ext x
  simp only [mem_union, mem_univ, iff_true]
  rw [lowBand_mem H, highBand, borderBand, tailBand,
    mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega), mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega), mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)]
  have hx := x.val_lt
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma low_high_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (lowBand ell K) (highBand ell g) := by
  apply disjoint_left.2
  intro x hx hy
  rw [lowBand_mem H] at hx
  rw [highBand, mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)] at hy
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma low_border_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (lowBand ell K) (borderBand ell g m) := by
  apply disjoint_left.2
  intro x hx hy
  rw [lowBand_mem H] at hx
  rw [borderBand, mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)] at hy
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma low_tail_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (lowBand ell K) (tailBand ell K g m) := by
  apply disjoint_left.2
  intro x hx hy
  rw [lowBand_mem H] at hx
  rw [tailBand, mem_zband_iff (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)] at hy
  have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega

lemma high_border_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (highBand ell g) (borderBand ell g m) :=
  zband_disjoint (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) le_rfl
lemma high_tail_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (highBand ell g) (tailBand ell K g m) :=
  zband_disjoint (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega)
lemma border_tail_disjoint (H : BandGeometry ell K m S g) :
    Disjoint (borderBand ell g m) (tailBand ell K g m) :=
  zband_disjoint (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) (by have := H.hK; have := H.hS; have := H.hSg; have := H.room; omega) le_rfl

lemma card_supportBand (H : BandGeometry ell K m S g) :
    (lowBand ell K ∪ highBand ell g).card = K+g := by
  rw [card_union_of_disjoint (low_high_disjoint H), card_lowBand H, card_highBand H]

lemma rootProduct_union (s t : Finset (ZMod ell)) (h : Disjoint s t) :
    rootProduct (s ∪ t) = rootProduct s * rootProduct t := by
  exact Finset.prod_union h

lemma rootProduct_bands (H : BandGeometry ell K m S g) :
    rootProduct (lowBand ell K) * rootProduct (highBand ell g) *
      rootProduct (borderBand ell g m) * rootProduct (tailBand ell K g m) =
      X^ell-X := by
  have hd1 := low_high_disjoint H
  have hd2 : Disjoint (lowBand ell K ∪ highBand ell g) (borderBand ell g m) :=
    disjoint_union_left.mpr ⟨low_border_disjoint H, high_border_disjoint H⟩
  have hd3 : Disjoint (lowBand ell K ∪ highBand ell g ∪ borderBand ell g m)
      (tailBand ell K g m) :=
    disjoint_union_left.mpr ⟨disjoint_union_left.mpr ⟨low_tail_disjoint H,
      high_tail_disjoint H⟩, border_tail_disjoint H⟩
  rw [← rootProduct_union _ _ hd1, ← rootProduct_union _ _ hd2,
    ← rootProduct_union _ _ hd3, bands_partition H, rootProduct_univ]





lemma val_add_one (x : ZMod ell) : (x+1).val = (x.val+1)%ell := by
  rw [ZMod.val_add, ZMod.val_one'' (Fact.out : ell.Prime).ne_one]

lemma lowAdj_neighbors (H : BandGeometry ell K m S g) {x : ZMod ell}
    (hx : x ∈ lowAdjBand ell K) : x ∈ lowBand ell K ∧ x+1 ∈ lowBand ell K := by
  have hv := (mem_zband_iff le_rfl x).1 hx
  constructor
  · exact mem_insert_of_mem hx
  · rw [lowBand_mem H, val_add_one]
    by_cases ht : x.val+1 < ell
    · rw [Nat.mod_eq_of_lt ht]
      right; omega
    · have he : x.val+1=ell := by omega
      simp [he]

lemma highAdj_neighbors (H : BandGeometry ell K m S g) {x : ZMod ell}
    (hx : x ∈ highAdjBand ell S g) :
    x ∈ highBand ell g ∧ x+1 ∈ highBand ell g ∧ bandSign S x = bandSign S (x+1) := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  have he : g+1 ≤ ell := by omega
  have hx' : (1 ≤ x.val ∧ x.val < S-1) ∨ (S ≤ x.val ∧ x.val < g) := by
    simpa only [highAdjBand, mem_union, mem_zband_iff (show S-1 ≤ ell by omega),
      mem_zband_iff (show g ≤ ell by omega)] using hx
  have ht : x.val+1 < ell := by rcases hx' with h|h <;> omega
  have hv : (x+1).val=x.val+1 := by rw [val_add_one, Nat.mod_eq_of_lt ht]
  constructor
  · rw [highBand, mem_zband_iff he]; rcases hx' with h|h <;> omega
  constructor
  · rw [highBand, mem_zband_iff he, hv]; rcases hx' with h|h <;> omega
  · unfold bandSign
    rw [hv]
    rcases hx' with h|h
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

lemma tailBand_neighbor (H : BandGeometry ell K m S g) {x : ZMod ell}
    (hx : x ∈ tailBand ell K g m) :
    x+1 ∈ tailBand ell K g m ∨ x+1 ∈ lowBand ell K := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  have hv := (mem_zband_iff (show ell-K+1 ≤ ell by omega) x).1 hx
  by_cases ht : x.val+1 < ell
  · have hv' : (x+1).val=x.val+1 := by rw [val_add_one, Nat.mod_eq_of_lt ht]
    by_cases hc : x.val+1 < ell-K+1
    · left; rw [tailBand, mem_zband_iff (by omega), hv']; omega
    · right; rw [lowBand_mem H, hv']; omega
  · right; rw [lowBand_mem H, val_add_one]
    have he : x.val+1=ell := by have := x.val_lt; omega
    simp [he]

noncomputable def fixedBandQ (ell K S g m : ℕ) [Fact ell.Prime] : (ZMod ell)[X] :=
  rootProduct (lowAdjBand ell K)^3 * rootProduct (highAdjBand ell S g) *
    rootProduct (tailBand ell K g m)

lemma fixedBandQ_degree (H : BandGeometry ell K m S g) (hn : 3 ≤ K-m) :
    (fixedBandQ ell K S g m).natDegree=ell+2*(K-m)-5 := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  unfold fixedBandQ
  rw [natDegree_mul (mul_ne_zero (pow_ne_zero _ ((rootProduct_monic _).ne_zero))
      ((rootProduct_monic _).ne_zero)) ((rootProduct_monic _).ne_zero),
    natDegree_mul (pow_ne_zero _ ((rootProduct_monic _).ne_zero)) ((rootProduct_monic _).ne_zero),
    natDegree_pow, natDegree_rootProduct, natDegree_rootProduct, natDegree_rootProduct,
    card_lowAdjBand H, card_highAdjBand H, card_tailBand H]
  omega

lemma jump_band_exclusions (H : BandGeometry ell K m S g) :
    ((S-1 : ℕ) : ZMod ell) ∉ lowAdjBand ell K ∧
      ((S-1 : ℕ) : ZMod ell) ∉ highAdjBand ell S g ∧
      ((S-1 : ℕ) : ZMod ell) ∉ tailBand ell K g m := by
  have hk := H.hK; have hs := H.hS; have hsg := H.hSg; have hr := H.room
  have hS : S-1 < ell := by omega
  have hl : ((S-1 : ℕ) : ZMod ell) ∉ lowAdjBand ell K := by
    rw [lowAdjBand, mem_zband_iff le_rfl, ZMod.val_natCast_of_lt hS]
    omega
  have hh : ((S-1 : ℕ) : ZMod ell) ∉ highAdjBand ell S g := by
    rw [highAdjBand, mem_union, mem_zband_iff (by omega), mem_zband_iff (by omega),
      ZMod.val_natCast_of_lt hS]
    omega
  have ht : ((S-1 : ℕ) : ZMod ell) ∉ tailBand ell K g m := by
    rw [tailBand, mem_zband_iff (by omega), ZMod.val_natCast_of_lt hS]
    omega
  exact ⟨hl, hh, ht⟩

lemma fixedBandQ_eval_jump (H : BandGeometry ell K m S g) :
    (fixedBandQ ell K S g m).eval ((S-1 : ℕ) : ZMod ell) ≠ 0 := by
  obtain ⟨hl,hh,ht⟩ := jump_band_exclusions H
  have he (s : Finset (ZMod ell)) (hn : ((S-1 : ℕ) : ZMod ell) ∉ s) :
      (rootProduct s).eval ((S-1 : ℕ) : ZMod ell) ≠ 0 := by
    simp only [rootProduct, eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact sub_ne_zero.mpr (fun h => hn (h.symm ▸ ha))
  simpa only [fixedBandQ, eval_mul, eval_pow] using
    mul_ne_zero (mul_ne_zero (pow_ne_zero 3 (he _ hl)) (he _ hh)) (he _ ht)

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
