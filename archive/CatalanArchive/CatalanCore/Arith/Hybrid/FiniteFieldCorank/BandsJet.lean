module
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsGeometry
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.JetGeometry
@[expose] public section
open Finset Polynomial
namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank
variable {ell K m S g : ℕ} [Fact ell.Prime]

noncomputable def BandGeometry.toJetGeometry (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) :
    JetGeometry (ZMod ell) ell (K-m) where
  low := lowBand ell K
  high := highBand ell g
  lowAdj := lowAdjBand ell K
  highAdj := highAdjBand ell S g
  tail := tailBand ell K g m
  jump := ((S-1 : ℕ) : ZMod ell)
  eps := bandSign S
  low_card := by rw [card_lowBand H]; omega
  high_card := by rw [card_highBand H]; exact hng
  low_frob := by intro a ha; exact ZMod.pow_card a
  high_unit := by intro a ha; unfold bandSign; split_ifs <;> simp_all
  low_adj := fun _ ha => lowAdj_neighbors H ha
  high_adj := fun _ ha => highAdj_neighbors H ha
  tail_adj := fun _ ha => tailBand_neighbor H ha
  disj_lh := by
    apply (low_high_disjoint H).mono
    · intro a ha; exact mem_insert_of_mem ha
    · intro a ha; exact (highAdj_neighbors H ha).1
  disj_lt := by
    apply (low_tail_disjoint H).mono_left
    intro a ha; exact mem_insert_of_mem ha
  disj_ht := by
    apply (high_tail_disjoint H).mono_left
    intro a ha; exact (highAdj_neighbors H ha).1
  degree_count := by
    rw [card_lowAdjBand H, card_highAdjBand H, card_tailBand H]
    have := H.hK; have := H.hS; have := H.hSg; have := H.room
    omega
  jump_l := (jump_band_exclusions H).1
  jump_h := (jump_band_exclusions H).2.1
  jump_t := (jump_band_exclusions H).2.2
  jump_high := by
    have := H.hK; have := H.hS; have := H.hSg; have := H.room
    rw [highBand, mem_zband_iff (by omega), ZMod.val_natCast_of_lt (by omega)]
    omega
  jump_succ_high := by
    have := H.hK; have := H.hS; have := H.hSg; have := H.room
    have hs : ((S-1 : ℕ) : ZMod ell)+1=(S : ZMod ell) := by
      have he := congrArg (fun a : ℕ => (a : ZMod ell)) (show S-1+1=S by omega)
      simpa only [Nat.cast_add, Nat.cast_one] using he
    rw [hs, highBand, mem_zband_iff (by omega), ZMod.val_natCast_of_lt (by omega)]
    omega

#print axioms BandGeometry.toJetGeometry
end CatalanCore.Arith.Hybrid.FiniteFieldCorank
