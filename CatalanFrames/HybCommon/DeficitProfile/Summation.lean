module
public import CatalanFrames.HybCommon.DeficitProfile
public import CatalanCore.Arith.Hybrid.AffineProfileSum
@[expose] public section
set_option maxRecDepth 10000
open Finset Filter CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

lemma profileClass_unit {o : ℕ} (ho : o=1 ∨ o=3) (P : DeficitRow) :
    IsUnit (profileClass o P) := by
  rcases ho with rfl|rfl <;> unfold profileClass <;> split_ifs <;> norm_num <;> decide

lemma toPiece_area (P : DeficitRow) (C : ℝ) : (P.toPiece C).int=(P.area : ℝ) := by
  simp only [DeficitRow.toPiece, Piece.int, DeficitRow.area]
  push_cast
  rfl

lemma profile_area_real (C : ℝ) :
    (∑P∈newProfile.toFinset,(P.toPiece C).int)/2=(profileIntegral : ℝ) := by
  simp_rw [toPiece_area]
  rw [←Rat.cast_sum, List.sum_toFinset DeficitRow.area newProfile_nodup]
  simp only [profileIntegral, Rat.cast_div, Rat.cast_ofNat]

/-- The full finite profile sum; the geometric lower covers are an explicit input. -/
theorem profile_piece_sum_lower {o : ℕ} (ho : o=1 ∨ o=3) (δ : NewDeficit)
    {C : ℝ} (hC : 0≤C) (hcover : ProfileCover o δ C)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop,
      (r : ℝ)^2*((profileIntegral : ℝ)-ε)≤
        ∑P∈newProfile.toFinset,
          clsSum 4 (profileClass o P) (fun p => (δ r p : ℝ))
            ⌊(P.lo : ℝ)*r⌋₊ ⌊(P.hi : ℝ)*r⌋₊ := by
  have hP : ∀P∈newProfile.toFinset,
      0<(P.toPiece C).s ∧ (P.toPiece C).s≤(P.toPiece C).t ∧ 0≤(P.toPiece C).C := by
    intro P hP
    have hh := newProfile_cert P (List.mem_toFinset.mp hP)
    refine ⟨?_,?_,hC⟩
    · change (0:ℝ)<(P.lo:ℝ)
      exact_mod_cast hh.2.1
    · change (P.lo:ℝ)≤(P.hi:ℝ)
      exact_mod_cast hh.2.2.1.le
  have h := finite_piece_sum_lower newProfile.toFinset (profileClass o) (fun P => P.toPiece C)
    (fun P _ => profileClass_unit ho P) hP hε
  filter_upwards [h,hcover] with r hr hc
  have hh := hr (fun p => (δ r p : ℝ)) (fun P hP => hc P (List.mem_toFinset.mp hP))
  have he : ((∑P∈newProfile.toFinset,(P.toPiece C).int)/(Nat.totient 4 : ℝ))=(profileIntegral : ℝ) := by
    simpa only [show Nat.totient 4=2 by decide, Nat.cast_ofNat] using profile_area_real C
  rw [he] at hh
  exact hh

instance : Std.Symm DeficitRow.disjoint where
  symm P Q h := by
    rcases h with h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

lemma profileClass_tag_eq {o : ℕ} (ho : o=1 ∨ o=3) {P Q : DeficitRow}
    (hP : P.poleClass=1 ∨ P.poleClass=3) (hQ : Q.poleClass=1 ∨ Q.poleClass=3)
    (he : profileClass o P=profileClass o Q) : P.poleClass=Q.poleClass := by
  rcases hP with hP|hP <;> rcases hQ with hQ|hQ
  · omega
  · rcases ho with rfl|rfl <;> norm_num [profileClass,hP,hQ] at he <;> exact False.elim (by first | exact (by decide : (3 : ZMod 4)≠1) he | exact (by decide : (1 : ZMod 4)≠3) he)
  · rcases ho with rfl|rfl <;> norm_num [profileClass,hP,hQ] at he <;> exact False.elim (by first | exact (by decide : (3 : ZMod 4)≠1) he | exact (by decide : (1 : ZMod 4)≠3) he)
  · omega

lemma profile_window_unique {o : ℕ} (ho : o=1 ∨ o=3) (r p : ℕ)
    {P Q : DeficitRow} (hP : P∈newProfile) (hQ : Q∈newProfile)
    (hPl : ⌊(P.lo : ℝ)*r⌋₊<p) (hPh : p≤⌊(P.hi : ℝ)*r⌋₊)
    (hPc : (p : ZMod 4)=profileClass o P)
    (hQl : ⌊(Q.lo : ℝ)*r⌋₊<p) (hQh : p≤⌊(Q.hi : ℝ)*r⌋₊)
    (hQc : (p : ZMod 4)=profileClass o Q) : P=Q := by
  by_contra hne
  have hd := newProfile_pairwise.forall hP hQ hne
  have htags := profileClass_tag_eq ho (newProfile_cert P hP).1 (newProfile_cert Q hQ).1 (hPc.symm.trans hQc)
  rcases hd with hd|hd|hd
  · exact hd htags
  · have hh : ⌊(P.hi : ℝ)*r⌋₊≤⌊(Q.lo : ℝ)*r⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (Nat.cast_nonneg r))
    omega
  · have hh : ⌊(Q.hi : ℝ)*r⌋₊≤⌊(P.lo : ℝ)*r⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (Nat.cast_nonneg r))
    omega

/-- PNT lower bound for the new deficit, with no arithmetic nonvanishing conclusion assumed. -/
theorem profile_sum_lower {o : ℕ} (ho : o=1 ∨ o=3) (δ : NewDeficit)
    {C : ℝ} (hC : 0≤C) (hcover : ProfileCover o δ C)
    (N : ℕ→ℕ) (hN : ∀r : ℕ,∀P∈newProfile,⌊(P.hi : ℝ)*r⌋₊<N r)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr : ℕ in atTop,
      (r : ℝ)^2*((profileIntegral : ℝ)-ε)≤
        ∑p∈(range (N r)).filter Nat.Prime,(δ r p : ℝ)*Real.log p := by
  filter_upwards [profile_piece_sum_lower ho δ hC hcover hε] with r hr
  refine hr.trans ?_
  apply sum_clsSum_le newProfile.toFinset (profileClass o)
    (fun P => ⌊(P.lo : ℝ)*r⌋₊) (fun P => ⌊(P.hi : ℝ)*r⌋₊) (N r) (fun p => (δ r p : ℝ))
  · intro P hP; exact hN r P (List.mem_toFinset.mp hP)
  · intro p; positivity
  · intro p hp P hP Q hQ hPl hPh hPc hQl hQh hQc
    exact profile_window_unique ho r p (List.mem_toFinset.mp hP) (List.mem_toFinset.mp hQ)
      hPl hPh hPc hQl hQh hQc

#print axioms profile_sum_lower
end CatalanFrames.HybCommon
