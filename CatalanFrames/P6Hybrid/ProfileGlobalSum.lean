module
public import CatalanFrames.P6Hybrid.ProfileSummation
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid

def IntervalRow.disjoint (P Q : IntervalRow) : Prop :=
  P.c≠Q.c ∨ (P.hiN:ℚ)/P.hiD≤(Q.loN:ℚ)/Q.loD ∨ (Q.hiN:ℚ)/Q.hiD≤(P.loN:ℚ)/P.loD
instance : Std.Symm IntervalRow.disjoint where
  symm P Q h := by
    rcases h with h|h|h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

lemma intervalProfile_window_unique {r p : ℕ} {P Q : IntervalRow}
    (hP : P∈intervalProfile) (hQ : Q∈intervalProfile)
    (hPl : ⌊P.toPiece.s*r⌋₊<p) (hPh : p≤⌊P.toPiece.t*r⌋₊)
    (hPc : (p:ZMod 6)=P.c)
    (hQl : ⌊Q.toPiece.s*r⌋₊<p) (hQh : p≤⌊Q.toPiece.t*r⌋₊)
    (hQc : (p:ZMod 6)=Q.c) : P=Q := by
  by_contra hne
  have hpair : intervalProfile.Pairwise IntervalRow.disjoint:=intervalProfile_disjoint
  have H:=hpair.forall hP hQ hne
  have hcp : P.c<6 :=(intervalProfile_data P hP).2.2.2.2.2.2
  have hcq : Q.c<6 :=(intervalProfile_data Q hQ).2.2.2.2.2.2
  have hc : P.c=Q.c := by
    have H:=congrArg ZMod.val (hPc.symm.trans hQc)
    simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hcp,Nat.mod_eq_of_lt hcq] using H
  rcases H with H|H|H
  · exact H hc
  · have hh : ⌊P.toPiece.t*r⌋₊≤⌊Q.toPiece.s*r⌋₊ := by
      apply Nat.floor_le_floor
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg r)
      change (P.hiN:ℝ)/P.hiD≤(Q.loN:ℝ)/Q.loD
      have HR:=(Rat.cast_le (K:=ℝ)).2 H
      push_cast at HR
      exact HR
    omega
  · have hh : ⌊Q.toPiece.t*r⌋₊≤⌊P.toPiece.s*r⌋₊ := by
      apply Nat.floor_le_floor
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg r)
      change (Q.hiN:ℝ)/Q.hiD≤(P.loN:ℝ)/P.loD
      have HR:=(Rat.cast_le (K:=ℝ)).2 H
      push_cast at HR
      exact HR
    omega

theorem intervalProfile_sum_lower (mf : ℕ→ℕ)
    (hadm : ∀r,r≤8*mf r ∧ 8*mf r≤r+9) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr:ℕ in atTop,
      (r:ℝ)^2*((11983/645120:ℝ)-ε)≤
        ∑p∈(range (Bnd (p6Inst r (mf r)) r (mf r))).filter Nat.Prime,
          (intervalDeficit r (mf r) p:ℝ)*Real.log p := by
  filter_upwards [intervalProfile_piece_sum_lower mf hadm hε] with r hr
  refine hr.trans ?_
  apply sum_clsSum_le intervalProfile.toFinset (fun P=>(P.c:ZMod 6))
    (fun P=>⌊P.toPiece.s*r⌋₊) (fun P=>⌊P.toPiece.t*r⌋₊)
    (Bnd (p6Inst r (mf r)) r (mf r)) (fun p=>(intervalDeficit r (mf r) p:ℝ))
  · intro P hP
    have hd:=intervalProfile_data P (List.mem_toFinset.mp hP)
    have H : ⌊P.toPiece.t*r⌋₊≤r := by
      have hh : P.toPiece.t≤1 := by
        change (P.hiN:ℝ)/P.hiD≤1
        have HR:=(Rat.cast_le (K:=ℝ)).2 hd.2.2.2.2.2.1
        push_cast at HR
        exact HR
      have H:=Nat.floor_le_floor (mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg r))
      simpa only [one_mul,Nat.floor_natCast] using H
    have hb : r<Bnd (p6Inst r (mf r)) r (mf r) := by
      change r<3*(r+2*mf r)+6
      omega
    omega
  · intro p;positivity
  · intro p hp P hP Q hQ hPl hPh hPc hQl hQh hQc
    exact intervalProfile_window_unique (List.mem_toFinset.mp hP) (List.mem_toFinset.mp hQ)
      hPl hPh hPc hQl hQh hQc
end CatalanFrames.P6Hybrid
