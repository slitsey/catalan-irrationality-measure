module
public import CatalanArchive.CatalanFrames.P6Hybrid.ProfileDenominator
public import CatalanCore.Arith.Hybrid.AffineProfileSum
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid

noncomputable def IntervalRow.toPiece (P : IntervalRow) : Piece :=
  mkPiece P.loN P.loD P.hiN P.hiD P.A P.B (100*P.den) P.den

lemma intervalRow_piece_area (P : IntervalRow) : P.toPiece.int=2*(P.area:ℝ) := by
  simp only [IntervalRow.toPiece,mkPiece,Piece.int,IntervalRow.area]
  push_cast
  simp only [div_eq_mul_inv]
  ring

lemma intervalProfile_area_real :
    (∑P∈intervalProfile.toFinset,P.toPiece.int)/2=(11983/645120:ℝ) := by
  simp_rw [intervalRow_piece_area]
  rw [←Finset.mul_sum,←Rat.cast_sum,List.sum_toFinset IntervalRow.area intervalProfile_nodup,
    intervalProfile_gain]
  norm_num

lemma intervalRow_lowerCovers (P : IntervalRow) (hP : P∈intervalProfile)
    {r m : ℕ} (hm1 : r≤8*m) (hm2 : 8*m≤r+9) :
    LowerCovers (P.c:ZMod 6) (fun p=>(intervalDeficit r m p:ℝ)) r P.toPiece := by
  intro p hlo hhi hp hpc
  have hd:=intervalProfile_data P hP
  rw [IntervalRow.toPiece,floor_mk_s] at hlo
  rw [IntervalRow.toPiece,floor_mk_t] at hhi
  have hclass : p%6=P.c := by
    have H:=(ZMod.natCast_eq_natCast_iff' p P.c 6).mp hpc
    rwa [Nat.mod_eq_of_lt hd.2.2.2.2.2.2] at H
  have ha : P.active r p := ⟨hclass,
    by simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hd.2.1).mp hlo,
    by have H:=(Nat.le_div_iff_mul_le hd.2.2.1).mp hhi;simpa [mul_comm] using H⟩
  have H:=intervalProfile_arithmetic P hP hm1 hm2 ha
  have hs : intervalRowDeficit P r m p ≤ intervalDeficit r m p :=
    Finset.le_sup (f:=fun P=>intervalRowDeficit P r m p) (List.mem_toFinset.mpr hP)
  rw [intervalRowDeficit,if_pos ha] at hs
  have H': (P.A:ℝ)*r+(P.B:ℝ)*p-100*P.den≤
      (P.den:ℝ)*((p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m:ℕ):ℝ) := by exact_mod_cast H
  have hs' : ((p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m:ℕ):ℝ) ≤ intervalDeficit r m p := by exact_mod_cast hs
  have hd' : (0:ℝ)<P.den := by exact_mod_cast hd.1
  simp only [IntervalRow.toPiece,mkPiece]
  push_cast
  have H'' : ((P.A:ℝ)*r+(P.B:ℝ)*p-100*P.den)/P.den ≤ (intervalDeficit r m p:ℝ) :=
    (div_le_iff₀ hd').mpr (by nlinarith [mul_le_mul_of_nonneg_left hs' hd'.le])
  convert H'' using 1 <;> field_simp <;> ring

lemma intervalProfile_piece_sum_lower (mf : ℕ→ℕ)
    (hadm : ∀r,r≤8*mf r ∧ 8*mf r≤r+9) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠr:ℕ in atTop,
      (r:ℝ)^2*((11983/645120:ℝ)-ε)≤
        ∑P∈intervalProfile.toFinset,clsSum 6 (P.c:ZMod 6)
          (fun p=>(intervalDeficit r (mf r) p:ℝ)) ⌊P.toPiece.s*r⌋₊ ⌊P.toPiece.t*r⌋₊ := by
  have h:=finite_piece_sum_lower intervalProfile.toFinset (fun P=>(P.c:ZMod 6))
    IntervalRow.toPiece (by
      intro P hP
      rcases (intervalProfile_poles P (List.mem_toFinset.mp hP)).1 with h|h <;> rw [h] <;> decide)
    (by
      intro P hP
      have hd:=intervalProfile_data P (List.mem_toFinset.mp hP)
      refine ⟨?_,?_,?_⟩
      · change (0:ℝ)<(P.loN:ℝ)/P.loD
        exact div_pos (by exact_mod_cast hd.2.2.2.1) (by exact_mod_cast hd.2.1)
      · change (P.loN:ℝ)/P.loD≤(P.hiN:ℝ)/P.hiD
        have H:=(Rat.cast_le (K:=ℝ)).2 hd.2.2.2.2.1
        push_cast at H
        exact H
      · simp only [IntervalRow.toPiece,mkPiece]
        push_cast
        positivity) hε
  filter_upwards [h] with r hr
  have H:=hr (fun p=>(intervalDeficit r (mf r) p:ℝ))
    (fun P hP=>intervalRow_lowerCovers P (List.mem_toFinset.mp hP) (hadm r).1 (hadm r).2)
  simpa only [show Nat.totient 6=2 by decide,Nat.cast_ofNat,intervalProfile_area_real] using H
end CatalanFrames.P6Hybrid
