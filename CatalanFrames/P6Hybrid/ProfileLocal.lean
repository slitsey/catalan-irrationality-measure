module
public import CatalanFrames.P6Hybrid.IntervalProfile
public import CatalanFrames.P6Hybrid.Pieces
@[expose] public section
open Finset Polynomial Matrix CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open CatalanFrames.P6

noncomputable def intervalRowDeficit (P : IntervalRow) (r m p : ℕ) : ℕ := by
  classical
  exact if P.active r p then
    p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m else 0

noncomputable def intervalBase (r m p : ℕ) : ℕ :=
  if p=2 ∨ p=3 then tropExp (p6Inst r m) r m p else
    max (tropExp (p6Inst r m) r m p) (Wn r m p)

lemma intervalBase_ge_trop (r m p : ℕ) : tropExp (p6Inst r m) r m p ≤ intervalBase r m p := by
  unfold intervalBase
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

lemma intervalBase_ge_Wn (P : IntervalRow) (hP : P∈intervalProfile)
    {r m p : ℕ} (ha : P.active r p) : Wn r m p ≤ intervalBase r m p := by
  have hc:=(intervalProfile_poles P hP).1
  have hn : ¬(p=2 ∨ p=3) := by
    have H:=ha.1
    rcases hc with h|h <;> rw [h] at H <;> omega
  unfold intervalBase
  rw [if_neg hn]
  exact le_max_right _ _

lemma intervalProfile_baseline (P : IntervalRow) (hP : P∈intervalProfile)
    {r m p : ℕ} (ha : P.active r p) (hpm : 2*m<p) : Wn r m p=2*r+m := by
  simp only [intervalProfile,List.mem_cons,List.mem_nil_iff,or_false] at hP
  rcases hP with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    dsimp [IntervalRow.active] at ha
    unfold Wn Hb
    split_ifs <;> omega

/-- Each active profile row improves the coefficient bound for every retained
common-node set. The finite arithmetic gain certificate is unconditional. -/
theorem intervalRow_minor_gle (P : IntervalRow) (hP : P∈intervalProfile)
    {r m p : ℕ} [Fact p.Prime] (hr : 1000≤r)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (s : Finset (Fin r)) :
    GLE p (intervalBase r m p-intervalRowDeficit P r m p) (commonMinorPoly p6Frame r m s) := by
  classical
  have hold : GLE p (intervalBase r m p) (commonMinorPoly p6Frame r m s) := by
    apply (commonMinorPoly_gle (p6Inst r m) p r m s).mono
    exact intervalBase_ge_trop _ _ _
  by_cases hg : P.active r p
  · rw [intervalRowDeficit,if_pos hg]
    by_cases hd : 0<p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m
    · have hb : p6WitnessLeft r p P.j≤p6WitnessRight r m p P.k := by omega
      have hpoles:=intervalProfile_poles P hP
      have hgeometry:=intervalProfile_geometry P hP
      have hwidth:=hgeometry.2 r m p
      have hpm : 2*m<p := by omega
      have h4:=hgeometry.1 r p hg
      have hp5 : 5≤p := by omega
      have hN : 3*(r+2*m)<p*p := by
        have H:=Nat.mul_self_le_mul_self (by omega : r≤4*p)
        nlinarith
      have H:=p6_interval_minor_gle hp5 hN hpm hpoles.1 hg.1 hpoles.2 hb s
      apply H.mono
      have hbase := intervalBase_ge_Wn P hP (m:=m) hg
      rw [intervalProfile_baseline P hP hg hpm] at hbase
      have hla : r≤p6WitnessLeft r p P.j := le_max_left _ _
      have hrb : p6WitnessRight r m p P.k≤r+2*m := min_le_left _ _
      omega
    · have he : p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m=0 := by omega
      simpa only [he,Nat.sub_zero] using hold
  · simpa only [intervalRowDeficit,if_neg hg,Nat.sub_zero] using hold
end CatalanFrames.P6Hybrid
