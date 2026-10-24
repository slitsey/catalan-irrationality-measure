module
public import CatalanArchive.CatalanFrames.P6Hybrid.ProfileLocal
public import CatalanCore.Arith.Hybrid.PrimeDenominator
@[expose] public section
open Finset Polynomial Matrix CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open CatalanFrames.P6

noncomputable def intervalDeficit (r m p : ℕ) : ℕ :=
  intervalProfile.toFinset.sup (fun P=>intervalRowDeficit P r m p)

lemma intervalDeficit_le (r m p : ℕ) : intervalDeficit r m p ≤ intervalBase r m p := by
  classical
  apply Finset.sup_le
  intro P hP
  have hP:=List.mem_toFinset.mp hP
  by_cases ha : P.active r p
  · rw [intervalRowDeficit,if_pos ha]
    by_cases hd : 0<p6WitnessRight r m p P.k-p6WitnessLeft r p P.j-m
    · have hw:=(intervalProfile_geometry P hP).2 r m p
      have hp : 2*m<p := by omega
      have hbase := intervalBase_ge_Wn P hP (m:=m) ha
      rw [intervalProfile_baseline P hP ha hp] at hbase
      have hla : r≤p6WitnessLeft r p P.j:=le_max_left _ _
      have hrb : p6WitnessRight r m p P.k≤r+2*m:=min_le_left _ _
      omega
    · omega
  · simp only [intervalRowDeficit,if_neg ha];exact Nat.zero_le _

theorem intervalProfile_minor_gle {r m p : ℕ} [Fact p.Prime]
    (hr : 1000≤r) (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (s : Finset (Fin r)) :
    GLE p (intervalBase r m p-intervalDeficit r m p) (commonMinorPoly p6Frame r m s) := by
  classical
  have hne : intervalProfile.toFinset.Nonempty := by decide
  obtain ⟨P,hP,hmax⟩:=Finset.exists_mem_eq_sup intervalProfile.toFinset hne
    (fun P=>intervalRowDeficit P r m p)
  change GLE p (intervalBase r m p-intervalProfile.toFinset.sup _) _
  rw [hmax]
  exact intervalRow_minor_gle P (List.mem_toFinset.mp hP) hr hm1 hm2 s

noncomputable def intervalDenominator (r m : ℕ) : ℕ :=
  primeDenominator (Bnd (p6Inst r m) r m) (fun p=>intervalBase r m p-intervalDeficit r m p)

lemma intervalDenominator_pos (r m : ℕ) : 0 < intervalDenominator r m :=
  primeDenominator_pos _ _

theorem intervalDenominator_integral {r m : ℕ} (hr : 1000≤r)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (s : Finset (Fin r)) (i : ℕ) :
    ∃z : ℤ,(intervalDenominator r m:ℚ)*(commonMinorPoly p6Frame r m s).coeff i=z := by
  apply primeDenominator_integral
  intro p hp
  by_cases hb : p<Bnd (p6Inst r m) r m
  · simp only [if_pos hb]
    exact intervalProfile_minor_gle hr hm1 hm2 s
  · simp only [if_neg hb]
    have H:=commonMinorPoly_gle (p6Inst r m) p r m s
    rwa [tropExp_eq_zero (p6Inst r m) r m p hp.out (by omega)] at H

theorem log_intervalDenominator (r m : ℕ) :
    Real.log (intervalDenominator r m)=
      (∑p∈(range (Bnd (p6Inst r m) r m)).filter Nat.Prime,(intervalBase r m p:ℝ)*Real.log p)-
      ∑p∈(range (Bnd (p6Inst r m) r m)).filter Nat.Prime,(intervalDeficit r m p:ℝ)*Real.log p := by
  rw [intervalDenominator,log_primeDenominator,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Nat.cast_sub (intervalDeficit_le r m p)]
  ring
end CatalanFrames.P6Hybrid
