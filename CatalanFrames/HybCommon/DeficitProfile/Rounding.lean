module
public import CatalanFrames.HybCommon.DeficitProfile.Witness
public import CatalanFrames.HybCommon.DeficitProfile.Family
public import CatalanCore.Arith.Hybrid.IntervalRounding
@[expose] public section
open Finset Classical CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

lemma profileCut_bounds (o p j : ℕ) (ho : o≤3) :
    (j : ℝ)*p/4-1≤profileCut o p j ∧ (profileCut o p j : ℝ)≤(j : ℝ)*p/4+1 := by
  have he : (if j%4=0 then 0 else o)≤3 := by split_ifs <;> omega
  have hlo : j*p<4*profileCut o p j+4 := by unfold profileCut; omega
  have hhi : 4*profileCut o p j≤j*p+3 := by unfold profileCut; omega
  have hlR : (j : ℝ)*p<4*(profileCut o p j : ℝ)+4 := by exact_mod_cast hlo
  have hhR : 4*(profileCut o p j : ℝ)≤(j : ℝ)*p+3 := by exact_mod_cast hhi
  constructor <;> linarith

lemma profile_m_bounds (r : ℕ) : (r : ℝ)/8-1≤((r/8 : ℕ) : ℝ) ∧ ((r/8 : ℕ) : ℝ)≤(r : ℝ)/8 := by
  have h0 : 8*(r/8)≤r := by omega
  have h1 : r<8*(r/8)+8 := by omega
  have h0R : 8*((r/8 : ℕ) : ℝ)≤r := by exact_mod_cast h0
  have h1R : (r : ℝ)<8*((r/8 : ℕ) : ℝ)+8 := by exact_mod_cast h1
  constructor <;> linarith

lemma profileLeft_upper (o r p : ℕ) (P : DeficitRow) (ho : o≤3) :
    (profileLeft o r p P : ℝ)≤max (r : ℝ) ((P.A4 : ℝ)*p/4)+1 := by
  rw [profileLeft, Nat.cast_max]
  apply max_le
  · have h:=le_max_left (r : ℝ) ((P.A4 : ℝ)*p/4); linarith
  · have h:=(profileCut_bounds o p P.A4 ho).2
    have hh:=le_max_right (r : ℝ) ((P.A4 : ℝ)*p/4)
    linarith

lemma profileRight_lower_low (o r p : ℕ) (P : DeficitRow) (ho : o≤3) (hk : P.kind=0) :
    min (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p))-2≤profileRight o r p P := by
  have hm:=(profile_m_bounds r).1
  have hc:=(profileCut_bounds o p P.B4 ho).1
  simp only [profileRight,hk,if_pos,Nat.cast_min,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  apply le_min
  · have h:=min_le_left (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p)); linarith
  · apply le_min
    · have h:=(min_le_right (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p))).trans (min_le_left _ _)
      linarith
    · have h:=(min_le_right (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p))).trans (min_le_right _ _)
      linarith

lemma profileRight_lower_nc (o r p : ℕ) (P : DeficitRow) (ho : o≤3) (hk : P.kind≠0) :
    min (5*(r : ℝ)/4) ((P.B4 : ℝ)*p/4)-2≤profileRight o r p P := by
  have hm:=(profile_m_bounds r).1
  have hc:=(profileCut_bounds o p P.B4 ho).1
  simp only [profileRight,hk,if_false,Nat.cast_min,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  apply le_min
  · have h:=min_le_left (5*(r : ℝ)/4) ((P.B4 : ℝ)*p/4); linarith
  · apply le_min
    · have h:=min_le_right (5*(r : ℝ)/4) ((P.B4 : ℝ)*p/4); linarith
    · have h:=min_le_left (5*(r : ℝ)/4) ((P.B4 : ℝ)*p/4); linarith

lemma profileRowDeficit_low_rounding (o r p : ℕ) (P : DeficitRow)
    (ho : o≤3) (hp : p≤r) (hk : P.kind=0) :
    min ((r : ℝ)/8-p+min (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p))-
      max (r : ℝ) ((P.A4 : ℝ)*p/4))
      (min (5*(r : ℝ)/4) (min ((P.B4 : ℝ)*p/4) ((r : ℝ)+p))-9*(r : ℝ)/8)-8≤
      (profileRowDeficit o r p P : ℝ) := by
  have h:=interval_low_rounding r p (r/8) (profileLeft o r p P) (profileRight o r p P)
    ((P.A4 : ℝ)*p/4) ((P.B4 : ℝ)*p/4) hp (profile_m_bounds r).1 (profile_m_bounds r).2
    (profileLeft_upper o r p P ho) (profileRight_lower_low o r p P ho hk)
  simpa only [profileRowDeficit,profileJLeft,hk,if_pos] using h

lemma profileRowDeficit_nc_rounding (o r p : ℕ) (P : DeficitRow)
    (ho : o≤3) (hk : P.kind≠0) :
    min (5*(r : ℝ)/4) ((P.B4 : ℝ)*p/4)-max (r : ℝ) ((P.A4 : ℝ)*p/4)-(r : ℝ)/8-7≤
      (profileRowDeficit o r p P : ℝ) := by
  have h:=interval_nc_rounding r (r/8) (profileLeft o r p P) (profileRight o r p P)
    ((P.A4 : ℝ)*p/4) ((P.B4 : ℝ)*p/4) (profile_m_bounds r).2
    (profileLeft_upper o r p P ho) (profileRight_lower_nc o r p P ho hk)
  simpa only [profileRowDeficit,profileJLeft,hk,if_false] using h
end CatalanFrames.HybCommon
