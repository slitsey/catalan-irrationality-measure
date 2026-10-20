module
public import CatalanFrames.HybCommon.DeficitProfile.Rounding
@[expose] public section
namespace CatalanFrames.HybCommon
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma newProfile_twoM_range : ∀P∈newProfile,
    (P.kind=0 → P.hi≤1/4-profileTrim) ∧
    (P.kind≠0 → 1/4+profileTrim≤P.lo) := by
  norm_num [newProfile,rawProfile,DeficitRow.trim,profileTrim]
lemma profile_kind_range {o r p : ℕ} (hr : 1000000000≤r)
    (P : DeficitRow) (hP : P∈newProfile) (ha : profileRowActive o r p P) :
    r/8≤p ∧ (P.kind=0 → p<2*(r/8)) ∧ (P.kind≠0 → 2*(r/8)<p) := by
  have hc:=newProfile_cert P hP
  have hs : (0 : ℝ)≤P.lo := by exact_mod_cast hc.2.1.le
  have ht : (0 : ℝ)≤P.hi := by
    have hx : (P.lo : ℝ)<P.hi := by exact_mod_cast hc.2.2.1
    linarith
  have hpL : (P.lo : ℝ)*r<p := (Nat.floor_lt (mul_nonneg hs (Nat.cast_nonneg r))).mp ha.2.1
  have hpH : (p : ℝ)≤(P.hi : ℝ)*r := (Nat.le_floor_iff (mul_nonneg ht (Nat.cast_nonneg r))).mp ha.2.2
  have hrR : (1000000000 : ℝ)≤r := by exact_mod_cast hr
  obtain ⟨hmL,hmU⟩:=profile_m_bounds r
  have hlope : (1/8 : ℝ)≤P.lo := by
    by_cases hk : P.kind=0
    · have hx:=hc.2.2.2.2
      rw [if_pos hk] at hx
      have hy:=(Rat.cast_le (K:=ℝ)).2 hx.1
      norm_num at hy
      exact hy
    · have hx:=(Rat.cast_le (K:=ℝ)).2 ((newProfile_twoM_range P hP).2 hk)
      norm_num [profileTrim] at hx
      linarith
  have hml : r/8≤p := by
    have hm:=mul_le_mul_of_nonneg_right hlope (Nat.cast_nonneg r : (0 : ℝ)≤r)
    have hh : ((r/8 : ℕ) : ℝ)≤p := by nlinarith
    exact_mod_cast hh
  refine ⟨hml,?_,?_⟩
  · intro hk
    have hx:=(Rat.cast_le (K:=ℝ)).2 ((newProfile_twoM_range P hP).1 hk)
    norm_num [profileTrim] at hx
    have hm:=mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg r : (0 : ℝ)≤r)
    have hh : (p : ℝ)<2*(r/8 : ℕ) := by nlinarith
    exact_mod_cast hh
  · intro hk
    have hx:=(Rat.cast_le (K:=ℝ)).2 ((newProfile_twoM_range P hP).2 hk)
    norm_num [profileTrim] at hx
    have hm:=mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg r : (0 : ℝ)≤r)
    have hh : (2*((r/8 : ℕ) : ℝ) : ℝ)<p := by nlinarith
    exact_mod_cast hh
end CatalanFrames.HybCommon
