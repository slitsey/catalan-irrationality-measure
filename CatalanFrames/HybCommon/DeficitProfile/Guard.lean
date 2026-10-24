module
public import CatalanFrames.HybCommon.DeficitProfile.Covers
public import CatalanFrames.HybCommon.DeficitProfile.OldDisjoint
@[expose] public section
open Finset Filter Classical CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

def DeficitRow.oldSafe (P : DeficitRow) : Prop :=
  1/8+profileTrim≤P.lo ∧ P.hi≤9/10 ∧
  (if P.poleClass=1 then
    (P.hi≤5/12-profileTrim ∨ 4/9+profileTrim≤P.lo) ∧
    (P.hi≤5/8-profileTrim ∨ 4/5+profileTrim≤P.lo) ∧ P.hi≤9/10-profileTrim
   else
    (P.hi≤5/11-profileTrim ∨ 1/2+profileTrim≤P.lo) ∧
    P.hi≤5/7-profileTrim ∧ P.hi≤9/14-profileTrim)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma newProfile_oldSafe : ∀P∈newProfile,P.oldSafe := by
  norm_num [newProfile, rawProfile, DeficitRow.trim, profileTrim, DeficitRow.oldSafe]

lemma profile_active_good_of {o r p : ℕ} (ho : o=1 ∨ o=3) (hr : 1000000000≤r)
    (P : DeficitRow) (hsafe : P.oldSafe)
    (hc : (P.poleClass=1 ∨ P.poleClass=3) ∧ 0<P.lo ∧ P.lo<P.hi) (ha : profileRowActive o r p P) :
    profilePrimeGood o r p := by
  have hrR : (1000000000 : ℝ)≤r := by exact_mod_cast hr
  have hr0 : (0 : ℝ)≤r := by positivity
  have hlo : (0 : ℝ)≤P.lo := by exact_mod_cast hc.2.1.le
  have hhi : (0 : ℝ)≤P.hi := by
    have hh : (P.lo : ℝ)<P.hi := by exact_mod_cast hc.2.2
    linarith
  have hpL : (P.lo : ℝ)*r<p := (Nat.floor_lt (mul_nonneg hlo hr0)).mp ha.2.1
  have hpH : (p : ℝ)≤(P.hi : ℝ)*r := (Nat.le_floor_iff (mul_nonneg hhi hr0)).mp ha.2.2
  have upper : ∀q : ℚ,P.hi≤q-profileTrim → (p : ℝ)≤(q : ℝ)*r-r/10000000 := by
    intro q hq
    have hh:=(Rat.cast_le (K:=ℝ)).2 hq
    push_cast at hh
    norm_num [profileTrim] at hh
    have hm:=mul_le_mul_of_nonneg_right hh hr0
    nlinarith
  have lower : ∀q : ℚ,q+profileTrim≤P.lo → (q : ℝ)*r+r/10000000<(p : ℝ) := by
    intro q hq
    have hh:=(Rat.cast_le (K:=ℝ)).2 hq
    push_cast at hh
    norm_num [profileTrim] at hh
    have hm:=mul_le_mul_of_nonneg_right hh hr0
    nlinarith
  have hp8:=lower (1/8) hsafe.1
  have hh:=(Rat.cast_le (K:=ℝ)).2 hsafe.2.1
  norm_num at hh
  have hm:=mul_le_mul_of_nonneg_right hh hr0
  have hp9 : (p : ℝ)≤9*r/10 := by linarith
  have hm0:=Nat.mod_lt r (by omega : 0<8)
  have hm1:=Nat.mod_add_div r 8
  have hmL : (r : ℝ)/8-1≤(r/8 : ℕ) := by
    exact (profile_m_bounds r).1
  have hmU : ((r/8 : ℕ) : ℝ)≤(r : ℝ)/8 := (profile_m_bounds r).2
  have hp13 : 13≤p := by exact_mod_cast (show (13 : ℝ)≤p by linarith)
  have hpSq : 4*(r+2*(r/8)+1)<p^2 := by
    have hp0 : (0 : ℝ)≤p := by positivity
    have hx : (r : ℝ)<8*p := by linarith
    have hpbig : (10000000 : ℝ)≤p := by linarith
    have hh : (4*((r : ℝ)+2*((r/8 : ℕ) : ℝ)+1) : ℝ)<(p : ℝ)^2 := by nlinarith
    exact_mod_cast hh
  have hb : ¬WBG r p := by
    intro h
    have hx : (r : ℝ)<p := by exact_mod_cast h.2.1
    linarith
  have hclass:=congrArg ZMod.val ha.1
  have hsmall : o≤3 := by omega
  have hdefs : defG o r p=0 := by
    rcases hc.1 with htag|htag
    · have hs1 : (P.hi≤5/12-profileTrim ∨ 4/9+profileTrim≤P.lo) ∧ (P.hi≤5/8-profileTrim ∨ 4/5+profileTrim≤P.lo) ∧ P.hi≤9/10-profileTrim := by
        simpa [DeficitRow.oldSafe,htag] using hsafe.2.2
      have hsame : p%4=4-o := by
        simpa [profileClass,htag,ZMod.val_natCast,Nat.mod_eq_of_lt (show 4-o<4 by omega)] using hclass
      have hg : 3*p<r+2*(r/8) ∨ 4*r≤9*p := by
        rcases hs1.1 with h|h
        · have hx:=upper (5/12) h
          left; have hx' : (3*p : ℝ)<r+2*(r/8 : ℕ) := by nlinarith
          exact_mod_cast hx'
        · have hx:=lower (4/9) h
          right; have hx' : (4*r : ℝ)≤9*p := by nlinarith
          exact_mod_cast hx'
      have he : 8*p<5*r+8 ∨ 4*r<5*p+5 := by
        rcases hs1.2.1 with h|h
        · have hx:=upper (5/8) h
          left; have hx' : (8*p : ℝ)<5*r+8 := by nlinarith
          exact_mod_cast hx'
        · have hx:=lower (4/5) h
          right; have hx' : (4*r : ℝ)<5*p+5 := by nlinarith
          exact_mod_cast hx'
      have h5 : 5*p+o<4*(r+r/8) := by
        have hx:=upper (9/10) hs1.2.2
        have hoR : (o : ℝ)≤3 := by exact_mod_cast hsmall
        have hx' : (5*p+o : ℝ)<4*(r+(r/8 : ℕ)) := by nlinarith
        exact_mod_cast hx'
      have hn : p%4≠o := by omega
      have hl : ¬LowCleanO o r (r/8) p := by unfold LowCleanO; omega
      have h7old : ¬WC7G o r p := by unfold WC7G; omega
      have h5old : ¬WC5G o r p := by unfold WC5G; omega
      have h3 : ¬cleanE3G o r p := by unfold cleanE3G; omega
      have h1 : ¬cleanE1G o r p := by unfold cleanE1G; omega
      simp [defG,hl,h7old,h5old,hb,h3,h1]
    · have hne : P.poleClass≠1 := by omega
      have hs3 : (P.hi≤5/11-profileTrim ∨ 1/2+profileTrim≤P.lo) ∧ P.hi≤5/7-profileTrim ∧ P.hi≤9/14-profileTrim := by
        simpa [DeficitRow.oldSafe,hne] using hsafe.2.2
      have hsame : p%4=o := by
        simpa [profileClass,hne,ZMod.val_natCast,Nat.mod_eq_of_lt (show o<4 by omega)] using hclass
      have hg : 11*p+o<4*(r+2*(r/8)) ∨ r≤2*p := by
        rcases hs3.1 with h|h
        · have hx:=upper (5/11) h
          have hoR : (o : ℝ)≤3 := by exact_mod_cast hsmall
          left; have hx' : (11*p+o : ℝ)<4*(r+2*(r/8 : ℕ)) := by nlinarith
          exact_mod_cast hx'
        · have hx:=lower (1/2) h
          right; have hx' : (r : ℝ)≤2*p := by nlinarith
          exact_mod_cast hx'
      have he : 7*p<5*r+8 := by
        have hx:=upper (5/7) hs3.2.1
        have hx' : (7*p : ℝ)<5*r+8 := by nlinarith
        exact_mod_cast hx'
      have h7 : 7*p+o<4*(r+r/8) := by
        have hx:=upper (9/14) hs3.2.2
        have hoR : (o : ℝ)≤3 := by exact_mod_cast hsmall
        have hx' : (7*p+o : ℝ)<4*(r+(r/8 : ℕ)) := by nlinarith
        exact_mod_cast hx'
      have hn : p%4≠4-o := by omega
      have hl : ¬LowCleanO o r (r/8) p := by unfold LowCleanO; omega
      have h7old : ¬WC7G o r p := by unfold WC7G; omega
      have h5old : ¬WC5G o r p := by unfold WC5G; omega
      have h3 : ¬cleanE3G o r p := by unfold cleanE3G; omega
      have h1 : ¬cleanE1G o r p := by unfold cleanE1G; omega
      simp [defG,hl,h7old,h5old,hb,h3,h1]
  exact ⟨hp13,hpSq,hdefs⟩

lemma profile_active_good {o r p : ℕ} (ho : o=1 ∨ o=3) (hr : 1000000000≤r)
    (P : DeficitRow) (hP : P∈newProfile) (ha : profileRowActive o r p P) :
    profilePrimeGood o r p :=
  profile_active_good_of ho hr P (newProfile_oldSafe P hP)
    (let h := newProfile_cert P hP; ⟨h.1,h.2.1,h.2.2.1⟩) ha

theorem profileCover {o : ℕ} (ho : o=1 ∨ o=3) : ProfileCover o (profileDeficit o) 8 := by
  apply profileCover_of_good ho
  filter_upwards [eventually_ge_atTop 1000000000] with r hr
  intro P hP p hp ha
  exact profile_active_good ho hr P hP ha
#print axioms profileCover
end CatalanFrames.HybCommon
