module
public import CatalanFrames.HybCommon.DeficitProfile.Range
public import CatalanFrames.HybCommon.DefBoth
public import CatalanCore.Arith.Hybrid.PoleIntervals
public import CatalanCore.Arith.Hybrid.ChainBorder
public import CatalanCore.Arith.Hybrid.ChainWitnessFull
@[expose] public section
open Finset Filter Classical Polynomial CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect
namespace CatalanFrames.HybCommon
open ChainClasses ChainModel

lemma profile_polePair {P : DeficitRow} (hP : P.cert) :
    PolePair P.poleClass P.A4 P.B4 := by
  have H:=hP.2.2.2.2
  by_cases hk : P.kind=0
  · simp only [hk,if_pos] at H
    exact H.2.2.1
  · simp only [hk,if_false] at H
    exact H.2.2.2.2.1

lemma profile_class_mod {o r p : ℕ} (ho : o=1 ∨ o=3) {P : DeficitRow}
    (hP : P.cert) (ha : profileRowActive o r p P) :
    p%4=if P.poleClass=1 then 4-o else o := by
  have h:=congrArg ZMod.val ha.1
  have ho0 : 0<o := by rcases ho with rfl|rfl <;> omega
  have ho4 : o<4 := by rcases ho with rfl|rfl <;> omega
  by_cases ht : P.poleClass=1
  · simpa only [profileClass,if_pos ht,ZMod.val_natCast,
      Nat.mod_eq_of_lt (by omega : 4-o<4)] using h
  · simpa only [profileClass,if_neg ht,ZMod.val_natCast,
      Nat.mod_eq_of_lt ho4] using h

lemma profileCut_poleCut (o p j : ℕ) : profileCut o p j=poleCut p o j := rfl

lemma profile_row_cut {o r p : ℕ} (ho : o=1 ∨ o=3) {P : DeficitRow}
    (hP : P.cert) (ha : profileRowActive o r p P) (hp : 5≤p)
    (hb : profileRight o r p P≤r+p) :
    ∀x y:ℕ,profileLeft o r p P≤x→x<profileRight o r p P→
      profileLeft o r p P≤y→y<profileRight o r p P→
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y) := by
  intro x y hax hxb hay hyb
  have ha0 : r≤profileLeft o r p P := le_max_left _ _
  have haA : poleCut p o P.A4≤profileLeft o r p P := le_max_right _ _
  have hbB : profileRight o r p P≤poleCut p o P.B4 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have H:=pole_pair_noCut ho hP.1 hp (profile_class_mod ho hP ha) (profile_polePair hP)
    (r:=r) (z:=min x y) (y:=max x y)
    (by omega) (by omega) (by omega) (by omega)
  simpa only [Nat.cast_min,Nat.cast_max] using H

lemma profile_row_cost {o r p : ℕ} (hr : 1000000000≤r) {P : DeficitRow}
    (hP : P∈newProfile) (ha : profileRowActive o r p P)
    (hpos : 0<profileRowDeficit o r p P) :
    profileRowDeficit o r p P≤profileBaseline r p ∧
    tropVal (witnessTable p r (r/8) (profileLeft o r p P) (profileRight o r p P))+
      2*r+4≤profileBaseline r p-profileRowDeficit o r p P := by
  have Hrange:=profile_kind_range hr P hP ha
  have hla : r≤profileLeft o r p P := le_max_left _ _
  have hrb : profileRight o r p P≤r+2*(r/8) := min_le_left _ _
  by_cases hk : P.kind=0
  · have hp:=Hrange.2.1 hk
    have hbp : profileRight o r p P≤r+p := by
      unfold profileRight
      simp only [hk,if_pos]
      exact (min_le_right _ _).trans (min_le_right _ _)
    have hd : 0<r/8+(profileRight o r p P-max (profileLeft o r p P) (r+2*(r/8)-p))-(p+4) := by
      simpa only [profileRowDeficit,profileJLeft,hk,if_pos] using hpos
    have hj : max (profileLeft o r p P) (r+2*(r/8)-p)≤profileRight o r p P := by omega
    have hab : profileLeft o r p P≤profileRight o r p P := by omega
    have HW:=witness_assignment_low hla hab hrb hbp hj
    have hn : profileRight o r p P-max (profileLeft o r p P) (r+2*(r/8)-p)≤2*(r/8) := by omega
    simp only [profileBaseline,if_pos hp,profileRowDeficit,profileJLeft,hk,if_pos]
    omega
  · have hp:=Hrange.2.2 hk
    have hd : 0<(profileRight o r p P-profileLeft o r p P)-(r/8+4) := by
      simpa only [profileRowDeficit,profileJLeft,hk,if_false] using hpos
    have hab : profileLeft o r p P≤profileRight o r p P := by omega
    have HW:=witness_assignment_high hla hab hrb hp
    have hn : profileRight o r p P-profileLeft o r p P≤2*(r/8) := by omega
    simp only [profileBaseline,if_neg (by omega : ¬p<2*(r/8)),profileRowDeficit,profileJLeft,hk,if_false]
    omega
/-- A positive active row clears both family members within its exact profile budget. -/
theorem profile_row_both_gle {Fr : Frame} {o r p : ℕ} [Fact p.Prime]
    (hL : LamData Fr o) (ho : o=1 ∨ o=3) (hr : 1000000000≤r) {P : DeficitRow}
    (hP : P∈newProfile) (ha : profileRowActive o r p P)
    (hg : profilePrimeGood o r p) (hpos : 0<profileRowDeficit o r p P) :
    GLE p (profileBaseline r p-profileRowDeficit o r p P) (Fr.fullPoly r (r/8)) ∧
    GLE p (profileBaseline r p-profileRowDeficit o r p P) ((afterTop r (r/8)).fullPolyG Fr) := by
  have hp : 5≤p := by have:=hg.1;omega
  have hN : 4*(r+2*(r/8)+1)<p*p := by simpa only [pow_two] using hg.2.1
  have Hcost:=profile_row_cost hr hP ha hpos
  have Hrange:=profile_kind_range hr P hP ha
  have hbp : profileRight o r p P≤r+p := by
    by_cases hk : P.kind=0
    · unfold profileRight
      simp only [hk,if_pos]
      exact (min_le_right _ _).trans (min_le_right _ _)
    · have H:=Hrange.2.2 hk
      have Hb : profileRight o r p P≤r+2*(r/8) := min_le_left _ _
      omega
  have hcut:=profile_row_cut ho (newProfile_cert P hP) ha hp hbp
  let k : ℕ := (((4:ZMod p)⁻¹)*(o:ZMod p)).val
  have hk : (4:ZMod p)*k=(o:ZMod p) := by
    dsimp only [k]
    rw [ZMod.natCast_zmod_val,←mul_assoc,mul_inv_cancel₀ (four_ne_zmod p hp),one_mul]
  have H1:=witness_fullPoly_gle hL hp (by omega : 4*(r+2*(r/8))<p*p) hk hcut
  have H2:=top_det_weighted hL hp hN hk
    (witnessTable p r (r/8) (profileLeft o r p P) (profileRight o r p P))
    (fun i j=>witnessWeight_le_two _ _ _ _ _)
    (witness_zero_condition hcut) witness_one_condition
  exact ⟨H1.mono (by omega),H2.mono (by omega)⟩

/-- **Row-local interface.**  What an active row of positive deficit must deliver at one prime:
its deficit is within the baseline and both family members clear the baseline minus the deficit
(the second member with the production border slack `topC`).  For the banked kinds 0, 1, 2 this is
`profile_row_cost` and `profile_row_both_gle`; the two-level (kind 3) rows supply it from
`twoLevel_fullPoly_gle` / `twoLevel_top_gle`. -/
def ProfileRowLocal {Fr : Frame} (I : HybInst Fr) (o : ℕ) (L : List DeficitRow) : Prop :=
  ∀ (r p : ℕ) [Fact p.Prime] [I.DiagOK r (r/8)], 1000000000≤r → ∀P∈L,
    profileRowActive o r p P → profilePrimeGood o r p → 0<profileRowDeficit o r p P →
    profileRowDeficit o r p P≤profileBaseline r p ∧
    GLE p (profileBaseline r p-profileRowDeficit o r p P) (Fr.fullPoly r (r/8)) ∧
    GLE p (profileBaseline r p-profileRowDeficit o r p P+topC I r (r/8) p)
      ((afterTop r (r/8)).fullPolyG Fr)

/-- The banked rows satisfy the row-local interface. -/
theorem profileRowLocal_new {Fr : Frame} (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o)
    (ho : o=1 ∨ o=3) : ProfileRowLocal I o newProfile := by
  intro r p _ _ hr P hP ha hg hpos
  have Hcost:=profile_row_cost hr hP ha hpos
  have H:=profile_row_both_gle hL ho hr hP ha hg hpos
  exact ⟨Hcost.1,H.1,H.2.mono (by omega)⟩

/-- Local family bookkeeping uses the profile guard and unique active row. -/
theorem profile_local {Fr : Frame} (I : HybInst Fr) {L : List DeficitRow} (hD : RowData L)
    {o r p : ℕ}
    [Fact p.Prime] [I.DiagOK r (r/8)] (hrow : ProfileRowLocal I o L)
    (ho : o=1 ∨ o=3) (hr : 1000000000≤r) :
    profileDeficitL L o r p≤profileTL L o I r p ∧
    GLE p (profileTL L o I r p-profileDeficitL L o r p) (Fr.fullPoly r (r/8)) ∧
    GLE p (profileTL L o I r p-profileDeficitL L o r p+topC I r (r/8) p)
      ((afterTop r (r/8)).fullPolyG Fr) := by
  have hT : tropExp I r (r/8) p≤profileTL L o I r p :=
    (TfunG_ge_trop (o:=o) p).trans (profileT_ge L o I r p)
  by_cases hpos : 0<profileDeficitL L o r p
  · have hg : profilePrimeGood o r p := by
      by_contra hn
      simp only [profileDeficitL,if_neg hn] at hpos
      omega
    have hs : profileSupportL L o r p := by
      by_contra hn
      have H:=profileDeficit_eq_zero_of_inactive L o r p hn
      omega
    obtain ⟨P,hP,ha⟩:=hs
    have he:=profileDeficit_eq_row hD o r p ho P hP hg ha
    have hrowpos : 0<profileRowDeficit o r p P := by omega
    have H:=hrow r p hr P hP ha hg hrowpos
    have hbase : profileBaseline r p≤profileTL L o I r p := by
      unfold profileTL
      rw [if_pos ⟨P,hP,ha⟩]
      exact le_max_right _ _
    exact ⟨by omega,H.2.1.mono (by omega),H.2.2.mono (by omega)⟩
  · have he : profileDeficitL L o r p=0 := by omega
    rw [he,Nat.sub_zero]
    exact ⟨Nat.zero_le _,(fullPoly_gle I p r (r/8)).mono hT,
      (fullTop_gle I r (r/8) p).mono (by omega)⟩

/-- Concrete two-member deficit family for a certified row list. -/
theorem defBoth_profileL {Fr : Frame} (I : HybInst Fr) {L : List DeficitRow} (hD : RowData L)
    {o r : ℕ}
    [I.DiagOK r (r/8)] (hrow : ProfileRowLocal I o L) (ho : o=1 ∨ o=3)
    (hr : 1000000000≤r) :
    DefBothG I r (profileTL L o I r) (profileDeficitL L o r) := by
  constructor
  · intro p hp hb
    letI : Fact p.Prime:=⟨hp⟩
    have H:=profile_local (p:=p) I hD hrow ho hr
    exact ⟨H.1,fun [Fact p.Prime]=>H.2.1⟩
  · intro p hp hb _
    exact (profile_local (p:=p) I hD hrow ho hr).2.2

theorem profile_defBothL {Fr : Frame} (I : HybInst Fr) {L : List DeficitRow} (hD : RowData L)
    {o : ℕ}
    [∀r,I.DiagOK r (r/8)] (hrow : ProfileRowLocal I o L) (ho : o=1 ∨ o=3) :
    ∀ᶠr : ℕ in atTop, DefBothG I r (profileTL L o I r) (profileDeficitL L o r) := by
  filter_upwards [eventually_ge_atTop 1000000000] with r hr
  exact defBoth_profileL I hD hrow ho hr

theorem profile_defBoth {Fr : Frame} (I : HybInst Fr) {o : ℕ}
    [∀r,I.DiagOK r (r/8)] (hL : LamData Fr o) (ho : o=1 ∨ o=3) :
    ∀ᶠr : ℕ in atTop, DefBothG I r (profileT o I r) (profileDeficit o r) :=
  profile_defBothL I newProfile_rowData (profileRowLocal_new I hL ho) ho

#print axioms profile_defBothL
#print axioms profile_defBoth
end CatalanFrames.HybCommon
