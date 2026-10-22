module
public import CatalanFrames.HybCommon.DeficitProfile.Summation
public import CatalanFrames.HybCommon.DefAll
@[expose] public section
open Finset Filter Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

/-- Exact integer singular cut; valid pole residues make the division exact. -/
def profileCut (o p j : ℕ) : ℕ := (j*p + if j%4=0 then 0 else o)/4

def profileLeft (o r p : ℕ) (P : DeficitRow) : ℕ := max r (profileCut o p P.A4)
def profileRight (o r p : ℕ) (P : DeficitRow) : ℕ :=
  min (r+2*(r/8)) (min (profileCut o p P.B4) (if P.kind=0 then r+p else r+2*(r/8)))
def profileJLeft (o r p : ℕ) (P : DeficitRow) : ℕ :=
  if P.kind=0 then max (profileLeft o r p P) (r+2*(r/8)-p) else profileLeft o r p P

def profileRowDeficit (o r p : ℕ) (P : DeficitRow) : ℕ :=
  let n := profileRight o r p P-profileJLeft o r p P
  if P.kind=0 then r/8+n-(p+4) else n-(r/8+4)

noncomputable def profileRowActive (o r p : ℕ) (P : DeficitRow) : Prop :=
  (p : ZMod 4)=profileClass o P ∧ ⌊(P.lo : ℝ)*r⌋₊<p ∧ p≤⌊(P.hi : ℝ)*r⌋₊

noncomputable def profilePrimeGood (o r p : ℕ) : Prop :=
  13≤p ∧ 4*(r+2*(r/8)+1)<p^2 ∧ defG o r p=0

/-- The guard makes the new and banked deficits disjoint even at small parameters. -/
noncomputable def profileDeficitL (L : List DeficitRow) (o r p : ℕ) : ℕ :=
  if profilePrimeGood o r p then
    ∑P∈L.toFinset,if profileRowActive o r p P then profileRowDeficit o r p P else 0
  else 0

noncomputable def profileSupportL (L : List DeficitRow) (o r p : ℕ) : Prop :=
  ∃P∈L,profileRowActive o r p P

def profileBaseline (r p : ℕ) : ℕ :=
  if p<2*(r/8) then 2*r+3*(r/8)-p else 2*r+r/8

noncomputable def profileTL (L : List DeficitRow) {Fr : Frame} (o : ℕ) (I : HybInst Fr) (r p : ℕ) : ℕ :=
  if profileSupportL L o r p then max (TfunG o I r p) (profileBaseline r p) else TfunG o I r p

lemma profileT_ge (L : List DeficitRow) {Fr : Frame} (o : ℕ) (I : HybInst Fr) (r p : ℕ) :
    TfunG o I r p≤profileTL L o I r p := by
  unfold profileTL
  split_ifs
  · exact le_max_left _ _
  · rfl

lemma profileDeficit_disjoint (L : List DeficitRow) (o r p : ℕ) :
    defG o r p=0 ∨ profileDeficitL L o r p=0 := by
  by_cases h : defG o r p=0
  · exact Or.inl h
  · right
    simp [profileDeficitL, profilePrimeGood, h]

lemma profileDeficit_ge_row {L : List DeficitRow} (o r p : ℕ) (P : DeficitRow) (hP : P∈L)
    (hg : profilePrimeGood o r p) (ha : profileRowActive o r p P) :
    profileRowDeficit o r p P≤profileDeficitL L o r p := by
  rw [profileDeficitL, if_pos hg]
  have h := Finset.single_le_sum (fun Q hQ => Nat.zero_le (if profileRowActive o r p Q then profileRowDeficit o r p Q else 0))
    (List.mem_toFinset.mpr hP)
  simpa only [if_pos ha] using h

lemma profileDeficit_eq_row {L : List DeficitRow} (hD : RowData L) (o r p : ℕ) (ho : o=1 ∨ o=3)
    (P : DeficitRow)
    (hP : P∈L) (hg : profilePrimeGood o r p) (ha : profileRowActive o r p P) :
    profileDeficitL L o r p=profileRowDeficit o r p P := by
  rw [profileDeficitL, if_pos hg]
  rw [Finset.sum_eq_single P]
  · simp [ha]
  · intro Q hQ hQP
    by_cases hqa : profileRowActive o r p Q
    · have he := profile_window_unique hD ho r p hP (List.mem_toFinset.mp hQ)
        ha.2.1 ha.2.2 ha.1 hqa.2.1 hqa.2.2 hqa.1
      exact False.elim (hQP he.symm)
    · simp [hqa]
  · intro hn; exact False.elim (hn (List.mem_toFinset.mpr hP))

lemma profileDeficit_eq_zero_of_inactive (L : List DeficitRow) (o r p : ℕ)
    (h : ¬profileSupportL L o r p) : profileDeficitL L o r p=0 := by
  unfold profileDeficitL
  split_ifs
  · apply Finset.sum_eq_zero
    intro P hP
    have hn : ¬profileRowActive o r p P := fun hh => h ⟨P,List.mem_toFinset.mp hP,hh⟩
    simp [hn]
  · rfl

/-! The banked 61-row list: the old names are the `L = newProfile` instances. -/
noncomputable abbrev profileDeficit (o r p : ℕ) : ℕ := profileDeficitL newProfile o r p
noncomputable abbrev profileSupport (o r p : ℕ) : Prop := profileSupportL newProfile o r p
noncomputable abbrev profileT {Fr : Frame} (o : ℕ) (I : HybInst Fr) (r p : ℕ) : ℕ :=
  profileTL newProfile o I r p

end CatalanFrames.HybCommon
