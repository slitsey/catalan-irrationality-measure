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
noncomputable def profileDeficit (o r p : ℕ) : ℕ :=
  if profilePrimeGood o r p then
    ∑P∈newProfile.toFinset,if profileRowActive o r p P then profileRowDeficit o r p P else 0
  else 0

noncomputable def profileSupport (o r p : ℕ) : Prop :=
  ∃P∈newProfile,profileRowActive o r p P

def profileBaseline (r p : ℕ) : ℕ :=
  if p<2*(r/8) then 2*r+3*(r/8)-p else 2*r+r/8

noncomputable def profileT {Fr : Frame} (o : ℕ) (I : HybInst Fr) (r p : ℕ) : ℕ :=
  if profileSupport o r p then max (TfunG o I r p) (profileBaseline r p) else TfunG o I r p

lemma profileT_ge {Fr : Frame} (o : ℕ) (I : HybInst Fr) (r p : ℕ) :
    TfunG o I r p≤profileT o I r p := by
  unfold profileT
  split_ifs
  · exact le_max_left _ _
  · rfl

lemma profileDeficit_disjoint (o r p : ℕ) : defG o r p=0 ∨ profileDeficit o r p=0 := by
  by_cases h : defG o r p=0
  · exact Or.inl h
  · right
    simp [profileDeficit, profilePrimeGood, h]

lemma profileDeficit_ge_row (o r p : ℕ) (P : DeficitRow) (hP : P∈newProfile)
    (hg : profilePrimeGood o r p) (ha : profileRowActive o r p P) :
    profileRowDeficit o r p P≤profileDeficit o r p := by
  rw [profileDeficit, if_pos hg]
  have h := Finset.single_le_sum (fun Q hQ => Nat.zero_le (if profileRowActive o r p Q then profileRowDeficit o r p Q else 0))
    (List.mem_toFinset.mpr hP)
  simpa only [if_pos ha] using h

lemma profileDeficit_eq_row (o r p : ℕ) (ho : o=1 ∨ o=3) (P : DeficitRow)
    (hP : P∈newProfile) (hg : profilePrimeGood o r p) (ha : profileRowActive o r p P) :
    profileDeficit o r p=profileRowDeficit o r p P := by
  rw [profileDeficit, if_pos hg]
  rw [Finset.sum_eq_single P]
  · simp [ha]
  · intro Q hQ hQP
    by_cases hqa : profileRowActive o r p Q
    · have he := profile_window_unique ho r p hP (List.mem_toFinset.mp hQ)
        ha.2.1 ha.2.2 ha.1 hqa.2.1 hqa.2.2 hqa.1
      exact False.elim (hQP he.symm)
    · simp [hqa]
  · intro hn; exact False.elim (hn (List.mem_toFinset.mpr hP))

lemma profileDeficit_eq_zero_of_inactive (o r p : ℕ)
    (h : ¬profileSupport o r p) : profileDeficit o r p=0 := by
  unfold profileDeficit
  split_ifs
  · apply Finset.sum_eq_zero
    intro P hP
    have hn : ¬profileRowActive o r p P := fun hh => h ⟨P,List.mem_toFinset.mp hP,hh⟩
    simp [hn]
  · rfl
end CatalanFrames.HybCommon
