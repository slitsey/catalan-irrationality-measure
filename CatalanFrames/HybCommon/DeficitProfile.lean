module
public import CatalanCore.Arith.Hybrid.AffineDeficit
@[expose] public section
open Finset Filter CatalanCore.Arith.Hybrid
namespace CatalanFrames.HybCommon

/-- Rational profile data. `poleClass` records the second-pole numerator modulo four. -/
structure DeficitRow where
  kind : ℕ
  poleClass : ℕ
  lo : ℚ
  hi : ℚ
  a : ℚ
  b : ℚ
  A4 : ℕ
  B4 : ℕ
  q4 : ℕ
  deriving DecidableEq

def DeficitRow.value (P : DeficitRow) (u : ℚ) : ℚ := P.a+P.b*u
def DeficitRow.area (P : DeficitRow) : ℚ :=
  P.a*(P.hi-P.lo)+P.b*(P.hi^2-P.lo^2)/2

def DeficitRow.polePair (P : DeficitRow) : Prop :=
  P.A4<P.B4 ∧ (P.A4%4=0 ∨ P.A4%4=P.poleClass) ∧
  (P.B4%4=0 ∨ P.B4%4=P.poleClass) ∧
  ∀j∈Finset.Ioo P.A4 P.B4, j%4≠0 ∧ j%4≠P.poleClass

instance (P : DeficitRow) : Decidable P.polePair := by unfold DeficitRow.polePair; infer_instance

def DeficitRow.cert (P : DeficitRow) : Prop :=
  (P.poleClass=1 ∨ P.poleClass=3) ∧ 0<P.lo ∧ P.lo<P.hi ∧
  (∀u∈[P.lo,P.hi], 0≤P.value u) ∧
  (if P.kind=0 then
    1/8≤P.lo ∧ P.hi≤1/4 ∧ P.polePair ∧
    ∀u∈[P.lo,P.hi],
      (∀aa∈[1,(P.A4:ℚ)*u/4],∀bb∈[5/4,(P.B4:ℚ)*u/4,1+u],
        aa≤bb ∧ P.value u≤1/8-u+bb-aa) ∧
      (∀bb∈[5/4,(P.B4:ℚ)*u/4,1+u],P.value u≤bb-9/8)
   else
    (P.kind=1 ∨ P.kind=2) ∧ 1/4≤P.lo ∧ P.hi≤9/10 ∧
    (if P.kind=1 then P.hi≤3/5 else 3/5≤P.lo) ∧ P.polePair ∧
    (P.q4%4=0 ∨ P.q4%4=P.poleClass) ∧
    ∀u∈[P.lo,P.hi],
      1<(P.q4:ℚ)*u/4 ∧ (P.q4:ℚ)*u/4<5/4 ∧
      ∀aa∈[1,(P.A4:ℚ)*u/4],∀bb∈[5/4,(P.B4:ℚ)*u/4],P.value u≤bb-aa-1/8
   )

instance (P : DeficitRow) : Decidable P.cert := by unfold DeficitRow.cert; infer_instance

def rawProfile : List DeficitRow := [
  ⟨0, 1, (1 / 8), (5 / 37), (-1 / 8), (1), 33, 36, 0⟩,
  ⟨0, 1, (5 / 37), (3 / 22), (9 / 8), (-33 / 4), 33, 36, 0⟩,
  ⟨0, 1, (3 / 22), (4 / 29), (-9 / 8), (33 / 4), 32, 33, 0⟩,
  ⟨0, 1, (4 / 29), (5 / 36), (-1 / 8), (1), 32, 33, 0⟩,
  ⟨0, 1, (5 / 36), (9 / 64), (9 / 8), (-8), 32, 33, 0⟩,
  ⟨0, 1, (9 / 64), (1 / 7), (-9 / 8), (8), 29, 32, 0⟩,
  ⟨0, 1, (1 / 7), (5 / 33), (-1 / 8), (1), 29, 32, 0⟩,
  ⟨0, 1, (5 / 33), (9 / 58), (9 / 8), (-29 / 4), 29, 32, 0⟩,
  ⟨0, 1, (9 / 58), (5 / 32), (-9 / 8), (29 / 4), 28, 29, 0⟩,
  ⟨0, 1, (5 / 32), (4 / 25), (1 / 8), (-3 / 4), 28, 29, 0⟩,
  ⟨0, 1, (4 / 25), (9 / 56), (9 / 8), (-7), 28, 29, 0⟩,
  ⟨0, 1, (9 / 56), (1 / 6), (-9 / 8), (7), 25, 28, 0⟩,
  ⟨0, 1, (1 / 6), (5 / 29), (-1 / 8), (1), 25, 28, 0⟩,
  ⟨0, 1, (5 / 29), (9 / 50), (9 / 8), (-25 / 4), 25, 28, 0⟩,
  ⟨0, 1, (3 / 16), (1 / 5), (-9 / 8), (6), 21, 24, 0⟩,
  ⟨0, 1, (1 / 5), (3 / 14), (9 / 8), (-21 / 4), 21, 24, 0⟩,
  ⟨0, 1, (9 / 40), (5 / 21), (-9 / 8), (5), 17, 20, 0⟩,
  ⟨0, 1, (5 / 21), (1 / 4), (1 / 8), (-1 / 4), 17, 20, 0⟩,
  ⟨0, 3, (1 / 8), (5 / 39), (-1 / 8), (1), 35, 36, 0⟩,
  ⟨0, 3, (5 / 39), (9 / 70), (9 / 8), (-35 / 4), 35, 36, 0⟩,
  ⟨0, 3, (9 / 70), (4 / 31), (-9 / 8), (35 / 4), 32, 35, 0⟩,
  ⟨0, 3, (4 / 31), (5 / 36), (-1 / 8), (1), 32, 35, 0⟩,
  ⟨0, 3, (5 / 36), (9 / 64), (9 / 8), (-8), 32, 35, 0⟩,
  ⟨0, 3, (9 / 64), (1 / 7), (-9 / 8), (8), 31, 32, 0⟩,
  ⟨0, 3, (1 / 7), (9 / 62), (9 / 8), (-31 / 4), 31, 32, 0⟩,
  ⟨0, 3, (9 / 62), (4 / 27), (-9 / 8), (31 / 4), 28, 31, 0⟩,
  ⟨0, 3, (4 / 27), (5 / 32), (-1 / 8), (1), 28, 31, 0⟩,
  ⟨0, 3, (5 / 32), (9 / 56), (9 / 8), (-7), 28, 31, 0⟩,
  ⟨0, 3, (9 / 56), (5 / 31), (-9 / 8), (7), 27, 28, 0⟩,
  ⟨0, 3, (5 / 31), (1 / 6), (1 / 8), (-3 / 4), 27, 28, 0⟩,
  ⟨0, 3, (1 / 6), (4 / 23), (-9 / 8), (27 / 4), 24, 27, 0⟩,
  ⟨0, 3, (4 / 23), (5 / 28), (-1 / 8), (1), 24, 27, 0⟩,
  ⟨0, 3, (5 / 28), (3 / 16), (9 / 8), (-6), 24, 27, 0⟩,
  ⟨0, 3, (9 / 46), (5 / 24), (-9 / 8), (23 / 4), 20, 23, 0⟩,
  ⟨0, 3, (5 / 24), (4 / 19), (1 / 8), (-1 / 4), 20, 23, 0⟩,
  ⟨0, 3, (4 / 19), (9 / 40), (9 / 8), (-5), 20, 23, 0⟩,
  ⟨0, 3, (9 / 38), (1 / 4), (-9 / 8), (19 / 4), 16, 19, 0⟩,
  ⟨1, 1, (1 / 4), (9 / 34), (9 / 8), (-17 / 4), 17, 20, 16⟩,
  ⟨1, 1, (9 / 32), (4 / 13), (-9 / 8), (4), 13, 16, 16⟩,
  ⟨1, 1, (4 / 13), (5 / 16), (-1 / 8), (3 / 4), 13, 16, 13⟩,
  ⟨1, 1, (5 / 16), (1 / 3), (9 / 8), (-13 / 4), 13, 16, 13⟩,
  ⟨1, 1, (1 / 3), (9 / 26), (9 / 8), (-13 / 4), 13, 16, 12⟩,
  ⟨1, 1, (3 / 8), (5 / 12), (-9 / 8), (3), 9, 12, 12⟩,
  ⟨1, 1, (4 / 9), (1 / 2), (9 / 8), (-9 / 4), 9, 12, 9⟩,
  ⟨1, 1, (1 / 2), (5 / 9), (-1 / 8), (1 / 4), 8, 9, 8⟩,
  ⟨1, 1, (5 / 9), (9 / 16), (9 / 8), (-2), 8, 9, 8⟩,
  ⟨1, 1, (9 / 16), (3 / 5), (-9 / 8), (2), 5, 8, 8⟩,
  ⟨1, 3, (1 / 4), (5 / 19), (-1 / 8), (3 / 4), 16, 19, 16⟩,
  ⟨1, 3, (5 / 19), (4 / 15), (9 / 8), (-4), 16, 19, 16⟩,
  ⟨1, 3, (4 / 15), (9 / 32), (9 / 8), (-4), 16, 19, 15⟩,
  ⟨1, 3, (3 / 10), (1 / 3), (-9 / 8), (15 / 4), 12, 15, 15⟩,
  ⟨1, 3, (1 / 3), (4 / 11), (9 / 8), (-3), 12, 15, 12⟩,
  ⟨1, 3, (4 / 11), (3 / 8), (9 / 8), (-3), 12, 15, 11⟩,
  ⟨1, 3, (9 / 22), (5 / 11), (-9 / 8), (11 / 4), 8, 11, 11⟩,
  ⟨1, 3, (1 / 2), (9 / 16), (9 / 8), (-2), 8, 11, 8⟩,
  ⟨1, 3, (9 / 16), (4 / 7), (-9 / 8), (2), 7, 8, 8⟩,
  ⟨1, 3, (4 / 7), (3 / 5), (-1 / 8), (1 / 4), 7, 8, 7⟩,
  ⟨2, 1, (4 / 5), (9 / 10), (9 / 8), (-5 / 4), 5, 8, 5⟩,
  ⟨2, 1, (3 / 5), (5 / 8), (-9 / 8), (2), 5, 8, 8⟩,
  ⟨2, 3, (5 / 8), (9 / 14), (9 / 8), (-7 / 4), 7, 8, 7⟩,
  ⟨2, 3, (3 / 5), (5 / 8), (-1 / 8), (1 / 4), 7, 8, 7⟩
  ]

def profileTrim : ℚ := 1/10000000
def DeficitRow.trim (P : DeficitRow) : DeficitRow :=
  {P with lo := P.lo+profileTrim, hi := P.hi-profileTrim}
def newProfile : List DeficitRow := rawProfile.map DeficitRow.trim

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem newProfile_cert : ∀P∈newProfile,P.cert := by
  norm_num [newProfile, rawProfile, DeficitRow.trim, profileTrim, DeficitRow.cert, DeficitRow.value, DeficitRow.polePair, Finset.mem_Ioo]
  repeat' constructor
  all_goals intros; omega

def DeficitRow.disjoint (P Q : DeficitRow) : Prop :=
  P.poleClass≠Q.poleClass ∨ P.hi≤Q.lo ∨ Q.hi≤P.lo

instance (P Q : DeficitRow) : Decidable (P.disjoint Q) := by unfold DeficitRow.disjoint; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem newProfile_pairwise : newProfile.Pairwise DeficitRow.disjoint := by
  norm_num (config := {maxSteps := 1000000}) [newProfile, rawProfile, DeficitRow.trim, profileTrim, List.pairwise_cons, DeficitRow.disjoint]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem newProfile_nodup : newProfile.Nodup := by
  norm_num (config := {maxSteps := 1000000}) [newProfile, rawProfile, DeficitRow.trim, profileTrim, List.nodup_cons, DeficitRow.mk.injEq]

def profileIntegralL (L : List DeficitRow) : ℚ := (L.map DeficitRow.area).sum/2

def profileIntegral : ℚ := profileIntegralL newProfile

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem profileIntegral_eq : profileIntegral=4420349242147094110541/213717258282528000000000 := by
  norm_num [profileIntegral, profileIntegralL, newProfile, rawProfile, DeficitRow.trim, profileTrim, DeficitRow.area]

def baseLambda : ℚ := 24729491161/6665218560-1/448-1/576-1/352

theorem profile_target_3474 : (76444/10000 : ℚ)/(39028/10000-baseLambda+profileIntegral)≤1737/50 := by
  rw [profileIntegral_eq]
  norm_num [baseLambda]

theorem profile_content_round : baseLambda-profileIntegral≤184137/50000 := by
  rw [profileIntegral_eq]
  norm_num [baseLambda]

theorem profile_rounded_target : (76444/10000 : ℚ)/(39028/10000-184137/50000)≤1737/50 := by norm_num

lemma newProfile_hi_le_one (P : DeficitRow) (hP : P∈newProfile) : P.hi≤1 := by
  have hh := (newProfile_cert P hP).2.2.2.2
  by_cases hk : P.kind=0
  · simp only [hk, if_pos] at hh
    exact hh.2.1.trans (by norm_num)
  · simp only [hk, if_false] at hh
    exact hh.2.2.1.trans (by norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem profile_lift_support : ∀P∈newProfile, (1/8 : ℚ)≤P.lo ∧
    (if P.kind=0 then P.hi≤1/4 else
      1/4≤P.lo ∧ P.hi≤(if P.poleClass=1 then 9/10 else 9/14)) := by
  norm_num [newProfile,rawProfile,DeficitRow.trim,profileTrim]

/-- **Row-list data.**  Everything the generic summation, family and weight machinery
(`Summation`, `Family`, `Weight`, `Log`, `SumFinal`, `Arithmetic`) needs from a list of rows.
The profile merge supplies it for the merged list; the banked list supplies it as `newProfile_rowData`. -/
structure RowData (L : List DeficitRow) : Prop where
  basic : ∀P∈L, (P.poleClass=1 ∨ P.poleClass=3) ∧ 0<P.lo ∧ P.lo<P.hi
  hi_le_one : ∀P∈L, P.hi≤1
  pairwise : L.Pairwise DeficitRow.disjoint
  nodup : L.Nodup
  lift : ∀P∈L, (1/8 : ℚ)≤P.lo ∧
    (if P.kind=0 then P.hi≤1/4 else
      1/4≤P.lo ∧ P.hi≤(if P.poleClass=1 then 9/10 else 9/14))

theorem newProfile_rowData : RowData newProfile where
  basic P hP := by
    have h := newProfile_cert P hP
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  hi_le_one := newProfile_hi_le_one
  pairwise := newProfile_pairwise
  nodup := newProfile_nodup
  lift := profile_lift_support

abbrev NewDeficit := ℕ→ℕ→ℕ
noncomputable def profileClass (o : ℕ) (P : DeficitRow) : ZMod 4 :=
  if P.poleClass=1 then ((4-o : ℕ) : ZMod 4) else (o : ZMod 4)
noncomputable def DeficitRow.toPiece (P : DeficitRow) (C : ℝ) : Piece :=
  ⟨P.lo,P.hi,P.a,P.b,C⟩

/-- The sole geometric input to the profile PNT theorem, for an arbitrary row list. -/
def ProfileCoverL (L : List DeficitRow) (o : ℕ) (δ : NewDeficit) (C : ℝ) : Prop :=
  ∀ᶠr : ℕ in atTop, ∀P∈L,
    LowerCovers (profileClass o P) (fun p => (δ r p : ℝ)) r (P.toPiece C)

abbrev ProfileCover (o : ℕ) (δ : NewDeficit) (C : ℝ) : Prop := ProfileCoverL newProfile o δ C

#print axioms newProfile_cert
#print axioms profileIntegral_eq
end CatalanFrames.HybCommon
