module

public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Value

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Actual unpivoted P123 weights are priced by the arbitrary-knownzero dual.
The U-zero requirement is on common nodes only; border V-zero windows may have U!=0. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Rect
open CatalanCore.Uniform.Content.Shape CatalanCore.Arith.Hybrid
open CatalanFrames.P6Hybrid (isRowP isColP)
open Classical

noncomputable def knownPlainWeight (p : ℕ) (Fr : Frame) (A B : ℕ) : ℕ :=
  if ((A:ℤ)≡B [ZMOD p]) then w0 p Fr A B else if Vp p Fr A=Vp p Fr B then 0 else 1

theorem knownPlainWeight_le_two (p : ℕ) (Fr : Frame) (A B : ℕ) :
    knownPlainWeight p Fr A B≤2 := by
  unfold knownPlainWeight w0
  split_ifs <;> omega

theorem knownPlainWeight_le_one (p : ℕ) (Fr : Frame) (A B : ℕ)
    (hc : ¬(p:ℤ)∣(A:ℤ)-B) : knownPlainWeight p Fr A B≤1 := by
  have hmod : ¬((A:ℤ)≡B [ZMOD p]) := fun h => hc h.symm.dvd
  simp only [knownPlainWeight,if_neg hmod]
  split_ifs <;> omega

theorem knownPlainWeight_dual (Fr : Frame) (r m p : ℕ) [Fact p.Prime]
    (hN : r+2*m≤2*p) (K : Finset ℕ) (hKp : ∀ t∈K,t<p)
    (hKV : ∀ t,t<r+2*m → t∈K → Vp p Fr t=0)
    (hKU : ∀ t,t<r → t∈K → Up p Fr t=0)
    (A B : ℕ) (hA : A<r+2*m) (hB : B<r+2*m)
    (hAr : isRowP r m A) (hBc : isColP r m B) :
    (knownPlainWeight p Fr A B : ℚ)≤(znU r m p K A : ℚ)+(znV r m p K B : ℚ) := by
  apply knownZero_dual_feasible (Fact.out : p.Prime).pos hN hKp (knownPlainWeight p Fr)
    (fun A B _ _ _ _ => knownPlainWeight_le_two p Fr A B)
    (fun A B _ _ _ _ _ hc => knownPlainWeight_le_one p Fr A B hc) ?_ ?_ A B hA hB hAr hBc
  · intro A hA hAr hAc hAK
    have hcommon : A<r := by
      rcases hAr with h | h
      · exact h
      · rcases hAc with h' | h'
        · exact h'
        · omega
    have hU := hKU A hcommon hAK
    simp [knownPlainWeight,w0,hU]
  · intro A B hA hB _ _ _ hc hAK hBK
    have hmod : ¬((A:ℤ)≡B [ZMOD p]) := fun h => hc h.symm.dvd
    simp [knownPlainWeight,hmod,hKV A hA hAK,hKV B hB hBK]

theorem knownZero_hf_weight (Fr : Frame) (r m p : ℕ) (x y : Fin r ⊕ Fin m) :
    Wd p Fr (hfData r m (fun _=>none) (fun _=>none) (fun _=>0) (fun _=>0))
      (hfVr r m p Fr (fun i=>Vp p Fr (r+2*i.val)))
      (hfVr r m p Fr (fun i=>Vp p Fr (r+2*i.val+1))) x y =
      knownPlainWeight p Fr (Frame.hybRow r m x) (Frame.hybCol r m y) := by
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Wd,hfData,hfVr,GData.aR,GData.aC,Frame.hybRow,Frame.hybCol,knownPlainWeight] <;> rfl

theorem knownZero_hf_feasible (Fr : Frame) (r m p : ℕ) [Fact p.Prime]
    (hN : r+2*m≤2*p) (K : Finset ℕ) (hKp : ∀ t∈K,t<p)
    (hKV : ∀ t,t<r+2*m → t∈K → Vp p Fr t=0)
    (hKU : ∀ t,t<r → t∈K → Up p Fr t=0)
    (x y : Fin r ⊕ Fin m) :
    ((Wd p Fr (hfData r m (fun _=>none) (fun _=>none) (fun _=>0) (fun _=>0))
      (hfVr r m p Fr (fun i=>Vp p Fr (r+2*i.val)))
      (hfVr r m p Fr (fun i=>Vp p Fr (r+2*i.val+1))) x y : ℕ) : ℚ) ≤
      knownRho r m p K x+knownGamma r m p K y := by
  rw [knownZero_hf_weight]
  apply knownPlainWeight_dual Fr r m p hN K hKp hKV hKU _ _
    (Frame_hybRow_lt r m x) (Frame_hybCol_lt r m y)
  · rcases x with x | x
    · left;exact x.isLt
    · right;have h:=x.isLt;simp [Frame.hybRow] <;> omega
  · rcases y with y | y
    · left;exact y.isLt
    · right;have h:=y.isLt;simp [Frame.hybCol] <;> omega

theorem knownZero_member_gle (Fr : Frame) (r m p : ℕ) [Fact p.Prime]
    (hP : HybPiv r m p Fr (fun _ => none) (fun _ => none)
      (fun _ => 0) (fun _ => 0)
      (fun i => Vp p Fr (r+2*i.val)) (fun i => Vp p Fr (r+2*i.val+1)))
    (hN : r+2*m≤2*p) (K : Finset ℕ)
    (hKp : ∀ t∈K,t<p)
    (hKV : ∀ t,t<r+2*m → t∈K → Vp p Fr t=0)
    (hKU : ∀ t,t<r → t∈K → Up p Fr t=0)
    (S : Finset (Fin r)) :
    GLE p (zPrice r m p K+2*(r-S.card)) (commonMinorPoly Fr r m S) := by
  apply member_gle hP S (knownRho r m p K) (knownGamma r m p K)
    (fun _=>Nat.cast_nonneg _) (fun _=>Nat.cast_nonneg _)
    (knownZero_hf_feasible Fr r m p hN K hKp hKV hKU)
  simpa only [known_dual_value,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
    (le_refl ((zPrice r m p K:ℚ)+2*((r-S.card:ℕ):ℚ)))

theorem knownZero_alt_member_gle (g : ℚ) (hg : 0<g) (Fr : Frame) (depth r m p : ℕ) [Fact p.Prime]
    (hm : m=(altGeom g hg).borderSize r) (hr : r%2=0)
    (hP : HybPiv r m p Fr (fun _ => none) (fun _ => none)
      (fun _ => 0) (fun _ => 0)
      (fun i => Vp p Fr (r+2*i.val)) (fun i => Vp p Fr (r+2*i.val+1)))
    (hN : r+2*m≤2*p) (K : Finset ℕ) (hKp : ∀ t∈K,t<p)
    (hKV : ∀ t,t<r+2*m → t∈K → Vp p Fr t=0)
    (hKU : ∀ t,t<r → t∈K → Up p Fr t=0)
    (S : Finset ((altGeom g hg).geometry r).C) :
    GLE p (zPrice r m p K+2*(r-S.card)) (((altGeom g hg).family Fr depth).Q ⟨r,S⟩) := by
  apply alt_member_gle_of_dual g hg Fr depth r m p hm hr S
    (fun _=>none) (fun _=>none) (fun _=>0) (fun _=>0)
    (fun i=>Vp p Fr (r+2*i.val)) (fun i=>Vp p Fr (r+2*i.val+1)) hP
    (knownRho r m p K) (knownGamma r m p K)
    (fun _=>Nat.cast_nonneg _) (fun _=>Nat.cast_nonneg _)
    (knownZero_hf_feasible Fr r m p hN K hKp hKV hKU)
  simpa only [known_dual_value] using (le_refl (zPrice r m p K:ℚ))

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.knownZero_hf_feasible
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.knownZero_member_gle
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.knownZero_alt_member_gle
