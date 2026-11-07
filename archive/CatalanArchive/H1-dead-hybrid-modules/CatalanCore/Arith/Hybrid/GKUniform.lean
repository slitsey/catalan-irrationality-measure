module
public import CatalanCore.Arith.Hybrid.GKConditions
public import CatalanCore.Arith.Hybrid.ChainWitnessFull
public import CatalanCore.Arith.Hybrid.PoleIntervals
@[expose] public section
open Polynomial Matrix Finset CatalanCore
namespace CatalanCore.Arith.Hybrid
open ChainClasses ChainModel
variable {o p r m k : ℕ} [Fact p.Prime] {Fr : Frame}
lemma gk_offset (hp : 13≤p) (ho : 0<o ∧ o≤3) (hj : 4∣p+o ∨ 4∣3*p+o) : o=1 ∨ o=3 := by
  obtain ⟨a,ha⟩ := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  rcases hj with ⟨j,hj⟩|⟨j,hj⟩ <;> omega
lemma GKS3.noCut (S : GKS3 o p r m k) :
    ∀ x y:ℕ,r≤x → x<r+2*m → r≤y → y<r+2*m →
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y) := by
  have ho:=gk_offset S.p13 ⟨S.hk.2.1,S.hk.2.2⟩ (Or.inl ⟨k,S.hk.1.symm⟩)
  have hm : p%4=4-o := by have:=S.hk.1; rcases ho with rfl|rfl <;> omega
  have hke:=S.hk.1
  have hA : poleCut p o 9=2*p+k := by simp [poleCut,poleOffset];omega
  have hB : poleCut p o 12=3*p := by simp [poleCut,poleOffset];omega
  intro x y hx hx' hy hy'
  have H:=pole_pair_noCut (p:=p) (o:=o) (c:=1) (A:=9) (B:=12) (r:=r) (z:=min x y) (y:=max x y) ho (Or.inl rfl)
    (by have:=S.p13;omega) (by simpa using hm) (by unfold PolePair;decide : PolePair 1 9 12)
    (by rw [hA];have:=S.hr;omega) (by rw [hB];have:=S.hN;omega)
    (by omega) (by have:=S.hr;have:=S.hN;have:=S.k0;omega)
  simpa only [Nat.cast_min,Nat.cast_max] using H
lemma GK1.GKS1.noCut (S : GK1.GKS1 o p r m k) :
    ∀ x y:ℕ,r≤x → x<r+2*m → r≤y → y<r+2*m →
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y) := by
  have ho:=gk_offset S.p13 ⟨S.hk.2.1,S.hk.2.2⟩ (Or.inr ⟨k,S.hk.1.symm⟩)
  have hm : p%4=o := by have:=S.hk.1; rcases ho with rfl|rfl <;> omega
  have hke:=S.hk.1
  have hA : poleCut p o 8=2*p := by simp [poleCut,poleOffset];omega
  have hB : poleCut p o 11=2*p+k := by simp [poleCut,poleOffset];omega
  intro x y hx hx' hy hy'
  have H:=pole_pair_noCut (p:=p) (o:=o) (c:=3) (A:=8) (B:=11) (r:=r) (z:=min x y) (y:=max x y) ho (Or.inr rfl)
    (by have:=S.p13;omega) (by simpa using hm) (by unfold PolePair;decide : PolePair 3 8 11)
    (by rw [hA];have:=S.hr;omega) (by rw [hB];have:=S.hN;have:=S.hk.1;omega)
    (by omega) (by have:=S.hr;have:=S.hN;have:=S.hk;have:=S.kp;omega)
  simpa only [Nat.cast_min,Nat.cast_max] using H
lemma clean_fullPoly_gle (hL : LamData Fr o) (hp : 5≤p) (hN : 4*(r+2*m)<p*p)
    (hk : (4:ZMod p)*k=o)
    (hc : ∀ x y:ℕ,r≤x → x<r+2*m → r≤y → y<r+2*m →
      NoCut (Cut p r (Singular p o)) (min (x:ℤ) y) (max (x:ℤ) y)) :
    GLE p (2*r) (Fr.fullPoly r m) := by
  have H:=witness_fullPoly_gle hL hp hN hk hc
  have hw : witnessTable p r m r (r+2*m) = fun _ _=>0 := by
    ext i j
    simp only [witnessTable,witnessWeight]
    rw [if_pos]
    have:=i.isLt;have:=j.isLt;omega
  rw [hw] at H
  have ht : tropVal (fun _ _ : Fin m => 0)=0 := by
    apply Nat.le_zero.mp
    apply tropVal_le_of_forall
    intro σ
    simp
  simpa only [ht,zero_add] using H
lemma GKS3.uniform_gle (hL : LamData Fr o) (S : GKS3 o p r m k) :
    GLE p (2*r) (Fr.fullPoly r m) := by
  exact clean_fullPoly_gle hL (by have:=S.p13;omega)
    (by have:=S.hN;have:=S.p13;nlinarith)
    (by have H:=congrArg (fun n:ℕ=>(n:ZMod p)) S.hk.1;simpa using H) S.noCut
lemma GK1.GKS1.uniform_gle (hL : LamData Fr o) (S : GK1.GKS1 o p r m k) :
    GLE p (2*r) (Fr.fullPoly r m) := by
  exact clean_fullPoly_gle hL (by have:=S.p13;omega)
    (by have:=S.hN;have:=S.hk;have:=S.p13;nlinarith)
    (by have H:=congrArg (fun n:ℕ=>(n:ZMod p)) S.hk.1;simpa using H) S.noCut
end CatalanCore.Arith.Hybrid
#print axioms CatalanCore.Arith.Hybrid.GKS3.uniform_gle
#print axioms CatalanCore.Arith.Hybrid.GK1.GKS1.uniform_gle
