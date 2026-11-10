module

public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Plane
public import CatalanCore.Uniform.Content.BankShared.KTerm.KnownZero
public import CatalanCore.Uniform.Bank.Plane1.Content

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! The actual known-zero price supplies catalogue branches at every positive
geometry and every deletion depth. The optional returned window selects class2. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Plane1
open CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Arith.Hybrid Finset

theorem plane_knownZero_catalogue (g : ℚ) (hg : 0<g) (σ : Support)
    (a b c : ℤ) (h0 : a+b+c=0) (depth Q0 Pbad N0 : ℕ)
    (hQ0 : 3≤Q0) (hP : 6≤Pbad) (win : Bool)
    (hret : win=true → 3*a+4*b=0) :
    KCatValid g hg (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts
      Q0 Pbad N0 [knownZeroBranch win] := by
  intro br hbr i hi hr0 p _ hPb _ hqN kv hroots hcond
  rw [List.mem_singleton] at hbr
  subst br
  obtain ⟨r,S⟩ := i
  set m := (altGeom g hg).borderSize r with hm
  have hp7 : 7≤p := by omega
  have hpodd : p%2=1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by omega)
  have hsq : 3*(r+2*m)<p*p :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hQ0) hqN
  obtain ⟨⟨jA,eA,hjA0,hjA3,hkA0,hkAp⟩,⟨jB,eB,hjB0,hjB2,hkB0,hkBp⟩⟩ :=
    (planeBundle σ a b c h0).roots_facts hroots
  change 3*kv 0=jA*p+σ.rho at eA
  have hn : jA=1 ∨ jA=2 := by omega
  have hjB : jB=1 := by omega
  rw [hjB,Nat.one_mul] at eB
  have h3 : 3∣jA*p+σ.rho := by rw [←eA];exact dvd_mul_right _ _
  have hKA : planeKA σ jA p=kv 0 := by unfold planeKA;rw [←eA];omega
  have hKB : planeKB p=kv 1 := by unfold planeKB;omega
  have hNcond := hcond ⟨-1,2,-2,[0,0],0,false⟩ (by simp [knownZeroBranch])
  have hmpcond := hcond ⟨0,1,-2,[0,0],-1,false⟩ (by simp [knownZeroBranch])
  simp [KCond.Holds,KCond.L,dot] at hNcond hmpcond
  have hN : r+2*m≤2*p := by omega
  have hmp : 2*m<p := by omega
  have hreturn : win=true → 3*(a:ℚ)/(jA:ℚ)+2*(b:ℚ)=0 := by
    intro hw
    have hc := hcond ⟨0,0,0,[1,-1],-1,false⟩ (by simp [knownZeroBranch,hw])
    simp [KCond.Holds,KCond.L,dot] at hc
    have hρ : σ.rho≤2 := by cases σ <;> decide
    have hjA : jA=2 := by
      rcases hn with hn | hn
      · rw [hn,Nat.one_mul] at eA
        omega
      · exact hn
    rw [hjA]
    have h := hret hw
    have hq : 3*(a:ℚ)+4*(b:ℚ)=0 := by exact_mod_cast h
    norm_num
    linarith
  have hG := plane_knownZero_alt_gle g hg σ a b c h0 depth r m p jA hp7 hn h3 hm hi.2 hsq hmp hN win hreturn S
  rw [hKA,hKB] at hG
  have hdel : delCount (altGeom g hg) ⟨r,S⟩=r-S.card := by
    unfold delCount
    show (((altGeom g hg).geometry r).C).card-S.card=r-S.card
    have hcard : (((altGeom g hg).geometry r).C).card=r := by rw [altGeom_C,Finset.card_range]
    exact congrArg (fun n => n-S.card) hcard
  refine ⟨zPrice r m p (knownIntervals r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win)+2*(r-S.card),hG,?_⟩
  change _≤(knownZeroPrice win).evalN r p m kv+2*delCount (altGeom g hg) ⟨r,S⟩
  rw [knownZeroPrice_eval r m p kv win hpodd ((min_le_left _ _).trans hkAp.le),hdel] <;> exact le_rfl

end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.plane_knownZero_catalogue
