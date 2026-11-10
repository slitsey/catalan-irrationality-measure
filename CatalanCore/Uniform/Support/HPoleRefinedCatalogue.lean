module

public import CatalanCore.Uniform.Support.HPoleCatalogue
public import CatalanCore.Uniform.Support.HPolePeriodRows

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Generic catalogue compilation of the full-period refined row (Q18).
Every order, coefficient sequence, geometry and finite chamber list is a parameter.
The old four-row catalogue is a prefix, so its certified numerical indices remain valid. -/
namespace CatalanCore.Uniform.Support
open CatalanCore CatalanCore.Basic CatalanCore.Uniform
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.SmallPrimes Finset Polynomial
open CatalanCore.Uniform.Content.Wire

namespace HPolePeriodRows

def chamberConditions (j : ℕ) : List KCond :=
  [⟨0,1,-2,[],0,false⟩,
   ⟨1,-(Int.ofNat (j-1)),0,[],0,false⟩,
   ⟨-1,Int.ofNat j,0,[],0,false⟩,
   ⟨0,1,0,[],-(Int.ofNat (2*(j+2))),false⟩]

def nonwrapBranch (h j : ℕ) : KBranch :=
  ⟨.add (.smul h .vr) (.smul (h-3) .vm),
    chamberConditions j ++ [⟨-1,Int.ofNat j,-2,[],0,false⟩],0⟩

def crossLeftBranch (h j : ℕ) : KBranch :=
  ⟨.add (.add (.smul (h-2) .vr) (.smul (h-3) .vm)) (.smul (2*j) .vp),
    chamberConditions j ++
      [⟨1,-(Int.ofNat j),1,[],0,false⟩,⟨1,-(Int.ofNat j),2,[],0,false⟩],0⟩

def crossRightBranch (h j : ℕ) : KBranch :=
  ⟨.tsub (.add (.smul (h+2) .vr) (.smul (h+1) .vm)) (.smul (2*j) .vp),
    chamberConditions j ++
      [⟨-1,Int.ofNat j,-1,[],0,false⟩,⟨1,-(Int.ofNat j),2,[],0,false⟩],0⟩

def refinedBranches (h j : ℕ) : List KBranch :=
  [nonwrapBranch h j,crossLeftBranch h j,crossRightBranch h j]

def refinedCatalogue (h : ℕ) (js : List ℕ) : List KBranch :=
  IntegerPoleRows.catalogue h ++ js.flatMap (refinedBranches h)

private theorem chamber_facts (j r p m : ℕ) (kv : ℕ → ℕ)
    (hc : ∀ cd ∈ chamberConditions j,cd.Holds r p m kv) :
    2*m ≤ p ∧ (j-1)*p ≤ r ∧ r ≤ j*p ∧ 2*(j+2) ≤ p := by
  have h0 := hc ⟨0,1,-2,[],0,false⟩ (by simp [chamberConditions])
  have h1 := hc ⟨1,-(Int.ofNat (j-1)),0,[],0,false⟩ (by simp [chamberConditions])
  have h2 := hc ⟨-1,Int.ofNat j,0,[],0,false⟩ (by simp [chamberConditions])
  have h3 := hc ⟨0,1,0,[],-(Int.ofNat (2*(j+2))),false⟩ (by simp [chamberConditions])
  norm_num [KCond.Holds,KCond.L,dot] at h0 h1 h2 h3
  have hlo : (((j-1)*p : ℕ) : ℤ) ≤ (r : ℤ) := by push_cast; nlinarith only [h1]
  have hhi : (r : ℤ) ≤ ((j*p : ℕ) : ℤ) := by push_cast; nlinarith only [h2]
  exact ⟨by omega,by exact_mod_cast hlo,by exact_mod_cast hhi,by omega⟩

end HPolePeriodRows

/-- Every finite collection of closed chambers is a valid refined catalogue.
No period-translation hypothesis is silently dropped, and no numerical design is fixed. -/
theorem hpole_refined_catalogue (h : ℕ) (hh : 3 ≤ h) (d : ℕ → ℚ)
    (c : ℚ) (hc : 0<c) (const : ℝ) (depth : ℕ)
    (shifts : List Shift) (Q0 Pbad N0 : ℕ) (hQ : 1≤Q0) (hbad : 2≤Pbad)
    (hcoeff : ∀ (p : ℕ) [Fact p.Prime],N0<p →
      ∀ k ∈ Icc 1 (h-1),d k ∈ LocRing p)
    (js : List ℕ) (hjs : ∀ j ∈ js,1≤j) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF h d) (hpoleE h d) (altGeom c hc).geometry)
      shifts Q0 Pbad N0 (HPolePeriodRows.refinedCatalogue h js) := by
  have old := hpole_catalogue h (by omega) d c hc const depth shifts Q0 Pbad N0 hQ hbad hcoeff
  intro br hbr i hi hr p _ hpb hpn hN kv hkv hcond
  change br ∈ IntegerPoleRows.catalogue h ++ js.flatMap (HPolePeriodRows.refinedBranches h) at hbr
  rcases List.mem_append.mp hbr with hold | hnew
  · exact old br hold i hi hr p hpb hpn hN kv hkv hcond
  obtain ⟨j,hj,hbr⟩ := List.mem_flatMap.mp hnew
  have hcbase : ∀ cd ∈ HPolePeriodRows.chamberConditions j,cd ∈ br.conds := by
    simp only [HPolePeriodRows.refinedBranches,List.mem_cons,List.not_mem_nil,or_false] at hbr
    rcases hbr with rfl | rfl | rfl <;>
      intro cd hcd <;>
      simp [HPolePeriodRows.nonwrapBranch,HPolePeriodRows.crossLeftBranch,
        HPolePeriodRows.crossRightBranch,hcd]
  have facts := HPolePeriodRows.chamber_facts j i.1 p ((altGeom c hc).borderSize i.1) kv
    (fun cd hcd => hcond cd (hcbase cd hcd))
  have hs := altGeom_hybShape c hc hi.2
  have hshort : 2*((altGeom c hc).geometry i.1).k < p := by
    have hodd : p%2=1 := by
      rcases (Fact.out : p.Prime).eq_two_or_odd with he | he
      · omega
      · exact he
    rw [geometry_k_eq_borderSize]
    omega
  have hp5 : 5≤p := by have := hjs j hj; omega
  have hlo : (j-1)*p ≤ i.1 := facts.2.1
  have hhi : i.1 ≤ j*p := facts.2.2.1
  have hpj : 2*(j+2)≤p := facts.2.2.2
  have hd := hcoeff p hpn
  simp only [HPolePeriodRows.refinedBranches,List.mem_cons,List.not_mem_nil,or_false] at hbr
  rcases hbr with rfl | rfl | rfl
  · have hcN := hcond ⟨-1,Int.ofNat j,-2,[],0,false⟩
      (by simp [HPolePeriodRows.nonwrapBranch])
    norm_num [KCond.Holds,KCond.L,dot] at hcN
    have hcNz : ((i.1+2*(altGeom c hc).borderSize i.1 : ℕ) : ℤ) ≤ ((j*p : ℕ) : ℤ) := by
      push_cast; nlinarith only [hcN]
    have hcNn : i.1+2*((altGeom c hc).geometry i.1).k ≤ j*p := by
      rw [geometry_k_eq_borderSize]; exact_mod_cast hcNz
    refine ⟨h*i.1+(h-3)*((altGeom c hc).geometry i.1).k,?_,?_⟩
    · apply IntegerPoleRows.family_of_window h d hs i.2 _
      intro ι _ _ cn hinj hcr
      exact HPolePeriodRows.row_refined_first_nonwrap h hh d hd cn hinj hcr
        hp5 hshort (hjs j hj) hlo hhi hpj hcNn
    · simp [HPolePeriodRows.nonwrapBranch,KExpr.evalN,geometry_k_eq_borderSize]
  · have hm := hcond ⟨1,-(Int.ofNat j),1,[],0,false⟩
      (by simp [HPolePeriodRows.crossLeftBranch])
    have hn := hcond ⟨1,-(Int.ofNat j),2,[],0,false⟩
      (by simp [HPolePeriodRows.crossLeftBranch])
    norm_num [KCond.Holds,KCond.L,dot] at hm hn
    have hmz : ((j*p : ℕ) : ℤ) ≤ ((i.1+(altGeom c hc).borderSize i.1 : ℕ) : ℤ) := by
      push_cast; nlinarith only [hm]
    have hnz : ((j*p : ℕ) : ℤ) ≤ ((i.1+2*(altGeom c hc).borderSize i.1 : ℕ) : ℤ) := by
      push_cast; nlinarith only [hn]
    have hmn : j*p ≤ i.1+((altGeom c hc).geometry i.1).k := by
      rw [geometry_k_eq_borderSize]; exact_mod_cast hmz
    have hnn : j*p ≤ i.1+2*((altGeom c hc).geometry i.1).k := by
      rw [geometry_k_eq_borderSize]; exact_mod_cast hnz
    refine ⟨(h-2)*i.1+(h-3)*((altGeom c hc).geometry i.1).k+2*j*p,?_,?_⟩
    · apply IntegerPoleRows.family_of_window h d hs i.2 _
      intro ι _ _ cn hinj hcr
      exact HPolePeriodRows.row_refined_first_cross_left h hh d hd cn hinj hcr
        hp5 hshort (hjs j hj) hlo hhi hpj hmn hnn
    · simp [HPolePeriodRows.crossLeftBranch,KExpr.evalN,geometry_k_eq_borderSize,Nat.mul_assoc]
  · have hm := hcond ⟨-1,Int.ofNat j,-1,[],0,false⟩
      (by simp [HPolePeriodRows.crossRightBranch])
    have hn := hcond ⟨1,-(Int.ofNat j),2,[],0,false⟩
      (by simp [HPolePeriodRows.crossRightBranch])
    norm_num [KCond.Holds,KCond.L,dot] at hm hn
    have hmz : ((i.1+(altGeom c hc).borderSize i.1 : ℕ) : ℤ) ≤ ((j*p : ℕ) : ℤ) := by
      push_cast; nlinarith only [hm]
    have hnz : ((j*p : ℕ) : ℤ) ≤ ((i.1+2*(altGeom c hc).borderSize i.1 : ℕ) : ℤ) := by
      push_cast; nlinarith only [hn]
    have hmn : i.1+((altGeom c hc).geometry i.1).k ≤ j*p := by
      rw [geometry_k_eq_borderSize]; exact_mod_cast hmz
    have hnn : j*p ≤ i.1+2*((altGeom c hc).geometry i.1).k := by
      rw [geometry_k_eq_borderSize]; exact_mod_cast hnz
    refine ⟨(h+2)*i.1+(h+1)*((altGeom c hc).geometry i.1).k-2*j*p,?_,?_⟩
    · apply IntegerPoleRows.family_of_window h d hs i.2 _
      intro ι _ _ cn hinj hcr
      exact HPolePeriodRows.row_refined_first_cross_right h hh d hd cn hinj hcr
        hp5 hshort (hjs j hj) hlo hhi hpj hmn hnn
    · simp [HPolePeriodRows.crossRightBranch,KExpr.evalN,geometry_k_eq_borderSize,Nat.mul_assoc]

end CatalanCore.Uniform.Support
#print axioms CatalanCore.Uniform.Support.hpole_refined_catalogue
