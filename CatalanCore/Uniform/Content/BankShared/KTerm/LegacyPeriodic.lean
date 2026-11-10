module

public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodTranslation

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! Generic suppliers for periodic conversion of existing one-index catalogues.
No extra frame/order/degree/depth/scale assumptions are introduced. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid Polynomial

def legacyShifts (q o : ℕ) : List Shift := [⟨q,o,1⟩,⟨q,o,1⟩]
def legacyZeroOld : Branch := ⟨.cst 0, [⟨-1,0,-2,1,0,true⟩], 0⟩
def legacyZero : KBranch := legacyZeroOld.liftK 0

theorem legacy_zero_valid (c : ℚ) (hc : 0<c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (q o Pbad N0 : ℕ) (cat : List Branch)
    (hcat : CatValidFam c hc const depth Q q o Pbad N0 cat) (hD6 : brD6 ∈ cat) :
    CatValidFam c hc const depth Q q o Pbad N0 [legacyZeroOld] := by
  intro b hb i hi hr p _ hPb hN0 hQN j k hk hj0 hjq hk0 hkp hconds
  simp only [List.mem_singleton] at hb
  subst b
  have hzk := hconds ⟨-1,0,-2,1,0,true⟩ (by simp [legacyZeroOld])
  simp only [Cond.Holds, Cond.L, ite_true] at hzk
  have hz : i.1+2*(altGeom c hc).borderSize i.1<k := by omega
  have hd : ∀ cd ∈ brD6.conds, cd.Holds i.1 p ((altGeom c hc).borderSize i.1) k := by
    intro cd hcd
    simp only [brD6, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hcd
    rcases hcd with rfl | rfl
    · simp only [Cat.cNlep, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false]
      omega
    · simp only [Cat.cRlek, Cond.Holds, Cond.L, Bool.false_eq_true, ite_false]
      omega
  obtain ⟨n,hn,hbound⟩ := hcat brD6 hD6 i hi hr p hPb hN0 hQN j k hk hj0 hjq hk0 hkp hd
  refine ⟨n,hn,?_⟩
  change n≤2*(altGeom c hc).borderSize i.1-(k-i.1)+0*delCount (altGeom c hc) i at hbound
  have hn0 : n≤0 := by omega
  simpa only [legacyZeroOld, Expr.evalN, zero_mul, add_zero] using hn0

theorem legacy_kcat_valid (c : ℚ) (hc : 0<c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (q o Pbad N0 : ℕ) (cat : List Branch)
    (hcat : CatValidFam c hc const depth Q q o Pbad N0 cat) (hD6 : brD6 ∈ cat) :
    KCatValidFam c hc const depth Q (legacyShifts q o) q Pbad N0
      (cat.map (Branch.liftK 0) ++ [legacyZero]) := by
  have h1 := hcat.liftK c hc const depth Q q o Pbad N0 cat (legacyShifts q o) 0 q
    (by simp [legacyShifts]) rfl rfl le_rfl
  have hz := legacy_zero_valid c hc const depth Q q o Pbad N0 cat hcat hD6
  have h2 := hz.liftK c hc const depth Q q o Pbad N0 [legacyZeroOld] (legacyShifts q o) 0 q
    (by simp [legacyShifts]) rfl rfl le_rfl
  intro br hbr
  rcases List.mem_append.1 hbr with hbr | hbr
  · exact h1 br hbr
  · exact h2 br (by simpa only [List.map_cons,List.map_nil,legacyZero] using hbr)

theorem legacy_d1x_valid (c : ℚ) (hc : 0<c) (const : ℝ) (depth : ℕ)
    (Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X])
    (q o Pbad N0 : ℕ) (cat : List Branch)
    (hcat : CatValidFam c hc const depth Q q o Pbad N0 cat) (hD1x : brD1x ∈ cat) :
    KCatValidFam c hc const depth Q (legacyShifts q o) q Pbad N0 [kbD1xB] := by
  have h : CatValidFam c hc const depth Q q o Pbad N0 [brD1x] := by
    intro br hbr
    simp only [List.mem_singleton] at hbr
    subst br
    exact hcat brD1x hD1x
  exact h.liftK c hc const depth Q q o Pbad N0 [brD1x] (legacyShifts q o) 0 q
    (by simp [legacyShifts]) rfl rfl le_rfl

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.legacy_zero_valid
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.legacy_kcat_valid
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.legacy_d1x_valid
