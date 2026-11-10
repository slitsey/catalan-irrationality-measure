module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Rows
public import CatalanCore.Uniform.Bank.Plane1.Dips.Bridge
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000
/-! Thin compatibility for the retained 1/6 dip certificates. Generic Rows
contains no fixed geometry, cover, budget or nonvanishing supplier. -/
namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.SmallPrimes
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect CatalanCore.Measure CatalanFrames.P6
  CatalanCore.Uniform.Bank.Plane1

/-- A catalogue of plane branches, valid dip lines and valid bridges is valid. -/
theorem dip_cat_valid (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (depth Q0 Pbad N0 : ℕ) (hQ0 : 3 ≤ Q0)
    (hP : 6 ≤ Pbad) (lns : List DipLine) (brs : List DipBridge) (cat : List KBranch)
    (hlns : ∀ L ∈ lns, L.ok σ.rho a b c = true)
    (hbr : ∀ B ∈ brs, (∀ L ∈ B.lines, L ∈ lns) ∧ B.Member σ.rho)
    (hcat : ∀ br ∈ cat, PlaneBranch br ∨ (∃ L ∈ lns, br = L.toBranch σ.rho) ∨ (∃ B ∈ brs, br = B.toBranch)) :
    KCatValid planeC planeC_pos (planeFrame σ a b c h0) depth (planeBundle σ a b c h0).shifts Q0 Pbad N0 cat := by
  intro br hbr'
  rcases hcat br hbr' with h | ⟨L, hL, rfl⟩ | ⟨B, hB, rfl⟩
  · exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth Q0 Pbad N0 hQ0 hP [br]
      (fun b' hb' => by rw [List.mem_singleton] at hb'; subst hb'; exact h) br (List.mem_singleton_self _)
  · exact DipLine.line_valid σ a b c h0 depth Q0 Pbad N0 hQ0 hP L (hlns L hL) _ (List.mem_singleton_self _)
  · exact DipBridge.valid B σ a b c h0 depth Q0 Pbad N0 hQ0 hP (fun L hL => hlns L ((hbr B hB).1 L hL))
      (hbr B hB).2 _ (List.mem_singleton_self _)

/-- The catalogue of a dip bank: the plane branches, the lines, the bridges, the prefix windows. -/
def dipCat (ρ : ℕ) (lns : List DipLine) (brs : List DipBridge) (pres : List (ℕ × ℕ × ℕ × ℕ)) : List KBranch :=
  planeTrop ++ lns.map (fun L => L.toBranch ρ) ++ brs.map DipBridge.toBranch ++
    pres.map (fun x => kbrPre x.1 x.2.1 [x.2.2.1, x.2.2.2])

theorem dipCat_mem (ρ : ℕ) (lns : List DipLine) (brs : List DipBridge) (pres : List (ℕ × ℕ × ℕ × ℕ)) :
    ∀ br ∈ dipCat ρ lns brs pres,
      PlaneBranch br ∨ (∃ L ∈ lns, br = L.toBranch ρ) ∨ (∃ B ∈ brs, br = B.toBranch) := by
  intro br hbr
  simp only [dipCat, List.mem_append, List.mem_map] at hbr
  rcases hbr with ((h | ⟨L, hL, rfl⟩) | ⟨B, hB, rfl⟩) | ⟨x, _, rfl⟩
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl ⟨L, hL, rfl⟩)
  · exact Or.inr (Or.inr ⟨B, hB, rfl⟩)
  · exact Or.inl (Or.inr ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, rfl⟩)


theorem legacyBankOK (σ : Support) (a b c : ℤ) (h0 : a+b+c=0)
    (kd : KBankDataC) (lns : List DipLine) (brs : List DipBridge)
    (hcheck : kcheckC kd=true)
    (hshifts : kd.shifts=[⟨3,σ.rho,1⟩,⟨2,1,1⟩]) (halpha : planeC=2*kd.α)
    (hlns : ∀ L∈lns,L.ok σ.rho a b c=true)
    (hbr : ∀ B∈brs,(∀ L∈B.lines,L∈lns) ∧ B.Member σ.rho)
    (hcat : ∀ br∈kd.kcat,PlaneBranch br ∨ (∃ L∈lns,br=L.toBranch σ.rho) ∨ (∃ B∈brs,br=B.toBranch))
    (hQ : 3≤kd.Q) (hP : 6≤kd.Pbad) (hM : 6∣kd.M)
    (ht0 : kd.t0≤1/68) (halpha0 : 13/6≤kd.α0b) (hcF : 23≤kd.cF) (hdepth : planeDepth≤kd.depth) :
    DipBankOK planeC planeC_pos planeDepth σ a b c h0 kd
      (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 where
  check := hcheck
  alpha := halpha
  hdepth := hdepth
  control := AltQ.ofFrame planeC planeC_pos planeC_le_one (planeFrame σ a b c h0)
    ((cFr_plane σ a b c h0).trans hcF)
  cat := by
    rw [hshifts]
    exact dip_cat_valid σ a b c h0 planeDepth kd.Q kd.Pbad 0 hQ hP lns brs kd.kcat hlns hbr hcat
  «prefix» := by
    intro n j0 j1 j2
    rw [hshifts]
    exact (planeBundle σ a b c h0).prefix_valid planeC planeC_pos planeDepth kd.Q kd.Pbad 0 n j0 j1 j2 hQ hP
  d1x := by
    rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one planeDepth kd.Q kd.Pbad 0 hQ hP [kbD1x]
      (fun br hbr => by
        rw [List.mem_singleton] at hbr
        subst hbr
        exact Or.inl (by simp [planeTrop]))
  pre := PreValid_mono hM ht0 halpha0 (plane_preValid σ a b c h0 planeDepth)
end CatalanCore.Uniform.Bank.Plane1.Dips
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.legacyBankOK
