module

public import CatalanCore.Uniform.Bank.Plane1.Bound
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodContent

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The content of the plane frames from the closed form (wave H5a-closed; ledger P109, P115)

`plane_content_closed` is `plane_content` for a bank `kd : KBankDataC` whose periodic layer is the expansion of a
period table (`kcheckC`, Theorem C3 of `THREE-TERM-CONTENT-2026-11-07.md`): the same hypotheses on the shifts, the
catalogue and the small primes (with `α₀ᵇ ≥ 13/6`), the same conclusion `HasScaledContent … Λ` for every plane
frame at once.  `PlaneBankOKC` and `planeContent_of_banksC` are `PlaneBankOK` and `planeContent_of_banks`: two
closed banks (one per support, the same `Λ`) give `PlaneContent Λ`. -/

namespace CatalanCore.Uniform.Bank.Plane1
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.SmallPrimes
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Rect

/-- **The scaled content of the plane family from a closed bank** (P109 with P115 in closed form). -/
theorem plane_content_closed (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (kd : KBankDataC)
    (hkd : kcheckC kd = true)
    (hshifts : kd.shifts = (planeBundle σ a b c h0).shifts) (hα : planeC = 2 * kd.α)
    (hcat : ∀ br ∈ kd.kcat, PlaneBranch br) (hQ : 3 ≤ kd.Q) (hP : 6 ≤ kd.Pbad) (hM : 6 ∣ kd.M)
    (ht0 : kd.t0 ≤ 1 / 68) (hα0 : 13 / 6 ≤ kd.α0b) (hcF : 23 ≤ kd.cF) (depth : ℕ)
    (hdepth : depth ≤ kd.depth) :
    HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) depth)
      (altGeom planeC planeC_pos).scale (kd.Λ : ℝ) := by
  refine hasScaledContent_of_kcheckC kd hkd planeC planeC_pos hα (planeFrame σ a b c h0).const depth _ hdepth
    (AltQ.ofFrame planeC planeC_pos planeC_le_one (planeFrame σ a b c h0) ((cFr_plane σ a b c h0).trans hcF))
    (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 ?_ ?_ ?_ ?_
  · rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth kd.Q kd.Pbad 0 hQ hP kd.kcat hcat
  · intro n j0 j1 j2
    rw [hshifts]
    exact (planeBundle σ a b c h0).prefix_valid planeC planeC_pos depth kd.Q kd.Pbad 0 n j0 j1 j2 hQ hP
  · rw [hshifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one depth kd.Q kd.Pbad 0 hQ hP [kbD1x]
      (fun br hbr => by
        rw [List.mem_singleton] at hbr
        subst hbr
        exact Or.inl (by simp [planeTrop]))
  · exact PreValid_mono hM ht0 hα0 (plane_preValid σ a b c h0 depth)

/-- The data of a closed bank for the support `σ` (see `plane_content_closed`). -/
structure PlaneBankOKC (σ : Support) (kd : KBankDataC) : Prop where
  check : kcheckC kd = true
  shifts : kd.shifts = [⟨3, σ.rho, 1⟩, ⟨2, 1, 1⟩]
  alpha : planeC = 2 * kd.α
  cat : ∀ br ∈ kd.kcat, PlaneBranch br
  hQ : 3 ≤ kd.Q
  hP : 6 ≤ kd.Pbad
  hM : 6 ∣ kd.M
  ht0 : kd.t0 ≤ 1 / 68
  hα0 : 13 / 6 ≤ kd.α0b
  hcF : 23 ≤ kd.cF
  hdepth : planeDepth ≤ kd.depth

/-- Content of the plane from a closed bank on each support, both with the same `Λ`. -/
theorem planeContent_of_banksC {kP kM : KBankDataC} (hP : PlaneBankOKC .plus kP)
    (hM : PlaneBankOKC .minus kM) (hΛ : kP.Λ = kM.Λ) : PlaneContent (kP.Λ : ℝ) := by
  intro σ a b c h0
  cases σ
  · exact plane_content_closed .plus a b c h0 kP hP.check hP.shifts hP.alpha hP.cat hP.hQ hP.hP hP.hM hP.ht0
      hP.hα0 hP.hcF planeDepth hP.hdepth
  · have := plane_content_closed .minus a b c h0 kM hM.check hM.shifts hM.alpha hM.cat hM.hQ hM.hP hM.hM hM.ht0
      hM.hα0 hM.hcF planeDepth hM.hdepth
    rwa [← hΛ] at this

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_content_closed
#print axioms CatalanCore.Uniform.Bank.Plane1.planeContent_of_banksC
