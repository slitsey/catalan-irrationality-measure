module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Bridge
public import CatalanCore.Uniform.Bank.Plane1.ContentClosed
public import CatalanCore.Uniform.Bank.Plane1.Cover
public import CatalanCore.Uniform.Bank.Plane1.Rows

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! # The dip rows: closed content bank with dip lines, and the point theorem (wave R1; ledger R01-R03; package R1e)

`dip_content_closed` is `plane_content_closed` for a closed bank whose catalogue is plane branches and **dip lines**
(`DipLine.ok`, `DipLine.line_valid`).  `dip_point` is `plane_frame_point` for a frame with a dip bank: the measure of
`L₃ + t π²`, `t = planeT σ a b`, is `ccert / (Dt - Λ)`, with the decay `Dp1` of the plane cover (`planeDecay_cover`)
and the content `Λ` of the dip bank.  The six dip theorems are instances (data modules `Dips.Data.*`). -/

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

/-- The data of a closed dip bank for the frame `(a, b, c)` on the support `σ`. -/
structure DipBankOK (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (kd : KBankDataC) (lns : List DipLine)
    (brs : List DipBridge) : Prop where
  check : kcheckC kd = true
  shifts : kd.shifts = [⟨3, σ.rho, 1⟩, ⟨2, 1, 1⟩]
  alpha : planeC = 2 * kd.α
  hlns : ∀ L ∈ lns, L.ok σ.rho a b c = true
  hbr : ∀ B ∈ brs, (∀ L ∈ B.lines, L ∈ lns) ∧ B.Member σ.rho
  cat : ∀ br ∈ kd.kcat, PlaneBranch br ∨ (∃ L ∈ lns, br = L.toBranch σ.rho) ∨ (∃ B ∈ brs, br = B.toBranch)
  hQ : 3 ≤ kd.Q
  hP : 6 ≤ kd.Pbad
  hM : 6 ∣ kd.M
  ht0 : kd.t0 ≤ 1 / 68
  hα0 : 13 / 6 ≤ kd.α0b
  hcF : 23 ≤ kd.cF
  hdepth : planeDepth ≤ kd.depth

/-- **The content of a dip frame from a closed bank with dip lines.** -/
theorem dip_content_closed (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (kd : KBankDataC) {lns : List DipLine} {brs : List DipBridge}
    (hok : DipBankOK σ a b c h0 kd lns brs) :
    HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) planeDepth)
      (altGeom planeC planeC_pos).scale (kd.Λ : ℝ) := by
  refine hasScaledContent_of_kcheckC kd hok.check planeC planeC_pos hok.alpha (planeFrame σ a b c h0).const planeDepth _
    hok.hdepth
    (AltQ.ofFrame planeC planeC_pos planeC_le_one (planeFrame σ a b c h0)
      ((cFr_plane σ a b c h0).trans hok.hcF))
    (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) 0 ?_ ?_ ?_ ?_
  · rw [hok.shifts]
    exact dip_cat_valid σ a b c h0 planeDepth kd.Q kd.Pbad 0 hok.hQ hok.hP lns brs kd.kcat hok.hlns hok.hbr hok.cat
  · intro n j0 j1 j2
    rw [hok.shifts]
    exact (planeBundle σ a b c h0).prefix_valid planeC planeC_pos planeDepth kd.Q kd.Pbad 0 n j0 j1 j2 hok.hQ hok.hP
  · rw [hok.shifts]
    exact plane_cat_valid σ a b c h0 planeC planeC_pos planeC_le_one planeDepth kd.Q kd.Pbad 0 hok.hQ hok.hP [kbD1x]
      (fun br hbr => by
        rw [List.mem_singleton] at hbr
        subst hbr
        exact Or.inl (by simp [planeTrop]))
  · exact PreValid_mono hok.hM hok.ht0 hok.hα0 (plane_preValid σ a b c h0 planeDepth)

/-- **The point theorem of a dip frame**: `μ(L₃ + t π²) ≤ B` and irrationality, `t = planeT σ a b`. -/
theorem dip_point (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {kd : KBankDataC} {lns : List DipLine} {brs : List DipBridge}
    (hok : DipBankOK σ a b c h0 kd lns brs) (hη : kd.Λ < Dp1.Dt) (hcc : 0 < Dp1.ccert) {B : ℚ}
    (hB : Dp1.ccert / (Dp1.Dt - kd.Λ) ≤ B) :
    MeasureLBAt (chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2) (B : ℝ) ∧
      Irrational (chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2) := by
  obtain ⟨h1, h2⟩ := plane_frame_point σ a b c h0 ha hb hc (dip_content_closed σ a b c h0 kd hok)
    (planeDecay_cover σ a b c h0) hη hcc
  refine ⟨h1.mono ?_, h2⟩
  have : ((Dp1.ccert / (Dp1.Dt - kd.Λ) : ℚ) : ℝ) ≤ (B : ℝ) := Rat.cast_le.2 hB
  push_cast at this
  exact this

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip_content_closed
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.dip_point
