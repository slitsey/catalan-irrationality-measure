module

public import CatalanCore.Uniform.Bank.Plane1.Rows

@[expose] public section
set_option Elab.async false

/-! # The plane theorem (wave H4 statement; ledger P116, P117)

**`plane_point`**: for every rational `t`, `L₃ + t π²` is irrational and has measure exponent `cc / (D - Λ)`,
whenever the plane has a content `Λ` and a decay `(D, cc)` (`PlaneContent`, `PlaneDecay`: for every plane frame at
once, at the selection depth) with `Λ < D`.  The frame of `t` is `exists_planeRow t` (P113): `S⁺`, or `S⁻` at
`t ∈ {1/9, 1/27}`.  The mirror (P117) is not a separate development: it is the `S⁻` instance of the same theorem
on the same cover (`mirror_point`).

`plane_point_of_covers` is the same theorem with the covers as data: a bank for each support (`PlaneBankOK`, the
`kcheck`-passing catalogue of `Plane1.Content`, both with the same `Λ`) and a decay cover `(T, D, P)` of the 25-piece
layout (any cover; the value of `μ` is that of the receipt: `μ* = D.ccert / (D.Dt - Λ)`). -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Measure
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Decay.Nodes CatalanCore.Uniform.Decay.PolyFull CatalanCore.Uniform.Decay.PolyWire3
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.AltDecay
  CatalanFrames.P6

/-- The content `Λ` of the plane: every plane frame, at the selection depth. -/
def PlaneContent (Λ : ℝ) : Prop :=
  ∀ (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0),
    HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) planeDepth) planeG.scale Λ

/-- The decay `(D, cc)` of the plane: every plane frame, at the selection depth. -/
def PlaneDecay (D cc : ℝ) : Prop :=
  ∀ (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0),
    HasScaledDecay (planeG.family (planeFrame σ a b c h0) planeDepth) planeG.scale D cc

/-- **The plane theorem (P116)**: for every rational `t`. -/
theorem plane_point (t : ℚ) {Λ D cc : ℚ} (hΛ : PlaneContent Λ) (hD : PlaneDecay D cc) (hη : Λ < D)
    (hcc : 0 < cc) :
    MeasureLBAt (chi3L2 + (t : ℝ) * Real.pi ^ 2) ((cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) ∧
      Irrational (chi3L2 + (t : ℝ) * Real.pi ^ 2) := by
  obtain ⟨σ, a, b, c, h0, ha, hb, hc, hT⟩ := exists_planeRow t
  have := plane_frame_point σ a b c h0 ha hb hc (hΛ σ a b c h0) (hD σ a b c h0) hη hcc
  rwa [hT] at this

/-- The data of a bank for the support `σ` (see `plane_content`). -/
structure PlaneBankOK (σ : Support) (kd : KBankData) : Prop where
  check : kcheck kd = true
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

/-- Content of the plane from a bank on each support, both with the same `Λ`. -/
theorem planeContent_of_banks {kP kM : KBankData} (hP : PlaneBankOK .plus kP) (hM : PlaneBankOK .minus kM)
    (hΛ : kP.Λ = kM.Λ) : PlaneContent (kP.Λ : ℝ) := by
  intro σ a b c h0
  cases σ
  · exact plane_content .plus a b c h0 kP hP.check hP.shifts hP.alpha hP.cat hP.hQ hP.hP hP.hM hP.ht0
      hP.hα0 hP.hcF planeDepth hP.hdepth
  · have := plane_content .minus a b c h0 kM hM.check hM.shifts hM.alpha hM.cat hM.hQ hM.hP hM.hM hM.ht0
      hM.hα0 hM.hcF planeDepth hM.hdepth
    rwa [← hΛ] at this

/-- Decay of the plane from a table cover. -/
theorem planeDecay_of_tables (T : PolyTables3)
    (hRP : T.RP = altPieces planeC) (hCP : T.CP = altPieces planeC) (hMq : T.Mq = 1 + planeC / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = 3)
    (N : ℕ) (hE : energyCheck N (altPieces planeC) (altPieces planeC) D.Inu = true)
    (hε : 0 < D.ε) : PlaneDecay (D.Dt : ℝ) (D.ccert : ℝ) :=
  fun σ a b c h0 => plane_decay σ a b c h0 T hRP hCP hMq D P hT hd N hE hε planeDepth

/-- **The plane theorem from covers**: two content banks (one per support, same `Λ`) and a decay cover. -/
theorem plane_point_of_covers (t : ℚ) {kP kM : KBankData} (hP : PlaneBankOK .plus kP)
    (hM : PlaneBankOK .minus kM) (hΛ : kP.Λ = kM.Λ) (T : PolyTables3)
    (hRP : T.RP = altPieces planeC) (hCP : T.CP = altPieces planeC) (hMq : T.Mq = 1 + planeC / 2)
    (D : SplineData) (P : RatPolygon) (hT : T.check D P = true) (hd : D.dim = 3)
    (N : ℕ) (hE : energyCheck N (altPieces planeC) (altPieces planeC) D.Inu = true)
    (hε : 0 < D.ε) (hη : kP.Λ < D.Dt) (hcc : 0 < D.ccert) :
    MeasureLBAt (chi3L2 + (t : ℝ) * Real.pi ^ 2) ((D.ccert : ℝ) / ((D.Dt : ℝ) - (kP.Λ : ℝ))) ∧
      Irrational (chi3L2 + (t : ℝ) * Real.pi ^ 2) :=
  plane_point t (planeContent_of_banks hP hM hΛ) (planeDecay_of_tables T hRP hCP hMq D P hT hd N hE hε)
    hη hcc

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_point
#print axioms CatalanCore.Uniform.Bank.Plane1.planeContent_of_banks
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_point_of_covers
