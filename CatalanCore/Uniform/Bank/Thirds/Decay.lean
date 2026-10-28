import CatalanCore.Uniform.Bank.Thirds.Energy
import CatalanCore.Uniform.Bank.Thirds.Final
import CatalanCore.Uniform.Decay.PolyChain.CheckMain
import CatalanCore.Uniform.Decay.PolyFull.Full
import CatalanFrames.Thirds.ContourInstances
set_option Elab.async false

/-! `ThirdsDecay` from the polygon checker (lane B, B4): every frame and node hypothesis of
`hasScaledDecay_of_check_poly` is discharged for `G310` and the two thirds frames.  What remains is
the single Boolean statement `D.checkP R P = true` (cell tables). -/

namespace CatalanCore.Uniform.Bank.Thirds
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.Thirds
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.PolyChain
  CatalanCore.Uniform.Decay.PolyFull

theorem G310_supp : ∀ r a : ℕ, a ∈ (G310.geometry r).C → (a : ℝ) ≤ r := by
  intro r a ha
  have h : (G310.geometry r).C = Finset.range r := altGeom_C _ c310_pos r
  rw [h, Finset.mem_range] at ha
  exact_mod_cast ha.le

theorem G310_blocks_v :
    (∀ i, ((G310.common.block i).v : ℝ) ≤ 2) ∧ (∀ i, ((G310.row.block i).v : ℝ) ≤ 2) ∧
      (∀ i, ((G310.column.block i).v : ℝ) ≤ 2) := by
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩ <;>
  · simp [G310, altGeom, single, commonB, rowB, colB]
    try norm_num

theorem thirdsAc_hAR : ∀ i : Fin thirdsAc.d, ((⌊thirdsAc.xs - thirdsAc.μ i⌋ : ℤ) : ℚ) +
    thirdsAc.μ i ≤ thirdsAc.n0off := by
  intro i
  fin_cases i
  · have : ⌊(2 / 3 : ℚ) - 1 / 3⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
    show ((⌊(2 / 3 : ℚ) - 1 / 3⌋ : ℤ) : ℚ) + 1 / 3 ≤ 1
    rw [this]; norm_num
  · have : ⌊(2 / 3 : ℚ) - 1⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    show ((⌊(2 / 3 : ℚ) - 1⌋ : ℤ) : ℚ) + 1 ≤ 1
    rw [this]; norm_num

theorem thirdsBc_hAR : ∀ i : Fin thirdsBc.d, ((⌊thirdsBc.xs - thirdsBc.μ i⌋ : ℤ) : ℚ) +
    thirdsBc.μ i ≤ thirdsBc.n0off := by
  intro i
  fin_cases i
  · have : ⌊(1 / 3 : ℚ) - 2 / 3⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    show ((⌊(1 / 3 : ℚ) - 2 / 3⌋ : ℤ) : ℚ) + 2 / 3 ≤ 0
    rw [this]; norm_num
  · have : ⌊(1 / 3 : ℚ) - 1⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    show ((⌊(1 / 3 : ℚ) - 1⌋ : ℤ) : ℚ) + 1 ≤ 0
    rw [this]; norm_num

/-- **Window decay of the thirds family from the polygon checker.**  For a spline datum `D` with the
bank's scalars (`Mq = 23/20`, `dim = 2`, `Inu`, `ε`, `Dt`, `ccert`) and any sound cell rules whose
Boolean check `D.checkP R P` holds. -/
theorem thirds_decay_of_check {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) (hd2 : Fr.d = 2)
    (hm0 : ∀ i, (1 / 3 : ℝ) ≤ Fr.μ i)
    (R : PolyCellRules G310.nodePot) (D : SplineData) (P : RatPolygon)
    (hchk : D.checkP R P = true) (hMq : D.Mq = 23 / 20) (hdim : D.dim = 2)
    (hInu : D.Inu = 867481404213 / 500000000000) (hε : D.ε = 1 / 1000)
    (hDt : D.Dt = DtT) (hcc : D.ccert = ctT) (depth : ℕ) : ThirdsDecay Fr depth := by
  obtain ⟨hc, hr, hq⟩ := G310_blocks_v
  have h := hasScaledDecay_of_check_poly G310 hC hAR hnorm1 R D P hchk
    (by rw [hMq, G310_totalMass]) (by rw [hdim, hd2])
    (by rw [hInu]; exact Inu_le_nodeEnergy)
    (nodePot_conj G310) ((nodePot_real_continuous G310).continuousOn) G310_supp
    (Bd := 2) (by norm_num) hc hr hq (m0 := 1 / 3) (by norm_num) hm0
    (e := 1 / 2000) (by norm_num) (by rw [hε]; norm_num) depth
  rw [hDt, hcc] at h
  exact h

end CatalanCore.Uniform.Bank.Thirds
