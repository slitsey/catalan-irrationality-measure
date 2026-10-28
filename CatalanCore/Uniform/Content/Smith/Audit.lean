module

public import CatalanCore.Uniform.Content.Smith.LP1
public import CatalanCore.Uniform.Content.Smith.Weights
public import CatalanCore.Uniform.Content.Smith.PoleCells
public import CatalanCore.Uniform.Content.Smith.DerivedLoads

@[expose] public section

/-!
# Audit of the Smith layer (H2) and the PT / LP1 / LP2 layer (H3)

* `#print axioms` of every main result (standard axioms only).
* Instance tests: a lambda-like frame (`LamData`, `q = 4`) is a `TwoTermData`, and the hypothesis
  packages `LP2Hyp`, `LP1Hyp` are inhabited at `p = 29` (`4·22 = 3·29 + 1`), so the general theorems
  instantiate in the existing lambda setting.
-/

open Finset CatalanCore CatalanCore.Arith.Hybrid

namespace CatalanCore.Uniform.Content.Smith

/-- The lambda-like frames are two-term frames with `q = 4`. -/
theorem _root_.CatalanCore.Arith.Hybrid.LamData.toTwoTerm {Fr : Frame} {o : ℕ} (hL : LamData Fr o) : TwoTermData Fr 4 o where
  o_pos := hL.o_pos
  o_lt := by have := hL.o_le; omega
  delta_eq := fun t ht => by simpa using hL.delta_eq t ht
  dsq_eq := fun t ht => by rw [hL.dsq_eq t ht]; push_cast; norm_num

instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

lemma lam_norm_good {Fr : Frame} {o : ℕ} (hL : LamData Fr o) :
    Fr.norm ∈ CatalanCore.S 29 ∧ red 29 Fr.norm ≠ 0 := by
  rw [hL.norm_eq]
  refine ⟨(Good.ofNat (ℓ := 29) 16).1, ?_⟩
  have : red 29 (16 : ℚ) = (16 : ZMod 29) := by simp [red]
  rw [this]; decide

lemma lam_hsq (bound : ℕ) (hb : 4 * bound ≤ 841) :
    ∀ t, 1 ≤ t → t < bound → ¬ 29 ^ 2 ∣ 4 * t - 1 := by
  intro t ht1 htb h
  have := Nat.le_of_dvd (by omega) h
  omega

/-- **Instance test (LP2).** -/
theorem lp2_instance (Fr : Frame) (hL : LamData Fr 1) : LP2Hyp Fr 29 4 1 25 8 22 3 where
  cfg :=
    { tt := hL.toTwoTerm
      sg := { hqp := by norm_num, hk := by norm_num, hk0 := by norm_num, hkp := by norm_num,
              hj0 := by norm_num, hNk := by norm_num }
      hsq := lam_hsq 41 (by norm_num)
      hnm := (lam_norm_good hL).1
      hnm0 := (lam_norm_good hL).2 }
  hrp := by norm_num
  hkr := by norm_num
  p5 := by norm_num

/-- **Instance test (LP1).** -/
theorem lp1_instance (Fr : Frame) (hL : LamData Fr 1) : LP1Hyp Fr 29 4 1 40 9 22 3 where
  cfg :=
    { tt := hL.toTwoTerm
      sg := { hqp := by norm_num, hk := by norm_num, hk0 := by norm_num, hkp := by norm_num,
              hj0 := by norm_num, hN2 := by norm_num }
      hsq := lam_hsq 58 (by norm_num)
      hnm := (lam_norm_good hL).1
      hnm0 := (lam_norm_good hL).2 }
  hrp := by norm_num
  hUk := by norm_num
  p5 := by norm_num

/-- The general LP2 theorem, applied to the lambda-like frame at `p = 29`. -/
example (Fr : Frame) (hL : LamData Fr 1) :
    GLE 29 (∑ a, uPot 29 25 22 (Frame.hybRow 25 8 a) + ∑ b, uPot 29 25 22 (Frame.hybCol 25 8 b) -
      (8 - (29 - 25))) (Fr.fullPoly 25 8) :=
  (lp2_instance Fr hL).gle (by norm_num)

/-- The general LP1 theorem, applied to the lambda-like frame at `p = 29`. -/
example (Fr : Frame) (hL : LamData Fr 1) :
    GLE 29 (∑ a, wC 29 40 22 (Frame.hybRow 40 9 a) + ∑ b, wC 29 40 22 (Frame.hybCol 40 9 b) -
      (min (29 + 22 - 40) (2 * 9) - 9)) (Fr.fullPoly 40 9) :=
  (lp1_instance Fr hL).gle

end CatalanCore.Uniform.Content.Smith

#print axioms CatalanCore.Uniform.Content.Smith.ptg
#print axioms CatalanCore.Uniform.Content.Smith.pt
#print axioms CatalanCore.Uniform.Content.Smith.pt_loewner
#print axioms CatalanCore.Uniform.Content.Smith.pt_diag
#print axioms CatalanCore.Uniform.Content.Smith.rank_cauchyMat_le
#print axioms CatalanCore.Uniform.Content.Smith.loewner_of_loads
#print axioms CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_derived
#print axioms CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_uf
#print axioms CatalanCore.Uniform.Content.Smith.gamma_reindex
#print axioms CatalanCore.Uniform.Content.Smith.gamma_topExt
#print axioms CatalanCore.Uniform.Content.Smith.weight_transport
#print axioms CatalanCore.Uniform.Content.Smith.weight_topext
#print axioms CatalanCore.Uniform.Content.Smith.twoTermPoleData
#print axioms CatalanCore.Uniform.Content.Smith.LP2Hyp.good_Tg
#print axioms CatalanCore.Uniform.Content.Smith.LP2Hyp.good_Td
#print axioms CatalanCore.Uniform.Content.Smith.schur_scalar
#print axioms CatalanCore.Uniform.Content.Smith.hS_g
#print axioms CatalanCore.Uniform.Content.Smith.LP2Hyp.gleAt
#print axioms CatalanCore.Uniform.Content.Smith.LP2Hyp.gle
#print axioms CatalanCore.Uniform.Content.Smith.LP2Hyp.gle_sub
#print axioms CatalanCore.Arith.Hybrid.HasRankWit.gle_sub
#print axioms CatalanCore.Uniform.Content.Smith.TTCfg2.good_TCgen
#print axioms CatalanCore.Uniform.Content.Smith.LP1Hyp.hred
#print axioms CatalanCore.Uniform.Content.Smith.LP1Hyp.gleAt
#print axioms CatalanCore.Uniform.Content.Smith.LP1Hyp.gle
#print axioms CatalanCore.Uniform.Content.Smith.LP1Hyp.gle_sub
#print axioms CatalanCore.Uniform.Content.Smith.lp2_instance
#print axioms CatalanCore.Uniform.Content.Smith.lp1_instance
#print axioms CatalanCore.Uniform.Content.Smith.ptg_cells
#print axioms CatalanCore.Uniform.Content.Smith.pt_schur
#print axioms CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_uf_loads
