import CatalanCore.Uniform.Bank.HalvesContent.AutoData
import CatalanCore.Uniform.Bank.Halves.Frame
import CatalanCore.Uniform.Bank.Halves.Final
import CatalanCore.Uniform.Content.BankShared.Inst.TwoTerm
import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
import CatalanCore.Arith.Hybrid.PieceTools
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.HalvesContent.Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.Inst
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.Smith

theorem cFr_halves : cFr halves ≤ 16 := by decide +kernel

theorem halves_catValid (depth : ℕ) :
    CatValid (3 / 10) three_tenths_pos halves depth 2 1 4
      (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 9) 50) bankData.cat :=
  catValid_bankUF (twoTermInst halves_shift)
    (twoTerm_arithmetic_small halves_shift (by norm_num) (by norm_num) (by norm_num)).L_eq
    (twoTerm_levels halves_shift) (3 / 10) three_tenths_pos (by norm_num) halves_twoTerm
    (nm := 2 * 2) (by norm_num [halves, CatalanFrames.Thirds.thirdsFrame]) depth 4 9 50
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (twoTerm_hP halves_shift (by norm_num) (by norm_num)) (twoTerm_hkq halves_shift (by norm_num))
    [(3, 4), (4, 4), (4, 5), (5, 5), (5, 6), (6, 6), (6, 7), (7, 7), (7, 8)]

theorem halves_preValid (depth : ℕ) :
    PreValid (3 / 10) three_tenths_pos halves depth 2
      (SmallBudget.add (SmallBudget.sqrtLog 5 56) SmallBudget.unit) (qq 1 1000) (qq 23 10) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (3 / 10) three_tenths_pos 3 10 (by norm_num) (by norm_num) hr2
  have hR : (10 : ℝ) * (2 * ((altGeom (3 / 10) three_tenths_pos).borderSize i.1 : ℝ)) < 3 * i.1 + 10 := by
    exact_mod_cast hb2
  have hbad : p ∈ (twoTermInst halves_shift).cd.bad → p * p ≤ 5 * i.1 := by
    intro hpb
    have hp_le : p ≤ 2 := twoTerm_bad_le halves_shift hpb
    have : p * p ≤ 2 * 2 := Nat.mul_le_mul hp_le hp_le
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any (twoTermInst halves_shift)
    (twoTerm_arithmetic_small halves_shift (by norm_num) (by norm_num) (by norm_num)).L_eq
    (3 / 10) three_tenths_pos (by norm_num) depth i hr2 (by omega) p 5 56 3 16 (23 / 10)
    (by norm_num) cFr_halves (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 23 10 : ℚ) : ℝ) = 23 / 10 := by norm_num [qq]
  rw [e2]
  exact hle

theorem halves_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((FH.family halves depth).restrictAdm (fun i => i.1 % 2 = 0)) FH.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (3 / 10) three_tenths_pos (by norm_num) (by decide +kernel)
    halves depth hd cFr_halves 1 (by decide) _ _ (halves_catValid depth) (halves_preValid depth)

end CatalanCore.Uniform.Bank.HalvesContent.Auto
