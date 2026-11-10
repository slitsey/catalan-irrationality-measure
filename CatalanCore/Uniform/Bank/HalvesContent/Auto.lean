module

public import CatalanCore.Uniform.Bank.HalvesContent.AutoData
public import CatalanCore.Uniform.Bank.Plane2.TwoTermContent
public import CatalanCore.Uniform.Bank.Halves.Frame
public import CatalanCore.Uniform.Bank.Halves.Final
public import CatalanCore.Uniform.Content.BankShared.Inst.TwoTerm
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
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
      (max (NFr (1 / halves.norm) (-1 / halves.norm) 2 9) 50) bankData.cat := by
  rw [bankData_cat]
  exact CatalanCore.Uniform.Bank.Plane2.TwoTermContent.halves_catValid_c3_10
    depth bankWins bankPres

theorem halves_preValid (depth : ℕ) :
    PreValid (3 / 10) three_tenths_pos halves depth 2
      (SmallBudget.add (SmallBudget.sqrtLog 5 56) SmallBudget.unit) (qq 1 1000) (qq 23 10) := by
  simpa [qq] using
    CatalanCore.Uniform.Bank.Plane2.TwoTermContent.halves_preValid_c3_10 depth

theorem halves_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((FH.family halves depth).restrictAdm (fun i => i.1 % 2 = 0)) FH.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (3 / 10) three_tenths_pos (by norm_num) (by decide +kernel)
    halves depth hd cFr_halves 1 (by decide) _ _ (halves_catValid depth) (halves_preValid depth)

end CatalanCore.Uniform.Bank.HalvesContent.Auto

#print axioms CatalanCore.Uniform.Bank.HalvesContent.Auto.halves_catValid
#print axioms CatalanCore.Uniform.Bank.HalvesContent.Auto.halves_preValid
#print axioms CatalanCore.Uniform.Bank.HalvesContent.Auto.halves_content_auto
