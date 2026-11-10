module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O000
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O001
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O002
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O003
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O004
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O005
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O006
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.PC.U2O007

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcRawSeeds2 : List (CatalogueSeed pcLegacyCatalogue) := pcRawSeeds2O000 ++ pcRawSeeds2O001 ++ pcRawSeeds2O002 ++ pcRawSeeds2O003 ++ pcRawSeeds2O004 ++ pcRawSeeds2O005 ++ pcRawSeeds2O006 ++ pcRawSeeds2O007
theorem pcRawSeeds2_ok : ∀ S∈pcRawSeeds2,
    seedOK (pcHead 1) (S.law.palette 0) 2 pcSeedLimit (S.toSeed 20 3 10000)=true := by
  intro S hS
  simp only [pcRawSeeds2,List.mem_append,or_assoc] at hS
  rcases hS with hS | hS | hS | hS | hS | hS | hS | hS
  · exact pcRawSeeds2O000_ok S hS
  · exact pcRawSeeds2O001_ok S hS
  · exact pcRawSeeds2O002_ok S hS
  · exact pcRawSeeds2O003_ok S hS
  · exact pcRawSeeds2O004_ok S hS
  · exact pcRawSeeds2O005_ok S hS
  · exact pcRawSeeds2O006_ok S hS
  · exact pcRawSeeds2O007_ok S hS
def pcUnsortedHead2 := pcRawSeeds2.flatMap (CatalogueSeed.pieces 20 3 10000 bankHead.cF)
def pcHead2 := sortFuel (fun x y : QPiece × Cert => decide (x.1.s≤y.1.s)) pcUnsortedHead2.length pcUnsortedHead2
theorem pcHead2_eq : pcHead2=catalogueHead 20 3 10000 bankHead.cF pcRawSeeds2 :=
  sortFuel_eq_mergeSort _ _ _ le_rfl

def pcCellBase2_0 : QPiece × Cert := (⟨(qq (1) 200), (qq (3) 590), (qq (49) 20), (qq (-30) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (276000) 1)⟩)
def pcCellBase2_1 : QPiece × Cert := (⟨(qq (3) 590), (qq (3) 580), (qq (43) 20), (qq (29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (800630) 3)⟩)
def pcCellBase2_2 : QPiece × Cert := (⟨(qq (3) 580), (qq (1) 190), (qq (49) 20), (qq (-29) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (773720) 3)⟩)
def pcCellBase2_3 : QPiece × Cert := (⟨(qq (1) 190), (qq (3) 560), (qq (43) 20), (qq (28) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (249090) 1)⟩)
def pcCellBase2_4 : QPiece × Cert := (⟨(qq (3) 560), (qq (3) 550), (qq (49) 20), (qq (-28) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (721280) 3)⟩)
def pcCellBase2_5 : QPiece × Cert := (⟨(qq (3) 550), (qq (1) 180), (qq (43) 20), (qq (27) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (695750) 3)⟩)
def pcCells2 : List (QPiece × Cert) := [pcCellBase2_0, pcCellBase2_1, pcCellBase2_2, pcCellBase2_3, pcCellBase2_4, pcCellBase2_5]
def pcTmpl2 : KTmplP := ⟨1/1000, 41, 0, pcCells2, pcHead2, 90⟩
def tmpl2 : QTmpl := (pcTmpl2.toK 20 46 bankHead.cF).toQ
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto

#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto.tmpl2

#print axioms CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto.pcRawSeeds2_ok
