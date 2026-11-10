module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U1O000
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U1O001
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U1O002
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U1O003
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U1O004

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcRawSeeds1 : List (CatalogueSeed pcLegacyCatalogue) := pcRawSeeds1O000 ++ pcRawSeeds1O001 ++ pcRawSeeds1O002 ++ pcRawSeeds1O003 ++ pcRawSeeds1O004
theorem pcRawSeeds1_ok : ∀ S∈pcRawSeeds1,
    seedOK (pcHead 1) (S.law.palette 0) 1 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds1,List.mem_append,or_assoc] at hS
  rcases hS with hS | hS | hS | hS | hS
  · exact pcRawSeeds1O000_ok S hS
  · exact pcRawSeeds1O001_ok S hS
  · exact pcRawSeeds1O002_ok S hS
  · exact pcRawSeeds1O003_ok S hS
  · exact pcRawSeeds1O004_ok S hS
def pcUnsortedHead1 := pcRawSeeds1.flatMap (CatalogueSeed.pieces 9 1 10000 bankHead.cF)
def pcHead1 := sortFuel (fun x y : QPiece × Cert => decide (x.1.s≤y.1.s)) pcUnsortedHead1.length pcUnsortedHead1
theorem pcHead1_eq : pcHead1=catalogueHead 9 1 10000 bankHead.cF pcRawSeeds1 :=
  sortFuel_eq_mergeSort _ _ _ le_rfl

def pcCellBase1_0 : QPiece × Cert := (⟨(qq (1) 234), (qq (2) 459), (qq (7) 3), (qq (-26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (608400) 1)⟩)
def pcCellBase1_1 : QPiece × Cert := (⟨(qq (2) 459), (qq (1) 225), (qq (19) 9), (qq (25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (585225) 1)⟩)
def pcCells1 : List (QPiece × Cert) := [pcCellBase1_0, pcCellBase1_1]
def pcTmpl1 : KTmplP := ⟨1/1350, 125, 0, pcCells1, pcHead1, 91⟩
def tmpl1 : QTmpl := (pcTmpl1.toK 9 20 bankHead.cF).toQ
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.tmpl1

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.pcRawSeeds1_ok
