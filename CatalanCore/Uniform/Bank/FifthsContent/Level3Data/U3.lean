module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U3O000
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U3O001
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U3O002
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U3O003
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U3O004

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcRawSeeds3 : List (CatalogueSeed pcLegacyCatalogue) := pcRawSeeds3O000 ++ pcRawSeeds3O001 ++ pcRawSeeds3O002 ++ pcRawSeeds3O003 ++ pcRawSeeds3O004
theorem pcRawSeeds3_ok : ∀ S∈pcRawSeeds3,
    seedOK (pcHead 1) (S.law.palette 0) 3 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds3,List.mem_append,or_assoc] at hS
  rcases hS with hS | hS | hS | hS | hS
  · exact pcRawSeeds3O000_ok S hS
  · exact pcRawSeeds3O001_ok S hS
  · exact pcRawSeeds3O002_ok S hS
  · exact pcRawSeeds3O003_ok S hS
  · exact pcRawSeeds3O004_ok S hS
def pcUnsortedHead3 := pcRawSeeds3.flatMap (CatalogueSeed.pieces 9 1 10000 bankHead.cF)
def pcHead3 := sortFuel (fun x y : QPiece × Cert => decide (x.1.s≤y.1.s)) pcUnsortedHead3.length pcUnsortedHead3
theorem pcHead3_eq : pcHead3=catalogueHead 9 1 10000 bankHead.cF pcRawSeeds3 :=
  sortFuel_eq_mergeSort _ _ _ le_rfl

def pcCellBase3_0 : QPiece × Cert := (⟨(qq (1) 234), (qq (2) 459), (qq (7) 3), (qq (-26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (608400) 1)⟩)
def pcCellBase3_1 : QPiece × Cert := (⟨(qq (2) 459), (qq (1) 225), (qq (19) 9), (qq (25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (585225) 1)⟩)
def pcCells3 : List (QPiece × Cert) := [pcCellBase3_0, pcCellBase3_1]
def pcTmpl3 : KTmplP := ⟨1/1350, 125, 0, pcCells3, pcHead3, 91⟩
def tmpl3 : QTmpl := (pcTmpl3.toK 9 20 bankHead.cF).toQ
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.tmpl3

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.pcRawSeeds3_ok
