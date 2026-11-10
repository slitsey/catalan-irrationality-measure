module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U4O000
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U4O001
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U4O002
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U4O003
public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.PC.U4O004

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcRawSeeds4 : List (CatalogueSeed pcLegacyCatalogue) := pcRawSeeds4O000 ++ pcRawSeeds4O001 ++ pcRawSeeds4O002 ++ pcRawSeeds4O003 ++ pcRawSeeds4O004
theorem pcRawSeeds4_ok : ∀ S∈pcRawSeeds4,
    seedOK (pcHead 1) (S.law.palette 0) 4 pcSeedLimit (S.toSeed 9 1 10000)=true := by
  intro S hS
  simp only [pcRawSeeds4,List.mem_append,or_assoc] at hS
  rcases hS with hS | hS | hS | hS | hS
  · exact pcRawSeeds4O000_ok S hS
  · exact pcRawSeeds4O001_ok S hS
  · exact pcRawSeeds4O002_ok S hS
  · exact pcRawSeeds4O003_ok S hS
  · exact pcRawSeeds4O004_ok S hS
def pcUnsortedHead4 := pcRawSeeds4.flatMap (CatalogueSeed.pieces 9 1 10000 bankHead.cF)
def pcHead4 := sortFuel (fun x y : QPiece × Cert => decide (x.1.s≤y.1.s)) pcUnsortedHead4.length pcUnsortedHead4
theorem pcHead4_eq : pcHead4=catalogueHead 9 1 10000 bankHead.cF pcRawSeeds4 :=
  sortFuel_eq_mergeSort _ _ _ le_rfl

def pcCellBase4_0 : QPiece × Cert := (⟨(qq (1) 234), (qq (2) 459), (qq (7) 3), (qq (-26) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (608400) 1)⟩)
def pcCellBase4_1 : QPiece × Cert := (⟨(qq (2) 459), (qq (1) 225), (qq (19) 9), (qq (25) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (585225) 1)⟩)
def pcCells4 : List (QPiece × Cert) := [pcCellBase4_0, pcCellBase4_1]
def pcTmpl4 : KTmplP := ⟨1/1350, 125, 0, pcCells4, pcHead4, 91⟩
def tmpl4 : QTmpl := (pcTmpl4.toK 9 20 bankHead.cF).toQ
end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.tmpl4

#print axioms CatalanCore.Uniform.Bank.FifthsContent.Level3Auto.pcRawSeeds4_ok
