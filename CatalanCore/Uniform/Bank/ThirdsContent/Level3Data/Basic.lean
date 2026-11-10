module

public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.U1
public import CatalanCore.Uniform.Bank.ThirdsContent.Level3Data.U2

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! PC conversion: old head literals and exact Lambda preserved; no repeated translated-tail piece checks. -/
namespace CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

def bankData : BankData := { bankHead with Λ := qq 6933520273187729349014084193375908512293178064351944028577006104461695201428343405804123865436071830152308278147296229379177045260318914832728864723888595294302669410392493264281680408019532778992614033161743464033593068005699181099833165231328807225321295004539691663544363471084062251 2094437091849991561214174188505548492064499739726143498984099533714875252314276429335189987924567215298529571661143966080489657055512241303912442132298641058729954884702719322546093719609031306411916389494843525110787038578717082018255023743016308337180555739298649406376469026560000000, tmpls := [(1, tmpl1), (2, tmpl2)] }

theorem bankData_cat : bankData.cat = ((tableT ++ ([brLP1, brLP2w, brRank, brS] ++
    bankWins.map (fun w => brWin w.1 w.2)) ++ (bankPres.map (fun x => brPre x.1 x.2.1 x.2.2))) ++ [CatalanCore.Uniform.Content.UFSimple.WrapCheck.brWrap]) ++ CatalanCore.Uniform.Content.UFSimple.prefixBranches 24 :=
  by
  simp only [bankData, bankHead, bankExtra, BankData.cat, List.append_assoc]

theorem bankData_Λ : bankData.Λ = (6933520273187729349014084193375908512293178064351944028577006104461695201428343405804123865436071830152308278147296229379177045260318914832728864723888595294302669410392493264281680408019532778992614033161743464033593068005699181099833165231328807225321295004539691663544363471084062251 /
    2094437091849991561214174188505548492064499739726143498984099533714875252314276429335189987924567215298529571661143966080489657055512241303912442132298641058729954884702719322546093719609031306411916389494843525110787038578717082018255023743016308337180555739298649406376469026560000000 : ℚ) := by
  -- kcost: 165.82s measured complete4-offset metadata unit or55.50s/24 complete hard seeds; bounded module/operation count in admission, no hidden branch checks in metadata.
  decide +kernel

def pcTemplates : List (ℕ × KTmplP) := [(1,pcTmpl1), (2,pcTmpl2)]
def pcBank (o : ℕ) : KBankData := { pcHead o with Λ := bankData.Λ, tmpls := pcTemplates.map (fun x => (x.1,x.2.toK 20 46 bankHead.cF)) }

#print axioms bankData_Λ
end CatalanCore.Uniform.Bank.ThirdsContent.Level3Auto
