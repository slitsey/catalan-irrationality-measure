module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line63m0 : Macro := { x0 := (981332918272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9605801319916725750522955975),(4657968495139822853132124160),(4923649561170136203264),(0),(886973340089086509056),(4176985994322902)), boxes := [
    (((981265809408),(981400027136),(0),(0)),((654177206272),(654266684758),(-7296446521),(0)))
] }
theorem Line63m0_far : farOK pts Line63m0 := by decide +kernel
theorem Line63m0_ok : axisOK pts Line63m0 = true := by decide +kernel
def Line63m1 : Macro := { x0 := (981467136000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9623988707641426172466908387),(4657431954422030683686174720),(4924226021922439626752),(0),(886973340089086509056),(4175995392151840)), boxes := [
    (((981400027136),(981534244864),(0),(0)),((654266684757),(654356163243),(-7296406549),(0)))
] }
theorem Line63m1_far : farOK pts Line63m1 := by decide +kernel
theorem Line63m1_ok : axisOK pts Line63m1 = true := by decide +kernel
def Line63m2 : Macro := { x0 := (981601353728), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9642189666117783002841072393),(4656895835024647551382978560),(4924802482674743050240),(0),(886973340089086509056),(4175005401341884)), boxes := [
    (((981534244864),(981668462592),(0),(0)),((654356163242),(654445641728),(-7296369640),(0)))
] }
theorem Line63m2_far : farOK pts Line63m2 := by decide +kernel
theorem Line63m2_ok : axisOK pts Line63m2 = true := by decide +kernel
def Line63m3 : Macro := { x0 := (981735571456), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9660383631789566674356147312),(4656359573591032885173682176),(4925378943427046473728),(0),(886973340089086509056),(4174015525717610)), boxes := [
    (((981668462592),(981802680320),(0),(0)),((654445641728),(654535120214),(-7296328932),(0)))
] }
theorem Line63m3_far : farOK pts Line63m3 := by decide +kernel
theorem Line63m3_ok : axisOK pts Line63m3 = true := by decide +kernel
def Line63m4 : Macro := { x0 := (981869789184), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9678571894192756006439686935),(4655823328000352350858379264),(4925955404179349897216),(0),(886973340089086509056),(4173025910876929)), boxes := [
    (((981802680320),(981936898048),(0),(0)),((654535120213),(654624598699),(-7296287873),(0)))
] }
theorem Line63m4_far : farOK pts Line63m4 := by decide +kernel
theorem Line63m4_ok : axisOK pts Line63m4 = true := by decide +kernel
def Line63m5 : Macro := { x0 := (982004006912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9696761862889318737315494358),(4655287426007306828240977920),(4926531864931653320704),(0),(886973340089086509056),(4172036842444853)), boxes := [
    (((981936898048),(982071115776),(0),(0)),((654624598698),(654714077184),(-7296246715),(0)))
] }
theorem Line63m5_far : farOK pts Line63m5 := by decide +kernel
theorem Line63m5_ok : axisOK pts Line63m5 = true := by decide +kernel
def Line63m6 : Macro := { x0 := (982138224640), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9714951141467946392822916748),(4654751632545776385100283904),(4927108325683956744192),(0),(886973340089086509056),(4171048111915757)), boxes := [
    (((982071115776),(982205333504),(0),(0)),((654714077184),(654803555670),(-7296208418),(0)))
] }
theorem Line63m6_far : farOK pts Line63m6 := by decide +kernel
theorem Line63m6_ok : axisOK pts Line63m6 = true := by decide +kernel
def Line63m7 : Macro := { x0 := (982272442368), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9733137232609868483680472268),(4654216111066914330694647808),(4927684786436260167680),(0),(886973340089086509056),(4170059870643928)), boxes := [
    (((982205333504),(982339551232),(0),(0)),((654803555669),(654893034155),(-7296162874),(0)))
] }
theorem Line63m7_far : farOK pts Line63m7 := by decide +kernel
theorem Line63m7_ok : axisOK pts Line63m7 = true := by decide +kernel
def Line63Data : List Macro := [Line63m0,Line63m1,Line63m2,Line63m3,Line63m4,Line63m5,Line63m6,Line63m7]
theorem Line63_farAll : ∀ m ∈ Line63Data, farOK pts m := by
  intro m hm
  simp only [Line63Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line63m0_far,Line63m1_far,Line63m2_far,Line63m3_far,Line63m4_far,Line63m5_far,Line63m6_far,Line63m7_far]
theorem Line63_okAll : ∀ m ∈ Line63Data, axisOK pts m = true := by
  intro m hm
  simp only [Line63Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line63m0_ok,Line63m1_ok,Line63m2_ok,Line63m3_ok,Line63m4_ok,Line63m5_ok,Line63m6_ok,Line63m7_ok]
end CatalanCore.Cert.SigmaQuarter
