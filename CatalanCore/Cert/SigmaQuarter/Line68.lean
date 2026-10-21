module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line68m0 : Macro := { x0 := (990795268096), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10883402031206997624494538895),(4620449481682850490454441984),(4964290044207527559168),(0),(886973340089086509056),(4108010919432468)), boxes := [
    (((990526832640),(991063703552),(0),(0)),((660351221760),(660709135702),(-7296449724),(0)))
] }
theorem Line68m0_far : farOK pts Line68m0 := by decide +kernel
theorem Line68m0_ok : axisOK pts Line68m0 = true := by decide +kernel
def Line68m1 : Macro := { x0 := (991332139008), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10955565566924259248954842878),(4618338910323299948257280000),(4966595887216741253120),(0),(886973340089086509056),(4104148997880971)), boxes := [
    (((991063703552),(991600574464),(0),(0)),((660709135701),(661067049643),(-7296144048),(0)))
] }
theorem Line68m1_far : farOK pts Line68m1 := by decide +kernel
theorem Line68m1_ok : axisOK pts Line68m1 = true := by decide +kernel
def Line68m2 : Macro := { x0 := (991869009920), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11027710978099132530140029408),(4616230285232922922232315904),(4968901730225954947072),(0),(886973340089086509056),(4100292565214334)), boxes := [
    (((991600574464),(992137445376),(0),(0)),((661067049642),(661424963584),(-7295839232),(0)))
] }
theorem Line68m2_far : farOK pts Line68m2 := by decide +kernel
theorem Line68m2_ok : axisOK pts Line68m2 = true := by decide +kernel
def Line68m3 : Macro := { x0 := (992405880832), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11099840374684535199034586984),(4614123309744476269224919040),(4971207573235168641024),(0),(886973340089086509056),(4096441325662728)), boxes := [
    (((992137445376),(992674316288),(0),(0)),((661424963584),(661782877526),(-7295517044),(0)))
] }
theorem Line68m3_far : farOK pts Line68m3 := by decide +kernel
theorem Line68m3_ok : axisOK pts Line68m3 = true := by decide +kernel
def Line68m4 : Macro := { x0 := (992942751744), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11171912122364140276032069347),(4612018527379069835878531072),(4973513416244382334976),(0),(886973340089086509056),(4092595781271798)), boxes := [
    (((992674316288),(993211187200),(0),(0)),((661782877525),(662140791467),(-7295192860),(0)))
] }
theorem Line68m4_far : farOK pts Line68m4 := by decide +kernel
theorem Line68m4_ok : axisOK pts Line68m4 = true := by decide +kernel
def Line68m5 : Macro := { x0 := (993479622656), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11243951432251552306739968588),(4609915554895378247268237312),(4975819259253596028928),(0),(886973340089086509056),(4088755565254619)), boxes := [
    (((993211187200),(993748058112),(0),(0)),((662140791466),(662498705408),(-7294855920),(0)))
] }
theorem Line68m5_far : farOK pts Line68m5 := by decide +kernel
theorem Line68m5_ok : axisOK pts Line68m5 = true := by decide +kernel
def Line68m6 : Macro := { x0 := (994016493568), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11315963028411287667048480325),(4607814643271198461800022016),(4978125102262809722880),(0),(886973340089086509056),(4084920902141767)), boxes := [
    (((993748058112),(994284929024),(0),(0)),((662498705408),(662856619350),(-7294515083),(0)))
] }
theorem Line68m6_far : farOK pts Line68m6 := by decide +kernel
theorem Line68m6_ok : axisOK pts Line68m6 = true := by decide +kernel
def Line68m7 : Macro := { x0 := (994553364480), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11387957996928657385046226105),(4605715510432415134933843968),(4980430945272023416832),(0),(886973340089086509056),(4081091535971004)), boxes := [
    (((994284929024),(994821799936),(0),(0)),((662856619349),(663214533291),(-7294162423),(0)))
] }
theorem Line68m7_far : farOK pts Line68m7 := by decide +kernel
theorem Line68m7_ok : axisOK pts Line68m7 = true := by decide +kernel
def Line68Data : List Macro := [Line68m0,Line68m1,Line68m2,Line68m3,Line68m4,Line68m5,Line68m6,Line68m7]
theorem Line68_farAll : ∀ m ∈ Line68Data, farOK pts m := by
  intro m hm
  simp only [Line68Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line68m0_far,Line68m1_far,Line68m2_far,Line68m3_far,Line68m4_far,Line68m5_far,Line68m6_far,Line68m7_far]
theorem Line68_okAll : ∀ m ∈ Line68Data, axisOK pts m = true := by
  intro m hm
  simp only [Line68Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line68m0_ok,Line68m1_ok,Line68m2_ok,Line68m3_ok,Line68m4_ok,Line68m5_ok,Line68m6_ok,Line68m7_ok]
end CatalanCore.Cert.SigmaQuarter
