module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def RayCostPilotm0 : Macro := { x0 := (-297990199706), y0 := (564117110784), i0 := 26, i1 := 1358, fd := ((-2466920946464678432503689421),(-397966357030294339112035424),(360997837942971868444),(478432179279853100165365760),(257851028966312116224),(848233928745346)), boxes := [
    (((-274233662874),(-273428354457),(490431578112),(492847497216)),((-182822441916),(-182285569638),(326954385408),(328564998144))),
    (((-275038969242),(-274233660825),(492847497216),(495263416320)),((-183359312828),(-182822440550),(328564998144),(330175610880))),
    (((-275844275610),(-275038967193),(495263416320),(497679335424)),((-183896183740),(-183359311462),(330175610880),(331786223616))),
    (((-277454888346),(-275844273561),(497679335424),(502511173632)),((-184969925564),(-183896182374),(331786223616),(335007449088)))
] }
theorem RayCostPilotm0_far : farOK pts RayCostPilotm0 := by decide +kernel
theorem RayCostPilotm0_ok : rayOK pts (231169 / 100000) RayCostPilotm0 = true := by decide +kernel
def RayCostPilotData : List Macro := [RayCostPilotm0]
theorem RayCostPilot_farAll : ∀ m ∈ RayCostPilotData, farOK pts m := by
  intro m hm
  simp only [RayCostPilotData, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [RayCostPilotm0_far]
theorem RayCostPilot_okAll : ∀ m ∈ RayCostPilotData, rayOK pts (231169 / 100000) m = true := by
  intro m hm
  simp only [RayCostPilotData, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [RayCostPilotm0_ok]
end CatalanCore.Cert.SigmaQuarter
