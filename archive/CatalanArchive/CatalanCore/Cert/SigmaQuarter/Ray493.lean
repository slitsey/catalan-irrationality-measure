module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Ray493m0 : Macro := { x0 := (-297990199706), y0 := (564117110784), i0 := 26, i1 := 1358, fd := ((-2466920946464678432503689421),(-397966357030294339112035424),(360997837942971868444),(478432179279853100165365760),(257851028966312116224),(848233928745346)), boxes := [
    (((-287118564762),(-283897337241),(521838526464),(531502202880)),((-191412376508),(-189264891494),(347892350976),(354334801920))),
    (((-290339790234),(-287118562713),(531502202880),(541165879296)),((-193559860156),(-191412375142),(354334801920),(360777252864))),
    (((-293561015706),(-290339788185),(541165879296),(550829555712)),((-195707343804),(-193559858790),(360777252864),(367219703808))),
    (((-296782241178),(-293561013657),(550829555712),(560493232128)),((-197854827452),(-195707342438),(367219703808),(373662154752)))
] }
theorem Ray493m0_far : farOK pts Ray493m0 := by decide +kernel
theorem Ray493m0_ok : rayOK pts (231169 / 100000) Ray493m0 = true := by decide +kernel
def Ray493Data : List Macro := [Ray493m0]
theorem Ray493_farAll : ∀ m ∈ Ray493Data, farOK pts m := by
  intro m hm
  simp only [Ray493Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Ray493m0_far]
theorem Ray493_okAll : ∀ m ∈ Ray493Data, rayOK pts (231169 / 100000) m = true := by
  intro m hm
  simp only [Ray493Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Ray493m0_ok]
end CatalanCore.Cert.SigmaQuarter
