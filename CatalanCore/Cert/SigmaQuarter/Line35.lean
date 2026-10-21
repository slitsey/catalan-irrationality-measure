module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line35m0 : Macro := { x0 := (969706307584), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8021725628357315777871328883),(4704913009030170272464502784),(4873713648501852143616),(0),(886973340089086509056),(4264152421498775)), boxes := [
    (((969689530368),(969723084800),(0),(0)),((646459686912),(646482056534),(-7297034041),(0)))
] }
theorem Line35m0_far : farOK pts Line35m0 := by decide +kernel
theorem Line35m0_ok : axisOK pts Line35m0 = true := by decide +kernel
def Line35m1 : Macro := { x0 := (969739862016), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8026318525638714030536541487),(4704775894317215421630709760),(4873857763689927999488),(0),(886973340089086509056),(4263896698516512)), boxes := [
    (((969723084800),(969756639232),(0),(0)),((646482056533),(646504426155),(-7297038281),(0)))
] }
theorem Line35m1_far : farOK pts Line35m1 := by decide +kernel
theorem Line35m1_ok : axisOK pts Line35m1 = true := by decide +kernel
def Line35m2 : Macro := { x0 := (969773416448), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8030909207743910367372835376),(4704639149792519774718328832),(4874001878878003855360),(0),(886973340089086509056),(4263641320886290)), boxes := [
    (((969756639232),(969790193664),(0),(0)),((646504426154),(646526795776),(-7297038576),(0)))
] }
theorem Line35m2_far : farOK pts Line35m2 := by decide +kernel
theorem Line35m2_ok : axisOK pts Line35m2 = true := by decide +kernel
def Line35m3 : Macro := { x0 := (969806970880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8035501307404106028681468851),(4704502257098077631784878080),(4874145994066079711232),(0),(886973340089086509056),(4263385801920490)), boxes := [
    (((969790193664),(969823748096),(0),(0)),((646526795776),(646549165398),(-7297038565),(0)))
] }
theorem Line35m3_far : farOK pts Line35m3 := by decide +kernel
theorem Line35m3_ok : axisOK pts Line35m3 = true := by decide +kernel
def Line35m4 : Macro := { x0 := (969840525312), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8040096208202792201159876389),(4704365515550860773130174464),(4874290109254155567104),(0),(886973340089086509056),(4263130459825687)), boxes := [
    (((969823748096),(969857302528),(0),(0)),((646549165397),(646571535019),(-7297038908),(0)))
] }
theorem Line35m4_far : farOK pts Line35m4 := by decide +kernel
theorem Line35m4_ok : axisOK pts Line35m4 = true := by decide +kernel
def Line35m5 : Macro := { x0 := (969874079744), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8044689926506790430320662817),(4704228650001210399832473600),(4874434224442231422976),(0),(886973340089086509056),(4262875010057878)), boxes := [
    (((969857302528),(969890856960),(0),(0)),((646571535018),(646593904640),(-7297039236),(0)))
] }
theorem Line35m5_far : farOK pts Line35m5 := by decide +kernel
theorem Line35m5_ok : axisOK pts Line35m5 = true := by decide +kernel
def Line35m6 : Macro := { x0 := (969907634176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8049286074111451535549079835),(4704091888461169164600016896),(4874578339630307278848),(0),(886973340089086509056),(4262619678654067)), boxes := [
    (((969890856960),(969924411392),(0),(0)),((646593904640),(646616274262),(-7297039671),(0)))
] }
theorem Line35m6_far : farOK pts Line35m6 := by decide +kernel
theorem Line35m6_ok : axisOK pts Line35m6 = true := by decide +kernel
def Line35m7 : Macro := { x0 := (969941188608), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8053885178261407795531050004),(4703955260358112117453684736),(4874722454818383134720),(0),(886973340089086509056),(4262364472813236)), boxes := [
    (((969924411392),(969957965824),(0),(0)),((646616274261),(646638643883),(-7297039887),(0)))
] }
theorem Line35m7_far : farOK pts Line35m7 := by decide +kernel
theorem Line35m7_ok : axisOK pts Line35m7 = true := by decide +kernel
def Line35Data : List Macro := [Line35m0,Line35m1,Line35m2,Line35m3,Line35m4,Line35m5,Line35m6,Line35m7]
theorem Line35_farAll : ∀ m ∈ Line35Data, farOK pts m := by
  intro m hm
  simp only [Line35Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line35m0_far,Line35m1_far,Line35m2_far,Line35m3_far,Line35m4_far,Line35m5_far,Line35m6_far,Line35m7_far]
theorem Line35_okAll : ∀ m ∈ Line35Data, axisOK pts m = true := by
  intro m hm
  simp only [Line35Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line35m0_ok,Line35m1_ok,Line35m2_ok,Line35m3_ok,Line35m4_ok,Line35m5_ok,Line35m6_ok,Line35m7_ok]
end CatalanCore.Cert.SigmaQuarter
