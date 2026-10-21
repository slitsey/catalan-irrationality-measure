module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line53m0 : Macro := { x0 := (974588477440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8688849207619806692933763524),(4685085426511611894779674624),(4894682408366889172992),(0),(886973340089086509056),(4227219436384164)), boxes := [
    (((974554923008),(974622031872),(0),(0)),((649703282005),(649748021248),(-7297139298),(0)))
] }
theorem Line53m0_far : farOK pts Line53m0 := by decide +kernel
theorem Line53m0_ok : axisOK pts Line53m0 = true := by decide +kernel
def Line53m1 : Macro := { x0 := (974655586304), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8697999243853669890503062322),(4684814042842334244068786176),(4894970638743040884736),(0),(886973340089086509056),(4226715123208818)), boxes := [
    (((974622031872),(974689140736),(0),(0)),((649748021248),(649792760491),(-7297131695),(0)))
] }
theorem Line53m1_far : farOK pts Line53m1 := by decide +kernel
theorem Line53m1_ok : axisOK pts Line53m1 = true := by decide +kernel
def Line53m2 : Macro := { x0 := (974722695168), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8707145144614358022650954800),(4684542802296309440138510336),(4895258869119192596480),(0),(886973340089086509056),(4226211001298141)), boxes := [
    (((974689140736),(974756249600),(0),(0)),((649792760490),(649837499734),(-7297123617),(0)))
] }
theorem Line53m2_far : farOK pts Line53m2 := by decide +kernel
theorem Line53m2_ok : axisOK pts Line53m2 = true := by decide +kernel
def Line53m3 : Macro := { x0 := (974789804032), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8716292252509756494905954094),(4684271405866603974248038400),(4895547099495344308224),(0),(886973340089086509056),(4225706807814082)), boxes := [
    (((974756249600),(974823358464),(0),(0)),((649837499733),(649882238976),(-7297115808),(0)))
] }
theorem Line53m3_far : farOK pts Line53m3 := by decide +kernel
theorem Line53m3_ok : axisOK pts Line53m3 = true := by decide +kernel
def Line53m4 : Macro := { x0 := (974856912896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8725441342333031387552842336),(4684000084003357276514353152),(4895835329871496019968),(0),(886973340089086509056),(4225202730294699)), boxes := [
    (((974823358464),(974890467328),(0),(0)),((649882238976),(649926978219),(-7297107792),(0)))
] }
theorem Line53m4_far : farOK pts Line53m4 := by decide +kernel
theorem Line53m4_ok : axisOK pts Line53m4 = true := by decide +kernel
def Line53m5 : Macro := { x0 := (974924021760), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8734581821456983772399032616),(4683728897634696793041010688),(4896123560247647731712),(0),(886973340089086509056),(4224698840298505)), boxes := [
    (((974890467328),(974957576192),(0),(0)),((649926978218),(649971717462),(-7297099651),(0)))
] }
theorem Line53m5_far : farOK pts Line53m5 := by decide +kernel
theorem Line53m5_ok : axisOK pts Line53m5 = true := by decide +kernel
def Line53m6 : Macro := { x0 := (974991130624), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8743725329002327446696238458),(4683457435766522085797396480),(4896411790623799443456),(0),(886973340089086509056),(4224194771923494)), boxes := [
    (((974957576192),(975024685056),(0),(0)),((649971717461),(650016456704),(-7297091715),(0)))
] }
theorem Line53m6_far : farOK pts Line53m6 := by decide +kernel
theorem Line53m6_ok : axisOK pts Line53m6 = true := by decide +kernel
def Line53m7 : Macro := { x0 := (975058239488), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8752868106905149216678740752),(4683186487767296373874753536),(4896700020999951155200),(0),(886973340089086509056),(4223691222967141)), boxes := [
    (((975024685056),(975091793920),(0),(0)),((650016456704),(650061195947),(-7297083231),(0)))
] }
theorem Line53m7_far : farOK pts Line53m7 := by decide +kernel
theorem Line53m7_ok : axisOK pts Line53m7 = true := by decide +kernel
def Line53Data : List Macro := [Line53m0,Line53m1,Line53m2,Line53m3,Line53m4,Line53m5,Line53m6,Line53m7]
theorem Line53_farAll : ∀ m ∈ Line53Data, farOK pts m := by
  intro m hm
  simp only [Line53Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line53m0_far,Line53m1_far,Line53m2_far,Line53m3_far,Line53m4_far,Line53m5_far,Line53m6_far,Line53m7_far]
theorem Line53_okAll : ∀ m ∈ Line53Data, axisOK pts m = true := by
  intro m hm
  simp only [Line53Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line53m0_ok,Line53m1_ok,Line53m2_ok,Line53m3_ok,Line53m4_ok,Line53m5_ok,Line53m6_ok,Line53m7_ok]
end CatalanCore.Cert.SigmaQuarter
