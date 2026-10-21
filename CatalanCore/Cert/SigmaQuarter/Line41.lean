module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line41m0 : Macro := { x0 := (971316920320), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8242119890191712888485042270),(4698353399486054007533993984),(4880631177529493225472),(0),(886973340089086509056),(4251914801752512)), boxes := [
    (((971300143104),(971333697536),(0),(0)),((647533428736),(647555798358),(-7297032479),(0)))
] }
theorem Line41m0_far : farOK pts Line41m0 := by decide +kernel
theorem Line41m0_ok : axisOK pts Line41m0 = true := by decide +kernel
def Line41m1 : Macro := { x0 := (971350474752), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8246708024041274066887835332),(4698216849610481099670290432),(4880775292717569081344),(0),(886973340089086509056),(4251660350202151)), boxes := [
    (((971333697536),(971367251968),(0),(0)),((647555798357),(647578167979),(-7297031721),(0)))
] }
theorem Line41m1_far : farOK pts Line41m1 := by decide +kernel
theorem Line41m1_ok : axisOK pts Line41m1 = true := by decide +kernel
def Line41m2 : Macro := { x0 := (971384029184), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8251290083709833373788822587),(4698080352968515202573795328),(4880919407905644937216),(0),(886973340089086509056),(4251405935634424)), boxes := [
    (((971367251968),(971400806400),(0),(0)),((647578167978),(647600537600),(-7297027442),(0)))
] }
theorem Line41m2_far : farOK pts Line41m2 := by decide +kernel
theorem Line41m2_ok : axisOK pts Line41m2 = true := by decide +kernel
def Line41m3 : Macro := { x0 := (971417583616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8255880376777994540175909537),(4697943985909346211829121024),(4881063523093720793088),(0),(886973340089086509056),(4251151665531945)), boxes := [
    (((971400806400),(971434360832),(0),(0)),((647600537600),(647622907222),(-7297026470),(0)))
] }
theorem Line41m3_far : farOK pts Line41m3 := by decide +kernel
theorem Line41m3_ok : axisOK pts Line41m3 = true := by decide +kernel
def Line41m4 : Macro := { x0 := (971451138048), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8260467945584870716123543827),(4697807481908541652464238592),(4881207638281796648960),(0),(886973340089086509056),(4250897292360241)), boxes := [
    (((971434360832),(971467915264),(0),(0)),((647622907221),(647645276843),(-7297025431),(0)))
] }
theorem Line41m4_far : farOK pts Line41m4 := by decide +kernel
theorem Line41m4_ok : axisOK pts Line41m4 = true := by decide +kernel
def Line41m5 : Macro := { x0 := (971484692480), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8265055432730812117626441088),(4697671081440947707752808448),(4881351753469872504832),(0),(886973340089086509056),(4250643024656316)), boxes := [
    (((971467915264),(971501469696),(0),(0)),((647645276842),(647667646464),(-7297024415),(0)))
] }
theorem Line41m5_far : farOK pts Line41m5 := by decide +kernel
theorem Line41m5_ok : axisOK pts Line41m5 = true := by decide +kernel
def Line41m6 : Macro := { x0 := (971518246912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8269644480597289169954655719),(4697534561048324573960667136),(4881495868657948360704),(0),(886973340089086509056),(4250388677995508)), boxes := [
    (((971501469696),(971535024128),(0),(0)),((647667646464),(647690016086),(-7297023113),(0)))
] }
theorem Line41m6_far : farOK pts Line41m6 := by decide +kernel
theorem Line41m6_ok : axisOK pts Line41m6 = true := by decide +kernel
def Line41m7 : Macro := { x0 := (971551801344), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8274232848613433302250146632),(4697398226403958803971440640),(4881639983846024216576),(0),(886973340089086509056),(4250134486966110)), boxes := [
    (((971535024128),(971568578560),(0),(0)),((647690016085),(647712385707),(-7297022028),(0)))
] }
theorem Line41m7_far : farOK pts Line41m7 := by decide +kernel
theorem Line41m7_ok : axisOK pts Line41m7 = true := by decide +kernel
def Line41Data : List Macro := [Line41m0,Line41m1,Line41m2,Line41m3,Line41m4,Line41m5,Line41m6,Line41m7]
theorem Line41_farAll : ∀ m ∈ Line41Data, farOK pts m := by
  intro m hm
  simp only [Line41Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line41m0_far,Line41m1_far,Line41m2_far,Line41m3_far,Line41m4_far,Line41m5_far,Line41m6_far,Line41m7_far]
theorem Line41_okAll : ∀ m ∈ Line41Data, axisOK pts m = true := by
  intro m hm
  simp only [Line41Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line41m0_ok,Line41m1_ok,Line41m2_ok,Line41m3_ok,Line41m4_ok,Line41m5_ok,Line41m6_ok,Line41m7_ok]
end CatalanCore.Cert.SigmaQuarter
