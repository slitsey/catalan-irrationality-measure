module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line5m0 : Macro := { x0 := (942476886016), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4248449637170133411516735063),(4818653301880071476414644224),(4756764173378295103488),(0),(886973340089086509056),(4479340081016357)), boxes := [
    (((942208450560),(942745321472),(0),(0)),((628138967040),(628496880982),(-7292148822),(0)))
] }
theorem Line5m0_far : farOK pts Line5m0 := by decide +kernel
theorem Line5m0_ok : axisOK pts Line5m0 = true := by decide +kernel
def Line5m1 : Macro := { x0 := (943013756928), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4323721306077848594825118690),(4816357566731198277646942208),(4759070016387508797440),(0),(886973340089086509056),(4474940640370740)), boxes := [
    (((942745321472),(943282192384),(0),(0)),((628496880981),(628854794923),(-7292516393),(0)))
] }
theorem Line5m1_far : farOK pts Line5m1 := by decide +kernel
theorem Line5m1_ok : axisOK pts Line5m1 = true := by decide +kernel
def Line5m2 : Macro := { x0 := (943550627840), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4398967452596578201017310259),(4814063887495461014756327424),(4761375859396722491392),(0),(886973340089086509056),(4470547604416622)), boxes := [
    (((943282192384),(943819063296),(0),(0)),((628854794922),(629212708864),(-7292874892),(0)))
] }
theorem Line5m2_far : farOK pts Line5m2 := by decide +kernel
theorem Line5m2_ok : axisOK pts Line5m2 = true := by decide +kernel
def Line5m3 : Macro := { x0 := (944087498752), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4474150046422667427061347093),(4811772682351806723038445568),(4763681702405936185344),(0),(886973340089086509056),(4466161300141239)), boxes := [
    (((943819063296),(944355934208),(0),(0)),((629212708864),(629570622806),(-7293233635),(0)))
] }
theorem Line5m3_far : farOK pts Line5m3 := by decide +kernel
theorem Line5m3_ok : axisOK pts Line5m3 = true := by decide +kernel
def Line5m4 : Macro := { x0 := (944624369664), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4549330820953698603119596110),(4809483486755258114951282688),(4765987545415149879296),(0),(886973340089086509056),(4461781339985271)), boxes := [
    (((944355934208),(944892805120),(0),(0)),((629570622805),(629928536747),(-7293577476),(0)))
] }
theorem Line5m4_far : farOK pts Line5m4 := by decide +kernel
theorem Line5m4_ok : axisOK pts Line5m4 = true := by decide +kernel
def Line5m5 : Macro := { x0 := (945161240576), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4624457802200595006782148482),(4807196560480277315381952512),(4768293388424363573248),(0),(886973340089086509056),(4457407914682403)), boxes := [
    (((944892805120),(945429676032),(0),(0)),((629928536746),(630286450688),(-7293921762),(0)))
] }
theorem Line5m5_far : farOK pts Line5m5 := by decide +kernel
theorem Line5m5_ok : axisOK pts Line5m5 = true := by decide +kernel
def Line5m6 : Macro := { x0 := (945698111488), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4699562411451899633408987986),(4804911575296893333435121664),(4770599231433577267200),(0),(886973340089086509056),(4453040727381041)), boxes := [
    (((945429676032),(945966546944),(0),(0)),((630286450688),(630644364630),(-7294252692),(0)))
] }
theorem Line5m6_far : farOK pts Line5m6 := by decide +kernel
theorem Line5m6_ok : axisOK pts Line5m6 = true := by decide +kernel
def Line5m7 : Macro := { x0 := (946234982400), y0 := (0), i0 := 1200, i1 := 1200, fd := ((4774604528431955097209924978),(4802628861203659716170022912),(4772905074442790961152),(0),(886973340089086509056),(4448680087355408)), boxes := [
    (((945966546944),(946503417856),(0),(0)),((630644364629),(631002278571),(-7294576703),(0)))
] }
theorem Line5m7_far : farOK pts Line5m7 := by decide +kernel
theorem Line5m7_ok : axisOK pts Line5m7 = true := by decide +kernel
def Line5Data : List Macro := [Line5m0,Line5m1,Line5m2,Line5m3,Line5m4,Line5m5,Line5m6,Line5m7]
theorem Line5_farAll : ∀ m ∈ Line5Data, farOK pts m := by
  intro m hm
  simp only [Line5Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line5m0_far,Line5m1_far,Line5m2_far,Line5m3_far,Line5m4_far,Line5m5_far,Line5m6_far,Line5m7_far]
theorem Line5_okAll : ∀ m ∈ Line5Data, axisOK pts m = true := by
  intro m hm
  simp only [Line5Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line5m0_ok,Line5m1_ok,Line5m2_ok,Line5m3_ok,Line5m4_ok,Line5m5_ok,Line5m6_ok,Line5m7_ok]
end CatalanCore.Cert.SigmaQuarter
