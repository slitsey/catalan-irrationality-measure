module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line55m0 : Macro := { x0 := (975662219264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8835181130652013175998044739),(4680747279869521371912798208),(4899294094385316560896),(0),(886973340089086509056),(4219161477662215)), boxes := [
    (((975628664832),(975695773696),(0),(0)),((650419109888),(650463849131),(-7297006735),(0)))
] }
theorem Line55m0_far : farOK pts Line55m0 := by decide +kernel
theorem Line55m0_ok : axisOK pts Line55m0 = true := by decide +kernel
def Line55m1 : Macro := { x0 := (975729328128), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8844325642229876889427321871),(4680476216901199170406580224),(4899582324761468272640),(0),(886973340089086509056),(4218658458200951)), boxes := [
    (((975695773696),(975762882560),(0),(0)),((650463849130),(650508588374),(-7296997315),(0)))
] }
theorem Line55m1_far : farOK pts Line55m1 := by decide +kernel
theorem Line55m1_ok : axisOK pts Line55m1 = true := by decide +kernel
def Line55m2 : Macro := { x0 := (975796436992), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8853466038557701115835477787),(4680205447349862199680630784),(4899870555137619984384),(0),(886973340089086509056),(4218155745031361)), boxes := [
    (((975762882560),(975829991424),(0),(0)),((650508588373),(650553327616),(-7296987247),(0)))
] }
theorem Line55m2_far : farOK pts Line55m2 := by decide +kernel
theorem Line55m2_ok : axisOK pts Line55m2 = true := by decide +kernel
def Line55m3 : Macro := { x0 := (975863545856), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8862612223006372117462248816),(4679934745749543738063978496),(4900158785513771696128),(0),(886973340089086509056),(4217653162297339)), boxes := [
    (((975829991424),(975897100288),(0),(0)),((650553327616),(650598066859),(-7296977773),(0)))
] }
theorem Line55m3_far : farOK pts Line55m3 := by decide +kernel
theorem Line55m3_ok : axisOK pts Line55m3 = true := by decide +kernel
def Line55m4 : Macro := { x0 := (975930654720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8871745493889981906882237022),(4679663759619803556211982336),(4900447015889923407872),(0),(886973340089086509056),(4217150388565872)), boxes := [
    (((975897100288),(975964209152),(0),(0)),((650598066858),(650642806102),(-7296967422),(0)))
] }
theorem Line55m4_far : farOK pts Line55m4 := by decide +kernel
theorem Line55m4_ok : axisOK pts Line55m4 = true := by decide +kernel
def Line55m5 : Macro := { x0 := (975997763584), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8880894201998917068391121477),(4679393291095344009119858688),(4900735246266075119616),(0),(886973340089086509056),(4216648144278433)), boxes := [
    (((975964209152),(976031318016),(0),(0)),((650642806101),(650687545344),(-7296957921),(0)))
] }
theorem Line55m5_far : farOK pts Line55m5 := by decide +kernel
theorem Line55m5_ok : axisOK pts Line55m5 = true := by decide +kernel
def Line55m6 : Macro := { x0 := (976064872448), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8890026785753811971623535433),(4679122346996647733244264448),(4901023476642226831360),(0),(886973340089086509056),(4216145528723350)), boxes := [
    (((976031318016),(976098426880),(0),(0)),((650687545344),(650732284587),(-7296947506),(0)))
] }
theorem Line55m6_far : farOK pts Line55m6 := by decide +kernel
theorem Line55m6_ok : axisOK pts Line55m6 = true := by decide +kernel
def Line55m7 : Macro := { x0 := (976131981312), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8899166580896410478839074235),(4678851637852845207643750400),(4901311707018378543104),(0),(886973340089086509056),(4215643188826837)), boxes := [
    (((976098426880),(976165535744),(0),(0)),((650732284586),(650777023830),(-7296937591),(0)))
] }
theorem Line55m7_far : farOK pts Line55m7 := by decide +kernel
theorem Line55m7_ok : axisOK pts Line55m7 = true := by decide +kernel
def Line55Data : List Macro := [Line55m0,Line55m1,Line55m2,Line55m3,Line55m4,Line55m5,Line55m6,Line55m7]
theorem Line55_farAll : ∀ m ∈ Line55Data, farOK pts m := by
  intro m hm
  simp only [Line55Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line55m0_far,Line55m1_far,Line55m2_far,Line55m3_far,Line55m4_far,Line55m5_far,Line55m6_far,Line55m7_far]
theorem Line55_okAll : ∀ m ∈ Line55Data, axisOK pts m = true := by
  intro m hm
  simp only [Line55Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line55m0_ok,Line55m1_ok,Line55m2_ok,Line55m3_ok,Line55m4_ok,Line55m5_ok,Line55m6_ok,Line55m7_ok]
end CatalanCore.Cert.SigmaQuarter
