module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line25m0 : Macro := { x0 := (967021953024), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7653718933153964507279570567),(4715886226385047715851927552),(4862184433455783673856),(0),(886973340089086509056),(4284666391167388)), boxes := [
    (((967005175808),(967038730240),(0),(0)),((644670117205),(644692486827),(-7296898877),(0)))
] }
theorem Line25m0_far : farOK pts Line25m0 := by decide +kernel
theorem Line25m0_ok : axisOK pts Line25m0 = true := by decide +kernel
def Line25m1 : Macro := { x0 := (967055507456), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7658325243961058450047977819),(4715748775934431143533412352),(4862328548643859529728),(0),(886973340089086509056),(4284409078619316)), boxes := [
    (((967038730240),(967072284672),(0),(0)),((644692486826),(644714856448),(-7296901644),(0)))
] }
theorem Line25m1_far : farOK pts Line25m1 := by decide +kernel
theorem Line25m1_ok : axisOK pts Line25m1 = true := by decide +kernel
def Line25m2 : Macro := { x0 := (967089061888), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7662932061649771908233838601),(4715611366665778733290684416),(4862472663831935385600),(0),(886973340089086509056),(4284151816886911)), boxes := [
    (((967072284672),(967105839104),(0),(0)),((644714856448),(644737226070),(-7296904453),(0)))
] }
theorem Line25m2_far : farOK pts Line25m2 := by decide +kernel
theorem Line25m2_ok : axisOK pts Line25m2 = true := by decide +kernel
def Line25m3 : Macro := { x0 := (967122616320), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7667537621407678232139309751),(4715474005447508941699940352),(4862616779020011241472),(0),(886973340089086509056),(4283894611517319)), boxes := [
    (((967105839104),(967139393536),(0),(0)),((644737226069),(644759595691),(-7296906926),(0)))
] }
theorem Line25m3_far : farOK pts Line25m3 := by decide +kernel
theorem Line25m3_ok : axisOK pts Line25m3 = true := by decide +kernel
def Line25m4 : Macro := { x0 := (967156170752), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7672146072850951909387543654),(4715336497309464481573568512),(4862760894208087097344),(0),(886973340089086509056),(4283637296839493)), boxes := [
    (((967139393536),(967172947968),(0),(0)),((644759595690),(644781965312),(-7296909701),(0)))
] }
theorem Line25m4_far : farOK pts Line25m4 := by decide +kernel
theorem Line25m4_ok : axisOK pts Line25m4 = true := by decide +kernel
def Line25m5 : Macro := { x0 := (967189725184), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7676749121900286452866933611),(4715199126193390669226377216),(4862905009396162953216),(0),(886973340089086509056),(4283380108197445)), boxes := [
    (((967172947968),(967206502400),(0),(0)),((644781965312),(644804334934),(-7296912318),(0)))
] }
theorem Line25m5_far : farOK pts Line25m5 := by decide +kernel
theorem Line25m5_ok : axisOK pts Line25m5 = true := by decide +kernel
def Line25m6 : Macro := { x0 := (967223279616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7681349423996001976132726638),(4715061521726649423112634368),(4863049124584238809088),(0),(886973340089086509056),(4283122750031412)), boxes := [
    (((967206502400),(967240056832),(0),(0)),((644804334933),(644826704555),(-7296914865),(0)))
] }
theorem Line25m6_far : farOK pts Line25m6 := by decide +kernel
theorem Line25m6_ok : axisOK pts Line25m6 = true := by decide +kernel
def Line25m7 : Macro := { x0 := (967256834048), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7685956888604274296859881163),(4714924089996626606755545088),(4863193239772314664960),(0),(886973340089086509056),(4282865549121860)), boxes := [
    (((967240056832),(967273611264),(0),(0)),((644826704554),(644849074176),(-7296917384),(0)))
] }
theorem Line25m7_far : farOK pts Line25m7 := by decide +kernel
theorem Line25m7_ok : axisOK pts Line25m7 = true := by decide +kernel
def Line25Data : List Macro := [Line25m0,Line25m1,Line25m2,Line25m3,Line25m4,Line25m5,Line25m6,Line25m7]
theorem Line25_farAll : ∀ m ∈ Line25Data, farOK pts m := by
  intro m hm
  simp only [Line25Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line25m0_far,Line25m1_far,Line25m2_far,Line25m3_far,Line25m4_far,Line25m5_far,Line25m6_far,Line25m7_far]
theorem Line25_okAll : ∀ m ∈ Line25Data, axisOK pts m = true := by
  intro m hm
  simp only [Line25Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line25m0_ok,Line25m1_ok,Line25m2_ok,Line25m3_ok,Line25m4_ok,Line25m5_ok,Line25m6_ok,Line25m7_ok]
end CatalanCore.Cert.SigmaQuarter
