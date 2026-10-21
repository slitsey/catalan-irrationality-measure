module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line69m0 : Macro := { x0 := (995090235392), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11459897605530982109353877044),(4603618496828843001688162304),(4982736788281237110784),(0),(886973340089086509056),(4077267739530316)), boxes := [
    (((994821799936),(995358670848),(0),(0)),((663214533290),(663572447232),(-7293800991),(0)))
] }
theorem Line69m0_far : farOK pts Line69m0 := by decide +kernel
theorem Line69m0_ok : axisOK pts Line69m0 = true := by decide +kernel
def Line69m1 : Macro := { x0 := (995627106304), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11531811267949272854864596069),(4601523211067959178892148736),(4985042631290450804736),(0),(886973340089086509056),(4073449171987794)), boxes := [
    (((995358670848),(995895541760),(0),(0)),((663572447232),(663930361174),(-7293430961),(0)))
] }
theorem Line69m1_far : farOK pts Line69m1 := by decide +kernel
theorem Line69m1_ok : axisOK pts Line69m1 = true := by decide +kernel
def Line69m2 : Macro := { x0 := (996163977216), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11603686319234957065649678416),(4599429836429375950826700800),(4987348474299664498688),(0),(886973340089086509056),(4069636004305435)), boxes := [
    (((995895541760),(996432412672),(0),(0)),((663930361173),(664288275115),(-7293055787),(0)))
] }
theorem Line69m2_far : farOK pts Line69m2 := by decide +kernel
theorem Line69m2_ok : axisOK pts Line69m2 = true := by decide +kernel
def Line69m3 : Macro := { x0 := (996700848128), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11675550759433634991697391968),(4597338423136568292813045760),(4989654317308878192640),(0),(886973340089086509056),(4065828252490541)), boxes := [
    (((996432412672),(996969283584),(0),(0)),((664288275114),(664646189056),(-7292668641),(0)))
] }
theorem Line69m3_far : farOK pts Line69m3 := by decide +kernel
theorem Line69m3_ok : axisOK pts Line69m3 = true := by decide +kernel
def Line69m4 : Macro := { x0 := (997237719040), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11747348459928029667126198694),(4595248711148836061424320512),(4991960160318091886592),(0),(886973340089086509056),(4062025688144267)), boxes := [
    (((996969283584),(997506154496),(0),(0)),((664646189056),(665004102998),(-7292273837),(0)))
] }
theorem Line69m4_far : farOK pts Line69m4 := by decide +kernel
theorem Line69m4_ok : axisOK pts Line69m4 = true := by decide +kernel
def Line69m5 : Macro := { x0 := (998043025408), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11855029452317692999224290678),(4592118137269843786390306816),(4995418924831912427520),(0),(886973340089086509056),(4056332242791548)), boxes := [
    (((997506154496),(998579896320),(0),(0)),((665004102997),(665719930880),(-7297038072),(0)))
] }
theorem Line69m5_far : farOK pts Line69m5 := by decide +kernel
theorem Line69m5_ok : axisOK pts Line69m5 = true := by decide +kernel
def Line69m6 : Macro := { x0 := (999116767232), y0 := (0), i0 := 1200, i1 := 1200, fd := ((11998460980794751540976483023),(4587950445019224952092884992),(5000030610850339815424),(0),(886973340089086509056),(4048759463383598)), boxes := [
    (((998579896320),(999653638144),(0),(0)),((665719930880),(666435758763),(-7296202494),(0)))
] }
theorem Line69m6_far : farOK pts Line69m6 := by decide +kernel
theorem Line69m6_ok : axisOK pts Line69m6 = true := by decide +kernel
def Line69m7 : Macro := { x0 := (1000190509056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12141775173188152280209502228),(4583790296338073024183533568),(5004642296868767203328),(0),(886973340089086509056),(4041207929352919)), boxes := [
    (((999653638144),(1000727379968),(0),(0)),((666435758762),(667151586646),(-7295332949),(0)))
] }
theorem Line69m7_far : farOK pts Line69m7 := by decide +kernel
theorem Line69m7_ok : axisOK pts Line69m7 = true := by decide +kernel
def Line69Data : List Macro := [Line69m0,Line69m1,Line69m2,Line69m3,Line69m4,Line69m5,Line69m6,Line69m7]
theorem Line69_farAll : ∀ m ∈ Line69Data, farOK pts m := by
  intro m hm
  simp only [Line69Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line69m0_far,Line69m1_far,Line69m2_far,Line69m3_far,Line69m4_far,Line69m5_far,Line69m6_far,Line69m7_far]
theorem Line69_okAll : ∀ m ∈ Line69Data, axisOK pts m = true := by
  intro m hm
  simp only [Line69Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line69m0_ok,Line69m1_ok,Line69m2_ok,Line69m3_ok,Line69m4_ok,Line69m5_ok,Line69m6_ok,Line69m7_ok]
end CatalanCore.Cert.SigmaQuarter
