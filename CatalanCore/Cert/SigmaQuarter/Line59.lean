module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line59m0 : Macro := { x0 := (977809702912), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9127459275680359965673377550),(4672094760125213140269989888),(4908517466422171336704),(0),(886973340089086509056),(4203114530035450)), boxes := [
    (((977776148480),(977843257344),(0),(0)),((651850765653),(651895504896),(-7296643456),(0)))
] }
theorem Line59m0_far : farOK pts Line59m0 := by decide +kernel
theorem Line59m0_ok : axisOK pts Line59m0 = true := by decide +kernel
def Line59m1 : Macro := { x0 := (977876811776), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9136588988898560233790240327),(4671824889170451925411692544),(4908805696798323048448),(0),(886973340089086509056),(4202614556478643)), boxes := [
    (((977843257344),(977910366208),(0),(0)),((651895504896),(651940244139),(-7296630363),(0)))
] }
theorem Line59m1_far : farOK pts Line59m1 := by decide +kernel
theorem Line59m1_ok : axisOK pts Line59m1 = true := by decide +kernel
def Line59m2 : Macro := { x0 := (977943920640), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9145713217029145898283439480),(4671555191446082190763622400),(4909093927174474760192),(0),(886973340089086509056),(4202114780583633)), boxes := [
    (((977910366208),(977977475072),(0),(0)),((651940244138),(651984983382),(-7296623809),(0)))
] }
theorem Line59m2_far : farOK pts Line59m2 := by decide +kernel
theorem Line59m2_ok : axisOK pts Line59m2 = true := by decide +kernel
def Line59m3 : Macro := { x0 := (978011029504), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9154832188900950421660167650),(4671285129677514520928911360),(4909382157550626471936),(0),(886973340089086509056),(4201614752944379)), boxes := [
    (((977977475072),(978044583936),(0),(0)),((651984983381),(652029722624),(-7296609629),(0)))
] }
theorem Line59m3_far : farOK pts Line59m3 := by decide +kernel
theorem Line59m3_ok : axisOK pts Line59m3 = true := by decide +kernel
def Line59m4 : Macro := { x0 := (978078138368), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9163959425505258732901936661),(4671015496268934100365672448),(4909670387926778183680),(0),(886973340089086509056),(4201115176201452)), boxes := [
    (((978044583936),(978111692800),(0),(0)),((652029722624),(652074461867),(-7296595939),(0)))
] }
theorem Line59m4_far : farOK pts Line59m4 := by decide +kernel
theorem Line59m4_ok : axisOK pts Line59m4 = true := by decide +kernel
def Line59m5 : Macro := { x0 := (978145247232), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9173087746599323227123259492),(4670745732933350408821342208),(4909958618302929895424),(0),(886973340089086509056),(4200615537576194)), boxes := [
    (((978111692800),(978178801664),(0),(0)),((652074461866),(652119201110),(-7296582390),(0)))
] }
theorem Line59m5_far : farOK pts Line59m5 := by decide +kernel
theorem Line59m5_ok : axisOK pts Line59m5 = true := by decide +kernel
def Line59m6 : Macro := { x0 := (978212356096), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9182205929677086588709216038),(4670475857814269141823717376),(4910246848679081607168),(0),(886973340089086509056),(4200115851244448)), boxes := [
    (((978178801664),(978245910528),(0),(0)),((652119201109),(652163940352),(-7296567924),(0)))
] }
theorem Line59m6_far : farOK pts Line59m6 := by decide +kernel
theorem Line59m6_ok : axisOK pts Line59m6 = true := by decide +kernel
def Line59m7 : Macro := { x0 := (978279464960), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9191325893972687162008454672),(4670206228236428847653388288),(4910535079055233318912),(0),(886973340089086509056),(4199616463182904)), boxes := [
    (((978245910528),(978313019392),(0),(0)),((652163940352),(652208679595),(-7296550832),(0)))
] }
theorem Line59m7_far : farOK pts Line59m7 := by decide +kernel
theorem Line59m7_ok : axisOK pts Line59m7 = true := by decide +kernel
def Line59Data : List Macro := [Line59m0,Line59m1,Line59m2,Line59m3,Line59m4,Line59m5,Line59m6,Line59m7]
theorem Line59_farAll : ∀ m ∈ Line59Data, farOK pts m := by
  intro m hm
  simp only [Line59Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line59m0_far,Line59m1_far,Line59m2_far,Line59m3_far,Line59m4_far,Line59m5_far,Line59m6_far,Line59m7_far]
theorem Line59_okAll : ∀ m ∈ Line59Data, axisOK pts m = true := by
  intro m hm
  simp only [Line59Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line59m0_ok,Line59m1_ok,Line59m2_ok,Line59m3_ok,Line59m4_ok,Line59m5_ok,Line59m6_ok,Line59m7_ok]
end CatalanCore.Cert.SigmaQuarter
