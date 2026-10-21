module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line24m0 : Macro := { x0 := (966753517568), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7616864777480409399524933069),(4716986573136552254301732864),(4861031511951176826880),(0),(886973340089086509056),(4286726140517568)), boxes := [
    (((966736740352),(966770294784),(0),(0)),((644491160234),(644513529856),(-7296867572),(0)))
] }
theorem Line24m0_far : farOK pts Line24m0 := by decide +kernel
theorem Line24m0_ok : axisOK pts Line24m0 = true := by decide +kernel
def Line24m1 : Macro := { x0 := (966787072000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7621463132726125749568805450),(4716849131925500659514081280),(4861175627139252682752),(0),(886973340089086509056),(4286468705138784)), boxes := [
    (((966770294784),(966803849216),(0),(0)),((644513529856),(644535899478),(-7296870501),(0)))
] }
theorem Line24m1_far : farOK pts Line24m1 := by decide +kernel
theorem Line24m1_ok : axisOK pts Line24m1 = true := by decide +kernel
def Line24m2 : Macro := { x0 := (966820626432), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7626072640641277315564725960),(4716711300712802060545097728),(4861319742327328538624),(0),(886973340089086509056),(4286210940886024)), boxes := [
    (((966803849216),(966837403648),(0),(0)),((644535899477),(644558269099),(-7296873832),(0)))
] }
theorem Line24m2_far : farOK pts Line24m2 := by decide +kernel
theorem Line24m2_ok : axisOK pts Line24m2 = true := by decide +kernel
def Line24m3 : Macro := { x0 := (966854180864), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7630680409622077045914876189),(4716573771596910677076082688),(4861463857515404394496),(0),(886973340089086509056),(4285953461919676)), boxes := [
    (((966837403648),(966870958080),(0),(0)),((644558269098),(644580638720),(-7296876772),(0)))
] }
theorem Line24m3_far : farOK pts Line24m3 := by decide +kernel
theorem Line24m3_ok : axisOK pts Line24m3 = true := by decide +kernel
def Line24m4 : Macro := { x0 := (966887735296), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7635284439289435115500406375),(4716436358833182576661299200),(4861607972703480250368),(0),(886973340089086509056),(4285696104205975)), boxes := [
    (((966870958080),(966904512512),(0),(0)),((644580638720),(644603008342),(-7296879829),(0)))
] }
theorem Line24m4_far : farOK pts Line24m4 := by decide +kernel
theorem Line24m4_ok : axisOK pts Line24m4 = true := by decide +kernel
def Line24m5 : Macro := { x0 := (966921289728), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7639892709629622443479974980),(4716298888579113418245144576),(4861752087891556106240),(0),(886973340089086509056),(4285438706144741)), boxes := [
    (((966904512512),(966938066944),(0),(0)),((644603008341),(644625377963),(-7296883054),(0)))
] }
theorem Line24m5_far : farOK pts Line24m5 := by decide +kernel
theorem Line24m5_ok : axisOK pts Line24m5 = true := by decide +kernel
def Line24m6 : Macro := { x0 := (966954844160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7644502245543670091252261827),(4716161083534898383027896320),(4861896203079631962112),(0),(886973340089086509056),(4285181026446451)), boxes := [
    (((966938066944),(966971621376),(0),(0)),((644625377962),(644647747584),(-7296886347),(0)))
] }
theorem Line24m6_far : farOK pts Line24m6 := by decide +kernel
theorem Line24m6_ok : axisOK pts Line24m6 = true := by decide +kernel
def Line24m7 : Macro := { x0 := (966988398592), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7649111601933213309217861400),(4716023778602996551914487808),(4862040318267707817984),(0),(886973340089086509056),(4284923812312208)), boxes := [
    (((966971621376),(967005175808),(0),(0)),((644647747584),(644670117206),(-7296896100),(0)))
] }
theorem Line24m7_far : farOK pts Line24m7 := by decide +kernel
theorem Line24m7_ok : axisOK pts Line24m7 = true := by decide +kernel
def Line24Data : List Macro := [Line24m0,Line24m1,Line24m2,Line24m3,Line24m4,Line24m5,Line24m6,Line24m7]
theorem Line24_farAll : ∀ m ∈ Line24Data, farOK pts m := by
  intro m hm
  simp only [Line24Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line24m0_far,Line24m1_far,Line24m2_far,Line24m3_far,Line24m4_far,Line24m5_far,Line24m6_far,Line24m7_far]
theorem Line24_okAll : ∀ m ∈ Line24Data, axisOK pts m = true := by
  intro m hm
  simp only [Line24Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line24m0_ok,Line24m1_ok,Line24m2_ok,Line24m3_ok,Line24m4_ok,Line24m5_ok,Line24m6_ok,Line24m7_ok]
end CatalanCore.Cert.SigmaQuarter
