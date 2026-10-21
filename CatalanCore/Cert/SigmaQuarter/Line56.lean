module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line56m0 : Macro := { x0 := (976199090176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8908302096955968783434467469),(4678581068554627122215714816),(4901599937394530254848),(0),(886973340089086509056),(4215141035250777)), boxes := [
    (((976165535744),(976232644608),(0),(0)),((650777023829),(650821763072),(-7296927233),(0)))
] }
theorem Line56m0_far : farOK pts Line56m0 := by decide +kernel
theorem Line56m0_ok : axisOK pts Line56m0 = true := by decide +kernel
def Line56m1 : Macro := { x0 := (976266199040), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8917442194524727333181484015),(4678310340522716517471551488),(4901888167770681966592),(0),(886973340089086509056),(4214638801076886)), boxes := [
    (((976232644608),(976299753472),(0),(0)),((650821763072),(650866502315),(-7296914315),(0)))
] }
theorem Line56m1_far : farOK pts Line56m1 := by decide +kernel
theorem Line56m1_ok : axisOK pts Line56m1 = true := by decide +kernel
def Line56m2 : Macro := { x0 := (976333307904), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8926581822450590390155855380),(4678039842585572163852173312),(4902176398146833678336),(0),(886973340089086509056),(4214136834828377)), boxes := [
    (((976299753472),(976366862336),(0),(0)),((650866502314),(650911241558),(-7296904000),(0)))
] }
theorem Line56m2_far : farOK pts Line56m2 := by decide +kernel
theorem Line56m2_ok : axisOK pts Line56m2 = true := by decide +kernel
def Line56m3 : Macro := { x0 := (976400416768), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8935720229166480951754972280),(4677769156512606759331168256),(4902464628522985390080),(0),(886973340089086509056),(4213634764983609)), boxes := [
    (((976366862336),(976433971200),(0),(0)),((650911241557),(650955980800),(-7296893100),(0)))
] }
theorem Line56m3_far : farOK pts Line56m3 := by decide +kernel
theorem Line56m3_ok : axisOK pts Line56m3 = true := by decide +kernel
def Line56m4 : Macro := { x0 := (976467525632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8944852462313351199738730756),(4677498716682385576202141696),(4902752858899137101824),(0),(886973340089086509056),(4213132978959792)), boxes := [
    (((976433971200),(976501080064),(0),(0)),((650955980800),(651000720043),(-7296882422),(0)))
] }
theorem Line56m4_far : farOK pts Line56m4 := by decide +kernel
theorem Line56m4_ok : axisOK pts Line56m4 = true := by decide +kernel
def Line56m5 : Macro := { x0 := (976534634496), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8953995230935726478430626829),(4677228335630075227453849600),(4903041089275288813568),(0),(886973340089086509056),(4212631308522328)), boxes := [
    (((976501080064),(976568188928),(0),(0)),((651000720042),(651045459286),(-7296871629),(0)))
] }
theorem Line56m5_far : farOK pts Line56m5 := by decide +kernel
theorem Line56m5_ok : axisOK pts Line56m5 = true := by decide +kernel
def Line56m6 : Macro := { x0 := (976601743360), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8963120780256319814932006584),(4676957698456733898300194816),(4903329319651440525312),(0),(886973340089086509056),(4212129463045041)), boxes := [
    (((976568188928),(976635297792),(0),(0)),((651045459285),(651090198528),(-7296864129),(0)))
] }
theorem Line56m6_far : farOK pts Line56m6 := by decide +kernel
theorem Line56m6_ok : axisOK pts Line56m6 = true := by decide +kernel
def Line56m7 : Macro := { x0 := (976668852224), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8972261505128996974216949558),(4676687224126076638846648320),(4903617550027592237056),(0),(886973340089086509056),(4211627830775261)), boxes := [
    (((976635297792),(976702406656),(0),(0)),((651090198528),(651134937771),(-7296852862),(0)))
] }
theorem Line56m7_far : farOK pts Line56m7 := by decide +kernel
theorem Line56m7_ok : axisOK pts Line56m7 = true := by decide +kernel
def Line56Data : List Macro := [Line56m0,Line56m1,Line56m2,Line56m3,Line56m4,Line56m5,Line56m6,Line56m7]
theorem Line56_farAll : ∀ m ∈ Line56Data, farOK pts m := by
  intro m hm
  simp only [Line56Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line56m0_far,Line56m1_far,Line56m2_far,Line56m3_far,Line56m4_far,Line56m5_far,Line56m6_far,Line56m7_far]
theorem Line56_okAll : ∀ m ∈ Line56Data, axisOK pts m = true := by
  intro m hm
  simp only [Line56Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line56m0_ok,Line56m1_ok,Line56m2_ok,Line56m3_ok,Line56m4_ok,Line56m5_ok,Line56m6_ok,Line56m7_ok]
end CatalanCore.Cert.SigmaQuarter
