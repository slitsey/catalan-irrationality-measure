module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line66m0 : Macro := { x0 := (985829212160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10214176771343212597590716708),(4640064504836518624241713152),(4942960996372300890112),(0),(886973340089086509056),(4143994861058542)), boxes := [
    (((985694994432),(985963429888),(0),(0)),((657129996288),(657308953259),(-7296188102),(0)))
] }
theorem Line66m0_far : farOK pts Line66m0 := by decide +kernel
theorem Line66m0_ok : axisOK pts Line66m0 = true := by decide +kernel
def Line66m1 : Macro := { x0 := (986097647616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10250431597897169002880002454),(4638999972433744974827618304),(4944113917876907737088),(0),(886973340089086509056),(4142037668514811)), boxes := [
    (((985963429888),(986231865344),(0),(0)),((657308953258),(657487910230),(-7296073476),(0)))
] }
theorem Line66m1_far : farOK pts Line66m1 := by decide +kernel
theorem Line66m1_ok : axisOK pts Line66m1 = true := by decide +kernel
def Line66m2 : Macro := { x0 := (986366083072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10286667287411160320116470823),(4637935889438797350790299648),(4945266839381514584064),(0),(886973340089086509056),(4140081836994281)), boxes := [
    (((986231865344),(986500300800),(0),(0)),((657487910229),(657666867200),(-7295961678),(0)))
] }
theorem Line66m2_far : farOK pts Line66m2 := by decide +kernel
theorem Line66m2_ok : axisOK pts Line66m2 = true := by decide +kernel
def Line66m3 : Macro := { x0 := (986634518528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10322901110942708966536251912),(4636872346811847290023182336),(4946419760886121431040),(0),(886973340089086509056),(4138127433487372)), boxes := [
    (((986500300800),(986768736256),(0),(0)),((657666867200),(657845824171),(-7295846653),(0)))
] }
theorem Line66m3_far : farOK pts Line66m3 := by decide +kernel
theorem Line66m3_ok : axisOK pts Line66m3 = true := by decide +kernel
def Line66m4 : Macro := { x0 := (986902953984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10359112877955869500316825888),(4635809258866734700217630720),(4947572682390728278016),(0),(886973340089086509056),(4136174393652256)), boxes := [
    (((986768736256),(987037171712),(0),(0)),((657845824170),(658024781142),(-7295727046),(0)))
] }
theorem Line66m4_far : farOK pts Line66m4 := by decide +kernel
theorem Line66m4_ok : axisOK pts Line66m4 = true := by decide +kernel
def Line66m5 : Macro := { x0 := (987171389440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10395321627190831739440346154),(4634746735145955595446059008),(4948725603895335124992),(0),(886973340089086509056),(4134222812604279)), boxes := [
    (((987037171712),(987305607168),(0),(0)),((658024781141),(658203738112),(-7295603523),(0)))
] }
theorem Line66m5_far : farOK pts Line66m5 := by decide +kernel
theorem Line66m5_ok : axisOK pts Line66m5 = true := by decide +kernel
def Line66m6 : Macro := { x0 := (987439824896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10431530052155117439077715138),(4633684577946180283487617024),(4949878525399941971968),(0),(886973340089086509056),(4132272508859690)), boxes := [
    (((987305607168),(987574042624),(0),(0)),((658203738112),(658382695083),(-7295480616),(0)))
] }
theorem Line66m6_far : farOK pts Line66m6 := by decide +kernel
theorem Line66m6_ok : axisOK pts Line66m6 = true := by decide +kernel
def Line66m7 : Macro := { x0 := (987708260352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((10467716527094530607796157997),(4632622938720360890058145792),(4951031446904548818944),(0),(886973340089086509056),(4130323618500091)), boxes := [
    (((987574042624),(987842478080),(0),(0)),((658382695082),(658561652054),(-7295361736),(0)))
] }
theorem Line66m7_far : farOK pts Line66m7 := by decide +kernel
theorem Line66m7_ok : axisOK pts Line66m7 = true := by decide +kernel
def Line66Data : List Macro := [Line66m0,Line66m1,Line66m2,Line66m3,Line66m4,Line66m5,Line66m6,Line66m7]
theorem Line66_farAll : ∀ m ∈ Line66Data, farOK pts m := by
  intro m hm
  simp only [Line66Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line66m0_far,Line66m1_far,Line66m2_far,Line66m3_far,Line66m4_far,Line66m5_far,Line66m6_far,Line66m7_far]
theorem Line66_okAll : ∀ m ∈ Line66Data, axisOK pts m = true := by
  intro m hm
  simp only [Line66Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line66m0_ok,Line66m1_ok,Line66m2_ok,Line66m3_ok,Line66m4_ok,Line66m5_ok,Line66m6_ok,Line66m7_ok]
end CatalanCore.Cert.SigmaQuarter
