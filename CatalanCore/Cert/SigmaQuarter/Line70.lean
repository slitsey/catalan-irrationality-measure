module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line70m0 : Macro := { x0 := (1001264250880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12284936833507605862215196474),(4579637841958714187683135488),(5009253982887194591232),(0),(886973340089086509056),(4033677719826394)), boxes := [
    (((1000727379968),(1001801121792),(0),(0)),((667151586645),(667867414528),(-7294428053),(0)))
] }
theorem Line70m0_far : farOK pts Line70m0 := by decide +kernel
theorem Line70m0_ok : axisOK pts Line70m0 = true := by decide +kernel
def Line70m1 : Macro := { x0 := (1002337992704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12427995362229628281882424207),(4575492754553176763632254976),(5013865668905621979136),(0),(886973340089086509056),(4026168480745521)), boxes := [
    (((1001801121792),(1002874863616),(0),(0)),((667867414528),(668583242411),(-7293484718),(0)))
] }
theorem Line70m1_far : farOK pts Line70m1 := by decide +kernel
theorem Line70m1_ok : axisOK pts Line70m1 = true := by decide +kernel
def Line70m2 : Macro := { x0 := (1003411734528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12570912770435092960898019513),(4571355189582037142884188160),(5018477354924049367040),(0),(886973340089086509056),(4018680277104996)), boxes := [
    (((1002874863616),(1003948605440),(0),(0)),((668583242410),(669299070294),(-7292506326),(0)))
] }
theorem Line70m2_far : farOK pts Line70m2 := by decide +kernel
theorem Line70m2_ok : axisOK pts Line70m2 = true := by decide +kernel
def Line70m3 : Macro := { x0 := (1004485476352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12713710215368108176164836841),(4567225193383852512006307840),(5023089040942476754944),(0),(886973340089086509056),(4011213098684508)), boxes := [
    (((1003948605440),(1005022347264),(0),(0)),((669299070293),(670014898176),(-7291495330),(0)))
] }
theorem Line70m3_far : farOK pts Line70m3 := by decide +kernel
theorem Line70m3_ok : axisOK pts Line70m3 = true := by decide +kernel
def Line70m4 : Macro := { x0 := (1005559218176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12856365035486857641153091900),(4563102654869046846820057088),(5027700726960904142848),(0),(886973340089086509056),(4003766793582644)), boxes := [
    (((1005022347264),(1006096089088),(0),(0)),((670014898176),(670730726059),(-7290448206),(0)))
] }
theorem Line70m4_far : farOK pts Line70m4 := by decide +kernel
theorem Line70m4_ok : axisOK pts Line70m4 = true := by decide +kernel
def Line70m5 : Macro := { x0 := (1006632960000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((12998906362341388994667878973),(4558987486263059753030516736),(5032312412979331530752),(0),(886973340089086509056),(3996341215209747)), boxes := [
    (((1006096089088),(1007169830912),(0),(0)),((670730726058),(671446553942),(-7289365669),(0)))
] }
theorem Line70m5_far : farOK pts Line70m5 := by decide +kernel
theorem Line70m5_ok : axisOK pts Line70m5 = true := by decide +kernel
def Line70m6 : Macro := { x0 := (1007706701824), y0 := (0), i0 := 1200, i1 := 1200, fd := ((13141305939306254823357992272),(4554879867294777982902272000),(5036924098997758918656),(0),(886973340089086509056),(3988936466770657)), boxes := [
    (((1007169830912),(1008243572736),(0),(0)),((671446553941),(672162381824),(-7288242303),(0)))
] }
theorem Line70m6_far : farOK pts Line70m6 := by decide +kernel
theorem Line70m6_ok : axisOK pts Line70m6 = true := by decide +kernel
def Line70m7 : Macro := { x0 := (1008780443648), y0 := (0), i0 := 1200, i1 := 1200, fd := ((13283582270018633507081504397),(4550779427638941819960623104),(5041535785016186306560),(0),(886973340089086509056),(3981552168455514)), boxes := [
    (((1008243572736),(1009317314560),(0),(0)),((672162381824),(672878209707),(-7287085898),(0)))
] }
theorem Line70m7_far : farOK pts Line70m7 := by decide +kernel
theorem Line70m7_ok : axisOK pts Line70m7 = true := by decide +kernel
def Line70Data : List Macro := [Line70m0,Line70m1,Line70m2,Line70m3,Line70m4,Line70m5,Line70m6,Line70m7]
theorem Line70_farAll : ∀ m ∈ Line70Data, farOK pts m := by
  intro m hm
  simp only [Line70Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line70m0_far,Line70m1_far,Line70m2_far,Line70m3_far,Line70m4_far,Line70m5_far,Line70m6_far,Line70m7_far]
theorem Line70_okAll : ∀ m ∈ Line70Data, axisOK pts m = true := by
  intro m hm
  simp only [Line70Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line70m0_ok,Line70m1_ok,Line70m2_ok,Line70m3_ok,Line70m4_ok,Line70m5_ok,Line70m6_ok,Line70m7_ok]
end CatalanCore.Cert.SigmaQuarter
