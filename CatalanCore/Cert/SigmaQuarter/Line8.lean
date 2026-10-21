module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line8m0 : Macro := { x0 := (953080086528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5728506047012256518674689632),(4773714073209385173574352896),(4802304572810265559040),(0),(886973340089086509056),(4393641579557807)), boxes := [
    (((952945868800),(953214304256),(0),(0)),((635297245866),(635476202838),(-7295520855),(0)))
] }
theorem Line8m0_far : farOK pts Line8m0 := by decide +kernel
theorem Line8m0_ok : axisOK pts Line8m0 = true := by decide +kernel
def Line8m1 : Macro := { x0 := (953348521984), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5765806692973337047270272168),(4772587248671209124346462208),(4803457494314872406016),(0),(886973340089086509056),(4391504129920209)), boxes := [
    (((953214304256),(953482739712),(0),(0)),((635476202837),(635655159808),(-7295641155),(0)))
] }
theorem Line8m1_far : farOK pts Line8m1 := by decide +kernel
theorem Line8m1_ok : axisOK pts Line8m1 = true := by decide +kernel
def Line8m2 : Macro := { x0 := (953616957440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5803084737369833357157172601),(4771460906123338583577788416),(4804610415819479252992),(0),(886973340089086509056),(4389368216363762)), boxes := [
    (((953482739712),(953751175168),(0),(0)),((635655159808),(635834116779),(-7295757158),(0)))
] }
theorem Line8m2_far : farOK pts Line8m2 := by decide +kernel
theorem Line8m2_ok : axisOK pts Line8m2 = true := by decide +kernel
def Line8m3 : Macro := { x0 := (953885392896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5840352689070520019859341738),(4770335143320598781025124352),(4805763337324086099968),(0),(886973340089086509056),(4387233880244527)), boxes := [
    (((953751175168),(954019610624),(0),(0)),((635834116778),(636013073750),(-7295866034),(0)))
] }
theorem Line8m3_far : farOK pts Line8m3 := by decide +kernel
theorem Line8m3_ok : axisOK pts Line8m3 = true := by decide +kernel
def Line8m4 : Macro := { x0 := (954153828352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5877619993198119278379289271),(4769209776128875127994777600),(4806916258828692946944),(0),(886973340089086509056),(4385101011382390)), boxes := [
    (((954019610624),(954288046080),(0),(0)),((636013073749),(636192030720),(-7295975866),(0)))
] }
theorem Line8m4_far : farOK pts Line8m4 := by decide +kernel
theorem Line8m4_ok : axisOK pts Line8m4 = true := by decide +kernel
def Line8m5 : Macro := { x0 := (954422263808), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5914863890925071931143340725),(4768085313951661037279641600),(4808069180333299793920),(0),(886973340089086509056),(4382970027675593)), boxes := [
    (((954288046080),(954556481536),(0),(0)),((636192030720),(636370987691),(-7296084440),(0)))
] }
theorem Line8m5_far : farOK pts Line8m5 := by decide +kernel
theorem Line8m5_ok : axisOK pts Line8m5 = true := by decide +kernel
def Line8m6 : Macro := { x0 := (954690699264), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5952110686232683786850682179),(4766961229894455391877201920),(4809222101837906640896),(0),(886973340089086509056),(4380840469271523)), boxes := [
    (((954556481536),(954824916992),(0),(0)),((636370987690),(636549944662),(-7296196434),(0)))
] }
theorem Line8m6_far : farOK pts Line8m6 := by decide +kernel
theorem Line8m6_ok : axisOK pts Line8m6 = true := by decide +kernel
def Line8m7 : Macro := { x0 := (954959134720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5989344401459168304357030680),(4765837611557327169822457856),(4810375023342513487872),(0),(886973340089086509056),(4378712402345813)), boxes := [
    (((954824916992),(955093352448),(0),(0)),((636549944661),(636728901632),(-7296301077),(0)))
] }
theorem Line8m7_far : farOK pts Line8m7 := by decide +kernel
theorem Line8m7_ok : axisOK pts Line8m7 = true := by decide +kernel
def Line8Data : List Macro := [Line8m0,Line8m1,Line8m2,Line8m3,Line8m4,Line8m5,Line8m6,Line8m7]
theorem Line8_farAll : ∀ m ∈ Line8Data, farOK pts m := by
  intro m hm
  simp only [Line8Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line8m0_far,Line8m1_far,Line8m2_far,Line8m3_far,Line8m4_far,Line8m5_far,Line8m6_far,Line8m7_far]
theorem Line8_okAll : ∀ m ∈ Line8Data, axisOK pts m = true := by
  intro m hm
  simp only [Line8Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line8m0_ok,Line8m1_ok,Line8m2_ok,Line8m3_ok,Line8m4_ok,Line8m5_ok,Line8m6_ok,Line8m7_ok]
end CatalanCore.Cert.SigmaQuarter
