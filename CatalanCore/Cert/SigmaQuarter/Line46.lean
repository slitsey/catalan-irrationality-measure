module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line46m0 : Macro := { x0 := (972659097600), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8425544606957615901841013413),(4692900905971522175701942272),(4886395785052527460352),(0),(886973340089086509056),(4241757038438192)), boxes := [
    (((972642320384),(972675874816),(0),(0)),((648428213589),(648450583211),(-7296973847),(0)))
] }
theorem Line46m0_far : farOK pts Line46m0 := by decide +kernel
theorem Line46m0_ok : axisOK pts Line46m0 = true := by decide +kernel
def Line46m1 : Macro := { x0 := (972692652032), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8430132278299421026237054501),(4692764725616105278268243968),(4886539900240603316224),(0),(886973340089086509056),(4241503533865919)), boxes := [
    (((972675874816),(972709429248),(0),(0)),((648450583210),(648472952832),(-7296971567),(0)))
] }
theorem Line46m1_far : farOK pts Line46m1 := by decide +kernel
theorem Line46m1_ok : axisOK pts Line46m1 = true := by decide +kernel
def Line46m2 : Macro := { x0 := (972726206464), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8434711620698137947783078051),(4692628610555903482338672640),(4886684015428679172096),(0),(886973340089086509056),(4241250107729955)), boxes := [
    (((972709429248),(972742983680),(0),(0)),((648472952832),(648495322454),(-7296969324),(0)))
] }
theorem Line46m2_far : farOK pts Line46m2 := by decide +kernel
theorem Line46m2_ok : axisOK pts Line46m2 = true := by decide +kernel
def Line46m3 : Macro := { x0 := (972759760896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8439297946781261525866586610),(4692492596693947161701449728),(4886828130616755027968),(0),(886973340089086509056),(4240996786702075)), boxes := [
    (((972742983680),(972776538112),(0),(0)),((648495322453),(648517692075),(-7296967343),(0)))
] }
theorem Line46m3_far : farOK pts Line46m3 := by decide +kernel
theorem Line46m3_ok : axisOK pts Line46m3 = true := by decide +kernel
def Line46m4 : Macro := { x0 := (972793315328), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8443876473066067218094983512),(4692356415574980242754306048),(4886972245804830883840),(0),(886973340089086509056),(4240743321621707)), boxes := [
    (((972776538112),(972810092544),(0),(0)),((648517692074),(648540061696),(-7296965123),(0)))
] }
theorem Line46m4_far : farOK pts Line46m4 := by decide +kernel
theorem Line46m4_ok : axisOK pts Line46m4 = true := by decide +kernel
def Line46m5 : Macro := { x0 := (972826869760), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8448452299041571245673475271),(4692220346227262094339866624),(4887116360992906739712),(0),(886973340089086509056),(4240489989172089)), boxes := [
    (((972810092544),(972843646976),(0),(0)),((648540061696),(648562431318),(-7296962442),(0)))
] }
theorem Line46m5_far : farOK pts Line46m5 := by decide +kernel
theorem Line46m5_ok : axisOK pts Line46m5 = true := by decide +kernel
def Line46m6 : Macro := { x0 := (972860424192), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8453035558266111040622164793),(4692084304811907728592601088),(4887260476180982595584),(0),(886973340089086509056),(4240236679989933)), boxes := [
    (((972843646976),(972877201408),(0),(0)),((648562431317),(648584800939),(-7296960282),(0)))
] }
theorem Line46m6_far : farOK pts Line46m6 := by decide +kernel
theorem Line46m6_ok : axisOK pts Line46m6 = true := by decide +kernel
def Line46m7 : Macro := { x0 := (972893978624), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8457613879900253999165936242),(4691948056802404214749265920),(4887404591369058451456),(0),(886973340089086509056),(4239983218121389)), boxes := [
    (((972877201408),(972910755840),(0),(0)),((648584800938),(648607170560),(-7296957980),(0)))
] }
theorem Line46m7_far : farOK pts Line46m7 := by decide +kernel
theorem Line46m7_ok : axisOK pts Line46m7 = true := by decide +kernel
def Line46Data : List Macro := [Line46m0,Line46m1,Line46m2,Line46m3,Line46m4,Line46m5,Line46m6,Line46m7]
theorem Line46_farAll : ∀ m ∈ Line46Data, farOK pts m := by
  intro m hm
  simp only [Line46Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line46m0_far,Line46m1_far,Line46m2_far,Line46m3_far,Line46m4_far,Line46m5_far,Line46m6_far,Line46m7_far]
theorem Line46_okAll : ∀ m ∈ Line46Data, axisOK pts m = true := by
  intro m hm
  simp only [Line46Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line46m0_ok,Line46m1_ok,Line46m2_ok,Line46m3_ok,Line46m4_ok,Line46m5_ok,Line46m6_ok,Line46m7_ok]
end CatalanCore.Cert.SigmaQuarter
