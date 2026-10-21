module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line13m0 : Macro := { x0 := (960529170432), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6760056813507746117850052511),(4742641350692458747262468096),(4834298144563105562624),(0),(886973340089086509056),(4334903957079971)), boxes := [
    (((960462061568),(960596279296),(0),(0)),((640308041045),(640397519531),(-7296780186),(0)))
] }
theorem Line13m0_far : farOK pts Line13m0 := by decide +kernel
theorem Line13m0_ok : axisOK pts Line13m0 = true := by decide +kernel
def Line13m1 : Macro := { x0 := (960663388160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6778576013969008461486600599),(4742085275657518610913361920),(4834874605315408986112),(0),(886973340089086509056),(4333856556480575)), boxes := [
    (((960596279296),(960730497024),(0),(0)),((640397519530),(640486998016),(-7296811424),(0)))
] }
theorem Line13m1_far : farOK pts Line13m1 := by decide +kernel
theorem Line13m1_ok : axisOK pts Line13m1 = true := by decide +kernel
def Line13m2 : Macro := { x0 := (960797605888), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6797103402251957483281649517),(4741529089127076107976572928),(4835451066067712409600),(0),(886973340089086509056),(4332809332926522)), boxes := [
    (((960730497024),(960864714752),(0),(0)),((640486998016),(640576476502),(-7296843556),(0)))
] }
theorem Line13m2_far : farOK pts Line13m2 := by decide +kernel
theorem Line13m2_ok : axisOK pts Line13m2 = true := by decide +kernel
def Line13m3 : Macro := { x0 := (960931823616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6815621640963121497132579425),(4740973326834552869037932544),(4836027526820015833088),(0),(886973340089086509056),(4331762743462472)), boxes := [
    (((960864714752),(960998932480),(0),(0)),((640576476501),(640665954987),(-7296879667),(0)))
] }
theorem Line13m3_far : farOK pts Line13m3 := by decide +kernel
theorem Line13m3_ok : axisOK pts Line13m3 = true := by decide +kernel
def Line13m4 : Macro := { x0 := (961066041344), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6834144882823000368227832412),(4740417724422455095317233664),(4836603987572319256576),(0),(886973340089086509056),(4330716566036729)), boxes := [
    (((960998932480),(961133150208),(0),(0)),((640665954986),(640755433472),(-7296910716),(0)))
] }
theorem Line13m4_far : farOK pts Line13m4 := by decide +kernel
theorem Line13m4_ok : axisOK pts Line13m4 = true := by decide +kernel
def Line13m5 : Macro := { x0 := (961200259072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6852656037406651088529047518),(4739861938529079049607970816),(4837180448324622680064),(0),(886973340089086509056),(4329670492066662)), boxes := [
    (((961133150208),(961267367936),(0),(0)),((640755433472),(640844911958),(-7296942704),(0)))
] }
theorem Line13m5_far : farOK pts Line13m5 := by decide +kernel
theorem Line13m5_ok : axisOK pts Line13m5 = true := by decide +kernel
def Line13m6 : Macro := { x0 := (961334476800), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6871173116267878905981664411),(4739306407585338946780594176),(4837756909076926103552),(0),(886973340089086509056),(4328624912389012)), boxes := [
    (((961267367936),(961401585664),(0),(0)),((640844911957),(640934390443),(-7296973273),(0)))
] }
theorem Line13m6_far : farOK pts Line13m6 := by decide +kernel
theorem Line13m6_ok : axisOK pts Line13m6 = true := by decide +kernel
def Line13m7 : Macro := { x0 := (961468694528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6889683576332421738435110470),(4738751181618165627455340544),(4838333369829229527040),(0),(886973340089086509056),(4327579850549693)), boxes := [
    (((961401585664),(961535803392),(0),(0)),((640934390442),(641023868928),(-7297004986),(0)))
] }
theorem Line13m7_far : farOK pts Line13m7 := by decide +kernel
theorem Line13m7_ok : axisOK pts Line13m7 = true := by decide +kernel
def Line13Data : List Macro := [Line13m0,Line13m1,Line13m2,Line13m3,Line13m4,Line13m5,Line13m6,Line13m7]
theorem Line13_farAll : ∀ m ∈ Line13Data, farOK pts m := by
  intro m hm
  simp only [Line13Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line13m0_far,Line13m1_far,Line13m2_far,Line13m3_far,Line13m4_far,Line13m5_far,Line13m6_far,Line13m7_far]
theorem Line13_okAll : ∀ m ∈ Line13Data, axisOK pts m = true := by
  intro m hm
  simp only [Line13Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line13m0_ok,Line13m1_ok,Line13m2_ok,Line13m3_ok,Line13m4_ok,Line13m5_ok,Line13m6_ok,Line13m7_ok]
end CatalanCore.Cert.SigmaQuarter
