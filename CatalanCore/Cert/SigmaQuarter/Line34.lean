module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line34m0 : Macro := { x0 := (969437872128), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7984964211635801507043814225),(4706007970790164802710405120),(4872560726997245296640),(0),(886973340089086509056),(4266197096478050)), boxes := [
    (((969421094912),(969454649344),(0),(0)),((646280729941),(646303099563),(-7297029496),(0)))
] }
theorem Line34m0_far : farOK pts Line34m0 := by decide +kernel
theorem Line34m0_ok : axisOK pts Line34m0 = true := by decide +kernel
def Line34m1 : Macro := { x0 := (969471426560), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7989561830591713539567099555),(4705871001062380638411489280),(4872704842185321152512),(0),(886973340089086509056),(4265941371575310)), boxes := [
    (((969454649344),(969488203776),(0),(0)),((646303099562),(646325469184),(-7297030275),(0)))
] }
theorem Line34m1_far : farOK pts Line34m1 := by decide +kernel
theorem Line34m1_ok : axisOK pts Line34m1 = true := by decide +kernel
def Line34m2 : Macro := { x0 := (969504980992), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7994157685752247665379904299),(4705734185313743542476210176),(4872848957373397008384),(0),(886973340089086509056),(4265685796043141)), boxes := [
    (((969488203776),(969521758208),(0),(0)),((646325469184),(646347838806),(-7297031018),(0)))
] }
theorem Line34m2_far : farOK pts Line34m2 := by decide +kernel
theorem Line34m2_ok : axisOK pts Line34m2 = true := by decide +kernel
def Line34m3 : Macro := { x0 := (969538535424), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7998755627459471305127695963),(4705597148430027735397040128),(4872993072561472864256),(0),(886973340089086509056),(4265430037844859)), boxes := [
    (((969521758208),(969555312640),(0),(0)),((646347838805),(646370208427),(-7297031414),(0)))
] }
theorem Line34m3_far : farOK pts Line34m3 := by decide +kernel
theorem Line34m3_ok : axisOK pts Line34m3 = true := by decide +kernel
def Line34m4 : Macro := { x0 := (969572089856), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8003347811862514525453511326),(4705460347515487742000824320),(4873137187749548720128),(0),(886973340089086509056),(4265174506060399)), boxes := [
    (((969555312640),(969588867072),(0),(0)),((646370208426),(646392578048),(-7297031939),(0)))
] }
theorem Line34m4_far : farOK pts Line34m4 := by decide +kernel
theorem Line34m4_ok : axisOK pts Line34m4 = true := by decide +kernel
def Line34m5 : Macro := { x0 := (969605644288), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8007946463881762448714430748),(4705323578711500680317042688),(4873281302937624576000),(0),(886973340089086509056),(4264919015505685)), boxes := [
    (((969588867072),(969622421504),(0),(0)),((646392578048),(646414947670),(-7297032708),(0)))
] }
theorem Line34m5_far : farOK pts Line34m5 := by decide +kernel
theorem Line34m5_ok : axisOK pts Line34m5 = true := by decide +kernel
def Line34m6 : Macro := { x0 := (969639198720), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8012543458438076574020733320),(4705186677356815550562172928),(4873425418125700431872),(0),(886973340089086509056),(4264663433492554)), boxes := [
    (((969622421504),(969655975936),(0),(0)),((646414947669),(646437317291),(-7297033446),(0)))
] }
theorem Line34m6_far : farOK pts Line34m6 := by decide +kernel
theorem Line34m6_ok : axisOK pts Line34m6 = true := by decide +kernel
def Line34m7 : Macro := { x0 := (969672753152), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8017136662064364028337926740),(4705049698654068565780267008),(4873569533313776287744),(0),(886973340089086509056),(4264407793318170)), boxes := [
    (((969655975936),(969689530368),(0),(0)),((646437317290),(646459686912),(-7297033669),(0)))
] }
theorem Line34m7_far : farOK pts Line34m7 := by decide +kernel
theorem Line34m7_ok : axisOK pts Line34m7 = true := by decide +kernel
def Line34Data : List Macro := [Line34m0,Line34m1,Line34m2,Line34m3,Line34m4,Line34m5,Line34m6,Line34m7]
theorem Line34_farAll : ∀ m ∈ Line34Data, farOK pts m := by
  intro m hm
  simp only [Line34Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line34m0_far,Line34m1_far,Line34m2_far,Line34m3_far,Line34m4_far,Line34m5_far,Line34m6_far,Line34m7_far]
theorem Line34_okAll : ∀ m ∈ Line34Data, axisOK pts m = true := by
  intro m hm
  simp only [Line34Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line34m0_ok,Line34m1_ok,Line34m2_ok,Line34m3_ok,Line34m4_ok,Line34m5_ok,Line34m6_ok,Line34m7_ok]
end CatalanCore.Cert.SigmaQuarter
