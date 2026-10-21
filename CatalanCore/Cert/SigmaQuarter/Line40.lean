module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line40m0 : Macro := { x0 := (971048484864), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8205393297886650629809330720),(4699445183191235848269791232),(4879478256024886378496),(0),(886973340089086509056),(4253950544711349)), boxes := [
    (((971031707648),(971065262080),(0),(0)),((647354471765),(647376841387),(-7297034449),(0)))
] }
theorem Line40m0_far : farOK pts Line40m0 := by decide +kernel
theorem Line40m0_ok : axisOK pts Line40m0 = true := by decide +kernel
def Line40m1 : Macro := { x0 := (971082039296), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8209981433359548662375042359),(4699308667348042880326631424),(4879622371212962234368),(0),(886973340089086509056),(4253695979567485)), boxes := [
    (((971065262080),(971098816512),(0),(0)),((647376841386),(647399211008),(-7297033629),(0)))
] }
theorem Line40m1_far : farOK pts Line40m1 := by decide +kernel
theorem Line40m1_ok : axisOK pts Line40m1 = true := by decide +kernel
def Line40m2 : Macro := { x0 := (971115593728), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8214568784993477596882081441),(4699172169025398682108821504),(4879766486401038090240),(0),(886973340089086509056),(4253441454580340)), boxes := [
    (((971098816512),(971132370944),(0),(0)),((647399211008),(647421580630),(-7297036656),(0)))
] }
theorem Line40m2_far : farOK pts Line40m2 := by decide +kernel
theorem Line40m2_ok : axisOK pts Line40m2 = true := by decide +kernel
def Line40m3 : Macro := { x0 := (971149148160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8219161074847408444839071752),(4699035721604532128705150976),(4879910601589113946112),(0),(886973340089086509056),(4253186989050389)), boxes := [
    (((971132370944),(971165925376),(0),(0)),((647421580629),(647443950251),(-7297036036),(0)))
] }
theorem Line40m3_far : farOK pts Line40m3 := by decide +kernel
theorem Line40m3_ok : axisOK pts Line40m3 = true := by decide +kernel
def Line40m4 : Macro := { x0 := (971182702592), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8223755549009332399557738424),(4698899481834083311663579136),(4880054716777189801984),(0),(886973340089086509056),(4252932715214769)), boxes := [
    (((971165925376),(971199479808),(0),(0)),((647443950250),(647466319872),(-7297035514),(0)))
] }
theorem Line40m4_far : farOK pts Line40m4 := by decide +kernel
theorem Line40m4_ok : axisOK pts Line40m4 = true := by decide +kernel
def Line40m5 : Macro := { x0 := (971216257024), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8228342942276603913591080657),(4698762698187288313882148864),(4880198831965265657856),(0),(886973340089086509056),(4252677982094668)), boxes := [
    (((971199479808),(971233034240),(0),(0)),((647466319872),(647488689494),(-7297034778),(0)))
] }
theorem Line40m5_far : farOK pts Line40m5 := by decide +kernel
theorem Line40m5_ok : axisOK pts Line40m5 = true := by decide +kernel
def Line40m6 : Macro := { x0 := (971249811456), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8232934868884016083834240452),(4698626444404580400049881088),(4880342947153341513728),(0),(886973340089086509056),(4252423732268839)), boxes := [
    (((971233034240),(971266588672),(0),(0)),((647488689493),(647511059115),(-7297033774),(0)))
] }
theorem Line40m6_far : farOK pts Line40m6 := by decide +kernel
theorem Line40m6_ok : axisOK pts Line40m6 = true := by decide +kernel
def Line40m7 : Macro := { x0 := (971283365888), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8237527097548502144379763567),(4698489782147166276891508736),(4880487062341417369600),(0),(886973340089086509056),(4252169141936858)), boxes := [
    (((971266588672),(971300143104),(0),(0)),((647511059114),(647533428736),(-7297033105),(0)))
] }
theorem Line40m7_far : farOK pts Line40m7 := by decide +kernel
theorem Line40m7_ok : axisOK pts Line40m7 = true := by decide +kernel
def Line40Data : List Macro := [Line40m0,Line40m1,Line40m2,Line40m3,Line40m4,Line40m5,Line40m6,Line40m7]
theorem Line40_farAll : ∀ m ∈ Line40Data, farOK pts m := by
  intro m hm
  simp only [Line40Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line40m0_far,Line40m1_far,Line40m2_far,Line40m3_far,Line40m4_far,Line40m5_far,Line40m6_far,Line40m7_far]
theorem Line40_okAll : ∀ m ∈ Line40Data, axisOK pts m = true := by
  intro m hm
  simp only [Line40Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line40m0_ok,Line40m1_ok,Line40m2_ok,Line40m3_ok,Line40m4_ok,Line40m5_ok,Line40m6_ok,Line40m7_ok]
end CatalanCore.Cert.SigmaQuarter
