module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line43m0 : Macro := { x0 := (971853791232), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8315512429649184838191707766),(4696170801261430354573459456),(4882937020538706919424),(0),(886973340089086509056),(4247847232289139)), boxes := [
    (((971837014016),(971870568448),(0),(0)),((647891342677),(647913712299),(-7297011080),(0)))
] }
theorem Line43m0_far : farOK pts Line43m0 := by decide +kernel
theorem Line43m0_ok : axisOK pts Line43m0 = true := by decide +kernel
def Line43m1 : Macro := { x0 := (971887345664), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8320098572871460258099327446),(4696034509620412324742496256),(4883081135726782775296),(0),(886973340089086509056),(4247593257649287)), boxes := [
    (((971870568448),(971904122880),(0),(0)),((647913712298),(647936081920),(-7297012687),(0)))
] }
theorem Line43m1_far : farOK pts Line43m1 := by decide +kernel
theorem Line43m1_ok : axisOK pts Line43m1 = true := by decide +kernel
def Line43m2 : Macro := { x0 := (971920900096), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8324681131730841443562095152),(4695898165770504416906510336),(4883225250914858631168),(0),(886973340089086509056),(4247339236963041)), boxes := [
    (((971904122880),(971937677312),(0),(0)),((647936081920),(647958451542),(-7297011221),(0)))
] }
theorem Line43m2_far : farOK pts Line43m2 := by decide +kernel
theorem Line43m2_ok : axisOK pts Line43m2 = true := by decide +kernel
def Line43m3 : Macro := { x0 := (971954454528), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8329260270419615242091281461),(4695761988831074481971724288),(4883369366102934487040),(0),(886973340089086509056),(4247085406000142)), boxes := [
    (((971937677312),(971971231744),(0),(0)),((647958451541),(647980821163),(-7297009284),(0)))
] }
theorem Line43m3_far : farOK pts Line43m3 := by decide +kernel
theorem Line43m3_ok : axisOK pts Line43m3 = true := by decide +kernel
def Line43m4 : Macro := { x0 := (971988008960), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8333847799385227273043373504),(4695625549910570037258420224),(4883513481291010342912),(0),(886973340089086509056),(4246831324538579)), boxes := [
    (((971971231744),(972004786176),(0),(0)),((647980821162),(648003190784),(-7297007888),(0)))
] }
theorem Line43m4_far : farOK pts Line43m4 := by decide +kernel
theorem Line43m4_ok : axisOK pts Line43m4 = true := by decide +kernel
def Line43m5 : Macro := { x0 := (972021563392), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8338435975028534760473681594),(4695489239620870482844516352),(4883657596479086198784),(0),(886973340089086509056),(4246577393536064)), boxes := [
    (((972004786176),(972038340608),(0),(0)),((648003190784),(648025560406),(-7297006539),(0)))
] }
theorem Line43m5_far : farOK pts Line43m5 := by decide +kernel
theorem Line43m5_ok : axisOK pts Line43m5 = true := by decide +kernel
def Line43m6 : Macro := { x0 := (972055117824), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8343022046964186648659050948),(4695353009080917679552528384),(4883801711667162054656),(0),(886973340089086509056),(4246323541855940)), boxes := [
    (((972038340608),(972071895040),(0),(0)),((648025560405),(648047930027),(-7297005144),(0)))
] }
theorem Line43m6_far : farOK pts Line43m6 := by decide +kernel
theorem Line43m6_ok : axisOK pts Line43m6 = true := by decide +kernel
def Line43m7 : Macro := { x0 := (972088672256), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8347611172918765999415475323),(4695216881105966366892883968),(4883945826855237910528),(0),(886973340089086509056),(4246069803442368)), boxes := [
    (((972071895040),(972105449472),(0),(0)),((648047930026),(648070299648),(-7297003542),(0)))
] }
theorem Line43m7_far : farOK pts Line43m7 := by decide +kernel
theorem Line43m7_ok : axisOK pts Line43m7 = true := by decide +kernel
def Line43Data : List Macro := [Line43m0,Line43m1,Line43m2,Line43m3,Line43m4,Line43m5,Line43m6,Line43m7]
theorem Line43_farAll : ∀ m ∈ Line43Data, farOK pts m := by
  intro m hm
  simp only [Line43Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line43m0_far,Line43m1_far,Line43m2_far,Line43m3_far,Line43m4_far,Line43m5_far,Line43m6_far,Line43m7_far]
theorem Line43_okAll : ∀ m ∈ Line43Data, axisOK pts m = true := by
  intro m hm
  simp only [Line43Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line43m0_ok,Line43m1_ok,Line43m2_ok,Line43m3_ok,Line43m4_ok,Line43m5_ok,Line43m6_ok,Line43m7_ok]
end CatalanCore.Cert.SigmaQuarter
