module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line47m0 : Macro := { x0 := (972927533056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8462188012677015948172592469),(4691811925981442304470679552),(4887548706557134307328),(0),(886973340089086509056),(4239729866319696)), boxes := [
    (((972910755840),(972944310272),(0),(0)),((648607170560),(648629540182),(-7296955561),(0)))
] }
theorem Line47m0_far : farOK pts Line47m0 := by decide +kernel
theorem Line47m0_ok : axisOK pts Line47m0 = true := by decide +kernel
def Line47m1 : Macro := { x0 := (972961087488), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8466764743444718113666786035),(4691675916878136877660241920),(4887692821745210163200),(0),(886973340089086509056),(4239476646509965)), boxes := [
    (((972944310272),(972977864704),(0),(0)),((648629540181),(648651909803),(-7296952911),(0)))
] }
theorem Line47m1_far : farOK pts Line47m1 := by decide +kernel
theorem Line47m1_ok : axisOK pts Line47m1 = true := by decide +kernel
def Line47m2 : Macro := { x0 := (972994641920), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8471348905273412233585393360),(4691539847839532463624486912),(4887836936933286019072),(0),(886973340089086509056),(4239223377094322)), boxes := [
    (((972977864704),(973011419136),(0),(0)),((648651909802),(648674279424),(-7296950731),(0)))
] }
theorem Line47m2_far : farOK pts Line47m2 := by decide +kernel
theorem Line47m2_ok : axisOK pts Line47m2 = true := by decide +kernel
def Line47m3 : Macro := { x0 := (973028196352), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8475930761960338235661498341),(4691403657053712386373451776),(4887981052121361874944),(0),(886973340089086509056),(4238970036152650)), boxes := [
    (((973011419136),(973044973568),(0),(0)),((648674279424),(648696649046),(-7296948499),(0)))
] }
theorem Line47m3_far : farOK pts Line47m3 := by decide +kernel
theorem Line47m3_ok : axisOK pts Line47m3 = true := by decide +kernel
def Line47m4 : Macro := { x0 := (973061750784), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8480512615633852430276672534),(4691267831154980182532489216),(4888125167309437730816),(0),(886973340089086509056),(4238717013954912)), boxes := [
    (((973044973568),(973078528000),(0),(0)),((648696649045),(648719018667),(-7296946292),(0)))
] }
theorem Line47m4_far : farOK pts Line47m4 := by decide +kernel
theorem Line47m4_ok : axisOK pts Line47m4 = true := by decide +kernel
def Line47m5 : Macro := { x0 := (973095305216), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8485094200217196370772292756),(4691131818681792168187723776),(4888269282497513586688),(0),(886973340089086509056),(4238463853325258)), boxes := [
    (((973078528000),(973112082432),(0),(0)),((648719018666),(648741388288),(-7296946932),(0)))
] }
theorem Line47m5_far : farOK pts Line47m5 := by decide +kernel
theorem Line47m5_ok : axisOK pts Line47m5 = true := by decide +kernel
def Line47m6 : Macro := { x0 := (973128859648), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8489675904983122549259268268),(4690995707266663372421398528),(4888413397685589442560),(0),(886973340089086509056),(4238210614226859)), boxes := [
    (((973112082432),(973145636864),(0),(0)),((648741388288),(648763757910),(-7296944162),(0)))
] }
theorem Line47m6_far : farOK pts Line47m6 := by decide +kernel
theorem Line47m6_ok : axisOK pts Line47m6 = true := by decide +kernel
def Line47m7 : Macro := { x0 := (973162414080), y0 := (0), i0 := 1200, i1 := 1200, fd := ((8494257935700028596052884388),(4690859539822037693578018816),(4888557512873665298432),(0),(886973340089086509056),(4237957339471790)), boxes := [
    (((973145636864),(973179191296),(0),(0)),((648763757909),(648786127531),(-7296941722),(0)))
] }
theorem Line47m7_far : farOK pts Line47m7 := by decide +kernel
theorem Line47m7_ok : axisOK pts Line47m7 = true := by decide +kernel
def Line47Data : List Macro := [Line47m0,Line47m1,Line47m2,Line47m3,Line47m4,Line47m5,Line47m6,Line47m7]
theorem Line47_farAll : ∀ m ∈ Line47Data, farOK pts m := by
  intro m hm
  simp only [Line47Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line47m0_far,Line47m1_far,Line47m2_far,Line47m3_far,Line47m4_far,Line47m5_far,Line47m6_far,Line47m7_far]
theorem Line47_okAll : ∀ m ∈ Line47Data, axisOK pts m = true := by
  intro m hm
  simp only [Line47Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line47m0_ok,Line47m1_ok,Line47m2_ok,Line47m3_ok,Line47m4_ok,Line47m5_ok,Line47m6_ok,Line47m7_ok]
end CatalanCore.Cert.SigmaQuarter
