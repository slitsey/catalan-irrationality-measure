module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line58m0 : Macro := { x0 := (977272832000), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9054430532687205410891298876),(4674254824265855913768583168),(4906211623412957642752),(0),(886973340089086509056),(4207117579869805)), boxes := [
    (((977239277568),(977306386432),(0),(0)),((651492851712),(651537590955),(-7296745251),(0)))
] }
theorem Line58m0_far : farOK pts Line58m0 := by decide +kernel
theorem Line58m0_ok : axisOK pts Line58m0 = true := by decide +kernel
def Line58m1 : Macro := { x0 := (977339940864), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9063565080932154444140918126),(4673984755000293215435292672),(4906499853789109354496),(0),(886973340089086509056),(4206616932210526)), boxes := [
    (((977306386432),(977373495296),(0),(0)),((651537590954),(651582330198),(-7296732987),(0)))
] }
theorem Line58m1_far : farOK pts Line58m1 := by decide +kernel
theorem Line58m1_ok : axisOK pts Line58m1 = true := by decide +kernel
def Line58m2 : Macro := { x0 := (977407049728), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9072693503480633417020585270),(4673714654859228381547266048),(4906788084165261066240),(0),(886973340089086509056),(4206116309336373)), boxes := [
    (((977373495296),(977440604160),(0),(0)),((651582330197),(651627069440),(-7296720182),(0)))
] }
theorem Line58m2_far : farOK pts Line58m2 := by decide +kernel
theorem Line58m2_ok : axisOK pts Line58m2 = true := by decide +kernel
def Line58m3 : Macro := { x0 := (977474158592), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9081819412452171169204854921),(4673444721506551316250886144),(4907076314541412777984),(0),(886973340089086509056),(4205615904313730)), boxes := [
    (((977440604160),(977507713024),(0),(0)),((651627069440),(651671808683),(-7296707508),(0)))
] }
theorem Line58m3_far : farOK pts Line58m3 := by decide +kernel
theorem Line58m3_ok : axisOK pts Line58m3 = true := by decide +kernel
def Line58m4 : Macro := { x0 := (977541267456), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9090951365066767510587587095),(4673174612746953803673042944),(4907364544917564489728),(0),(886973340089086509056),(4205115403505070)), boxes := [
    (((977507713024),(977574821888),(0),(0)),((651671808682),(651716547926),(-7296695142),(0)))
] }
theorem Line58m4_far : farOK pts Line58m4 := by decide +kernel
theorem Line58m4_ok : axisOK pts Line58m4 = true := by decide +kernel
def Line58m5 : Macro := { x0 := (977608376320), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9100075034065348626715872063),(4672904672661459044733681664),(4907652775293716201472),(0),(886973340089086509056),(4204615117005009)), boxes := [
    (((977574821888),(977641930752),(0),(0)),((651716547925),(651761287168),(-7296681918),(0)))
] }
theorem Line58m5_far : farOK pts Line58m5 := by decide +kernel
theorem Line58m5_ok : axisOK pts Line58m5 = true := by decide +kernel
def Line58m6 : Macro := { x0 := (977675485184), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9109207653618458400765650933),(4672634589944474406648020992),(4907941005669867913216),(0),(886973340089086509056),(4204114756712220)), boxes := [
    (((977641930752),(977709039616),(0),(0)),((651761287168),(651806026411),(-7296669456),(0)))
] }
theorem Line58m6_far : farOK pts Line58m6 := by decide +kernel
theorem Line58m6_ok : axisOK pts Line58m6 = true := by decide +kernel
def Line58m7 : Macro := { x0 := (977742594048), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9118332540944595008247225987),(4672364848892529715141279744),(4908229236046019624960),(0),(886973340089086509056),(4203614764246729)), boxes := [
    (((977709039616),(977776148480),(0),(0)),((651806026410),(651850765654),(-7296656236),(0)))
] }
theorem Line58m7_far : farOK pts Line58m7 := by decide +kernel
theorem Line58m7_ok : axisOK pts Line58m7 = true := by decide +kernel
def Line58Data : List Macro := [Line58m0,Line58m1,Line58m2,Line58m3,Line58m4,Line58m5,Line58m6,Line58m7]
theorem Line58_farAll : ∀ m ∈ Line58Data, farOK pts m := by
  intro m hm
  simp only [Line58Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line58m0_far,Line58m1_far,Line58m2_far,Line58m3_far,Line58m4_far,Line58m5_far,Line58m6_far,Line58m7_far]
theorem Line58_okAll : ∀ m ∈ Line58Data, axisOK pts m = true := by
  intro m hm
  simp only [Line58Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line58m0_ok,Line58m1_ok,Line58m2_ok,Line58m3_ok,Line58m4_ok,Line58m5_ok,Line58m6_ok,Line58m7_ok]
end CatalanCore.Cert.SigmaQuarter
