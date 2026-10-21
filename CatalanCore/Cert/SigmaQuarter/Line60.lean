module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line60m0 : Macro := { x0 := (978346573824), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9200448953446512349060460871),(4669936619086585238529835008),(4910823309431385030656),(0),(886973340089086509056),(4199117144049778)), boxes := [
    (((978313019392),(978380128256),(0),(0)),((652208679594),(652253418838),(-7296536110),(0)))
] }
theorem Line60m0_far : farOK pts Line60m0 := by decide +kernel
theorem Line60m0_ok : axisOK pts Line60m0 = true := by decide +kernel
def Line60m1 : Macro := { x0 := (978413682688), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9209566507659112734598883977),(4669666964332380482291564544),(4911111539807536742400),(0),(886973340089086509056),(4198617843562804)), boxes := [
    (((978380128256),(978447237120),(0),(0)),((652253418837),(652298158080),(-7296521568),(0)))
] }
theorem Line60m1_far : farOK pts Line60m1 := by decide +kernel
theorem Line60m1_ok : axisOK pts Line60m1 = true := by decide +kernel
def Line60m2 : Macro := { x0 := (978480791552), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9218692501886750388619107071),(4669397479777296473546883072),(4911399770183688454144),(0),(886973340089086509056),(4198118770192963)), boxes := [
    (((978447237120),(978514345984),(0),(0)),((652298158080),(652342897323),(-7296506911),(0)))
] }
theorem Line60m2_far : farOK pts Line60m2 := by decide +kernel
theorem Line60m2_ok : axisOK pts Line60m2 = true := by decide +kernel
def Line60m3 : Macro := { x0 := (978547900416), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9227808812173900166249357196),(4669127890480410458690093056),(4911688000559840165888),(0),(886973340089086509056),(4197619657690730)), boxes := [
    (((978514345984),(978581454848),(0),(0)),((652342897322),(652387636566),(-7296492204),(0)))
] }
theorem Line60m3_far : farOK pts Line60m3 := by decide +kernel
theorem Line60m3_ok : axisOK pts Line60m3 = true := by decide +kernel
def Line60m4 : Macro := { x0 := (978648563712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9241483803832881320471984930),(4668723640477299312314875904),(4912120346124067733504),(0),(886973340089086509056),(4196871223198929)), boxes := [
    (((978581454848),(978715672576),(0),(0)),((652387636565),(652477115051),(-7297132335),(0)))
] }
theorem Line60m4_far : farOK pts Line60m4 := by decide +kernel
theorem Line60m4_ok : axisOK pts Line60m4 = true := by decide +kernel
def Line60m5 : Macro := { x0 := (978782781440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9259721727428069086986243469),(4668184639691579095409033216),(4912696806876371156992),(0),(886973340089086509056),(4195873514680295)), boxes := [
    (((978715672576),(978849890304),(0),(0)),((652477115050),(652566593536),(-7297102593),(0)))
] }
theorem Line60m5_far : farOK pts Line60m5 := by decide +kernel
theorem Line60m5_ok : axisOK pts Line60m5 = true := by decide +kernel
def Line60m6 : Macro := { x0 := (978916999168), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9277965160735689315074008689),(4667645869122695916037603328),(4913273267628674580480),(0),(886973340089086509056),(4194876264788644)), boxes := [
    (((978849890304),(978984108032),(0),(0)),((652566593536),(652656072022),(-7297072881),(0)))
] }
theorem Line60m6_far : farOK pts Line60m6 := by decide +kernel
theorem Line60m6_ok : axisOK pts Line60m6 = true := by decide +kernel
def Line60m7 : Macro := { x0 := (979051216896), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9296189921242504356317854929),(4667107203210069053216915456),(4913849728380978003968),(0),(886973340089086509056),(4193879356818408)), boxes := [
    (((978984108032),(979118325760),(0),(0)),((652656072021),(652745550507),(-7297042382),(0)))
] }
theorem Line60m7_far : farOK pts Line60m7 := by decide +kernel
theorem Line60m7_ok : axisOK pts Line60m7 = true := by decide +kernel
def Line60Data : List Macro := [Line60m0,Line60m1,Line60m2,Line60m3,Line60m4,Line60m5,Line60m6,Line60m7]
theorem Line60_farAll : ∀ m ∈ Line60Data, farOK pts m := by
  intro m hm
  simp only [Line60Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line60m0_far,Line60m1_far,Line60m2_far,Line60m3_far,Line60m4_far,Line60m5_far,Line60m6_far,Line60m7_far]
theorem Line60_okAll : ∀ m ∈ Line60Data, axisOK pts m = true := by
  intro m hm
  simp only [Line60Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line60m0_ok,Line60m1_ok,Line60m2_ok,Line60m3_ok,Line60m4_ok,Line60m5_ok,Line60m6_ok,Line60m7_ok]
end CatalanCore.Cert.SigmaQuarter
