module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line22m0 : Macro := { x0 := (966132760576), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7531644308895347700756720384),(4719532523888411580974366720),(4858365380971773493248),(0),(886973340089086509056),(4291494517718312)), boxes := [
    (((966099206144),(966166315008),(0),(0)),((644066137429),(644110876672),(-7297137912),(0)))
] }
theorem Line22m0_far : farOK pts Line22m0 := by decide +kernel
theorem Line22m0_ok : axisOK pts Line22m0 = true := by decide +kernel
def Line22m1 : Macro := { x0 := (966199869440), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7540862496140273755859791109),(4719257101465102592907083776),(4858653611347925204992),(0),(886973340089086509056),(4290978588782743)), boxes := [
    (((966166315008),(966233423872),(0),(0)),((644110876672),(644155615915),(-7297145128),(0)))
] }
theorem Line22m1_far : farOK pts Line22m1 := by decide +kernel
theorem Line22m1_ok : axisOK pts Line22m1 = true := by decide +kernel
def Line22m2 : Macro := { x0 := (966266978304), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7550081296282131703155426297),(4718981798030480165614649344),(4858941841724076916736),(0),(886973340089086509056),(4290462831459239)), boxes := [
    (((966233423872),(966300532736),(0),(0)),((644155615914),(644200355158),(-7297152173),(0)))
] }
theorem Line22m2_far : farOK pts Line22m2 := by decide +kernel
theorem Line22m2_ok : axisOK pts Line22m2 = true := by decide +kernel
def Line22m3 : Macro := { x0 := (966317309952), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7556992035001537626985827882),(4718775147192318180129570816),(4859158014506190700544),(0),(886973340089086509056),(4290075893486447)), boxes := [
    (((966300532736),(966334087168),(0),(0)),((644200355157),(644222724779),(-7296828253),(0)))
] }
theorem Line22m3_far : farOK pts Line22m3 := by decide +kernel
theorem Line22m3_ok : axisOK pts Line22m3 = true := by decide +kernel
def Line22m4 : Macro := { x0 := (966350864384), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7561604810703928771868587559),(4718637670834701624623366144),(4859302129694266556416),(0),(886973340089086509056),(4289818215954169)), boxes := [
    (((966334087168),(966367641600),(0),(0)),((644222724778),(644245094400),(-7296831951),(0)))
] }
theorem Line22m4_far : farOK pts Line22m4 := by decide +kernel
theorem Line22m4_ok : axisOK pts Line22m4 = true := by decide +kernel
def Line22m5 : Macro := { x0 := (966384418816), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7566210758376127854927655834),(4718499833797601247145164800),(4859446244882342412288),(0),(886973340089086509056),(4289560238976453)), boxes := [
    (((966367641600),(966401196032),(0),(0)),((644245094400),(644267464022),(-7296835442),(0)))
] }
theorem Line22m5_far : farOK pts Line22m5 := by decide +kernel
theorem Line22m5_ok : axisOK pts Line22m5 = true := by decide +kernel
def Line22m6 : Macro := { x0 := (966417973248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7570819373804339576189701365),(4718362356215189925453168640),(4859590360070418268160),(0),(886973340089086509056),(4289302591141293)), boxes := [
    (((966401196032),(966434750464),(0),(0)),((644267464021),(644289833643),(-7296839047),(0)))
] }
theorem Line22m6_far : farOK pts Line22m6 := by decide +kernel
theorem Line22m6_ok : axisOK pts Line22m6 = true := by decide +kernel
def Line22m7 : Macro := { x0 := (966451527680), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7575426128578245673098801974),(4718224680624299814094635008),(4859734475258494124032),(0),(886973340089086509056),(4289044793351875)), boxes := [
    (((966434750464),(966468304896),(0),(0)),((644289833642),(644312203264),(-7296842205),(0)))
] }
theorem Line22m7_far : farOK pts Line22m7 := by decide +kernel
theorem Line22m7_ok : axisOK pts Line22m7 = true := by decide +kernel
def Line22Data : List Macro := [Line22m0,Line22m1,Line22m2,Line22m3,Line22m4,Line22m5,Line22m6,Line22m7]
theorem Line22_farAll : ∀ m ∈ Line22Data, farOK pts m := by
  intro m hm
  simp only [Line22Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line22m0_far,Line22m1_far,Line22m2_far,Line22m3_far,Line22m4_far,Line22m5_far,Line22m6_far,Line22m7_far]
theorem Line22_okAll : ∀ m ∈ Line22Data, axisOK pts m = true := by
  intro m hm
  simp only [Line22Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line22m0_ok,Line22m1_ok,Line22m2_ok,Line22m3_ok,Line22m4_ok,Line22m5_ok,Line22m6_ok,Line22m7_ok]
end CatalanCore.Cert.SigmaQuarter
