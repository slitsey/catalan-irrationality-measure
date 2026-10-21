module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line23m0 : Macro := { x0 := (966485082112), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7580028393491120116327701149),(4718087127963606855679475712),(4859878590446569979904),(0),(886973340089086509056),(4288787112165348)), boxes := [
    (((966468304896),(966501859328),(0),(0)),((644312203264),(644334572886),(-7296842736),(0)))
] }
theorem Line23m0_far : farOK pts Line23m0 := by decide +kernel
theorem Line23m0_ok : axisOK pts Line23m0 = true := by decide +kernel
def Line23m1 : Macro := { x0 := (966518636544), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7584638172015782945448812941),(4717949637584464689988108288),(4860022705634645835776),(0),(886973340089086509056),(4288529510387843)), boxes := [
    (((966501859328),(966535413760),(0),(0)),((644334572885),(644356942507),(-7296846131),(0)))
] }
theorem Line23m1_far : farOK pts Line23m1 := by decide +kernel
theorem Line23m1_ok : axisOK pts Line23m1 = true := by decide +kernel
def Line23m2 : Macro := { x0 := (966552190976), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7589241450600821460646600746),(4717811886314210978506866688),(4860166820822721691648),(0),(886973340089086509056),(4288271683695461)), boxes := [
    (((966535413760),(966568968192),(0),(0)),((644356942506),(644379312128),(-7296849330),(0)))
] }
theorem Line23m2_far : farOK pts Line23m2 := by decide +kernel
theorem Line23m2_ok : axisOK pts Line23m2 = true := by decide +kernel
def Line23m3 : Macro := { x0 := (966585745408), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7593844790121349690143295122),(4717674224991380307340296192),(4860310936010797547520),(0),(886973340089086509056),(4288013948284871)), boxes := [
    (((966568968192),(966602522624),(0),(0)),((644379312128),(644401681750),(-7296852163),(0)))
] }
theorem Line23m3_far : farOK pts Line23m3 := by decide +kernel
theorem Line23m3_ok : axisOK pts Line23m3 = true := by decide +kernel
def Line23m4 : Macro := { x0 := (966619299840), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7598449458380751802611029442),(4717536705037844872763670528),(4860455051198873403392),(0),(886973340089086509056),(4287756370799077)), boxes := [
    (((966602522624),(966636077056),(0),(0)),((644401681749),(644424051371),(-7296855321),(0)))
] }
theorem Line23m4_far : farOK pts Line23m4 := by decide +kernel
theorem Line23m4_ok : axisOK pts Line23m4 = true := by decide +kernel
def Line23m5 : Macro := { x0 := (966652854272), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7603060321001838038091731411),(4717399045506224826534330368),(4860599166386949259264),(0),(886973340089086509056),(4287498672604761)), boxes := [
    (((966636077056),(966669631488),(0),(0)),((644424051370),(644446420992),(-7296858714),(0)))
] }
theorem Line23m5_far : farOK pts Line23m5 := by decide +kernel
theorem Line23m5_ok : axisOK pts Line23m5 = true := by decide +kernel
def Line23m6 : Macro := { x0 := (966686408704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7607664042765555509113439061),(4717261768619681466909458432),(4860743281575025115136),(0),(886973340089086509056),(4287241333499182)), boxes := [
    (((966669631488),(966703185920),(0),(0)),((644446420992),(644468790614),(-7296861888),(0)))
] }
theorem Line23m6_far : farOK pts Line23m6 := by decide +kernel
theorem Line23m6_ok : axisOK pts Line23m6 = true := by decide +kernel
def Line23m7 : Macro := { x0 := (966719963136), y0 := (0), i0 := 1200, i1 := 1200, fd := ((7612266050573911397162545985),(4717123978224003103736725504),(4860887396763100971008),(0),(886973340089086509056),(4286983563524669)), boxes := [
    (((966703185920),(966736740352),(0),(0)),((644468790613),(644491160235),(-7296864655),(0)))
] }
theorem Line23m7_far : farOK pts Line23m7 := by decide +kernel
theorem Line23m7_ok : axisOK pts Line23m7 = true := by decide +kernel
def Line23Data : List Macro := [Line23m0,Line23m1,Line23m2,Line23m3,Line23m4,Line23m5,Line23m6,Line23m7]
theorem Line23_farAll : ∀ m ∈ Line23Data, farOK pts m := by
  intro m hm
  simp only [Line23Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line23m0_far,Line23m1_far,Line23m2_far,Line23m3_far,Line23m4_far,Line23m5_far,Line23m6_far,Line23m7_far]
theorem Line23_okAll : ∀ m ∈ Line23Data, axisOK pts m = true := by
  intro m hm
  simp only [Line23Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line23m0_ok,Line23m1_ok,Line23m2_ok,Line23m3_ok,Line23m4_ok,Line23m5_ok,Line23m6_ok,Line23m7_ok]
end CatalanCore.Cert.SigmaQuarter
