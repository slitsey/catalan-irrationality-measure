module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line62m0 : Macro := { x0 := (980259176448), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9460187939263643160285098545),(4662264533267685474309636096),(4919037875151708815360),(0),(886973340089086509056),(4184922976878918)), boxes := [
    (((980192067584),(980326285312),(0),(0)),((653461378389),(653550856875),(-7296743825),(0)))
] }
theorem Line62m0_far : farOK pts Line62m0 := by decide +kernel
theorem Line62m0_ok : axisOK pts Line62m0 = true := by decide +kernel
def Line62m1 : Macro := { x0 := (980393394176), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9478393153871333678133231410),(4661727182100719338747592704),(4919614335904012238848),(0),(886973340089086509056),(4183929687324459)), boxes := [
    (((980326285312),(980460503040),(0),(0)),((653550856874),(653640335360),(-7296710768),(0)))
] }
theorem Line62m1_far : farOK pts Line62m1 := by decide +kernel
theorem Line62m1_ok : axisOK pts Line62m1 = true := by decide +kernel
def Line62m2 : Macro := { x0 := (980527611904), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9496598715673130083351154652),(4661189797578694126227095552),(4920190796656315662336),(0),(886973340089086509056),(4182936614884815)), boxes := [
    (((980460503040),(980594720768),(0),(0)),((653640335360),(653729813846),(-7296674129),(0)))
] }
theorem Line62m2_far : farOK pts Line62m2 := by decide +kernel
theorem Line62m2_ok : axisOK pts Line62m2 = true := by decide +kernel
def Line62m3 : Macro := { x0 := (980661829632), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9514811364388927295446588517),(4660652579474470399386255360),(4920767257408619085824),(0),(886973340089086509056),(4181943943109014)), boxes := [
    (((980594720768),(980728938496),(0),(0)),((653729813845),(653819292331),(-7296637572),(0)))
] }
theorem Line62m3_far : farOK pts Line62m3 := by decide +kernel
theorem Line62m3_ok : axisOK pts Line62m3 = true := by decide +kernel
def Line62m4 : Macro := { x0 := (980796047360), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9533012000453360173756243095),(4660115616246722772172341248),(4921343718160922509312),(0),(886973340089086509056),(4180951736017221)), boxes := [
    (((980728938496),(980863156224),(0),(0)),((653819292330),(653908770816),(-7296603445),(0)))
] }
theorem Line62m4_far : farOK pts Line62m4 := by decide +kernel
theorem Line62m4_ok : axisOK pts Line62m4 = true := by decide +kernel
def Line62m5 : Macro := { x0 := (980930265088), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9551217413828938568373903908),(4659578639903602173909729280),(4921920178913225932800),(0),(886973340089086509056),(4179959758357701)), boxes := [
    (((980863156224),(980997373952),(0),(0)),((653908770816),(653998249302),(-7296565605),(0)))
] }
theorem Line62m5_far : farOK pts Line62m5 := by decide +kernel
theorem Line62m5_ok : axisOK pts Line62m5 = true := by decide +kernel
def Line62m6 : Macro := { x0 := (981064482816), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9569411219252449176196275866),(4659041767433809731194912768),(4922496639665529356288),(0),(886973340089086509056),(4178968118334370)), boxes := [
    (((980997373952),(981131591680),(0),(0)),((653998249301),(654087727787),(-7296527214),(0)))
] }
theorem Line62m6_far : farOK pts Line62m6 := by decide +kernel
theorem Line62m6_ok : axisOK pts Line62m6 = true := by decide +kernel
def Line62m7 : Macro := { x0 := (981198700544), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9587612189847143450545566733),(4658505167745793678054195200),(4923073100417832779776),(0),(886973340089086509056),(4177976978490060)), boxes := [
    (((981131591680),(981265809408),(0),(0)),((654087727786),(654177206272),(-7296485862),(0)))
] }
theorem Line62m7_far : farOK pts Line62m7 := by decide +kernel
theorem Line62m7_ok : axisOK pts Line62m7 = true := by decide +kernel
def Line62Data : List Macro := [Line62m0,Line62m1,Line62m2,Line62m3,Line62m4,Line62m5,Line62m6,Line62m7]
theorem Line62_farAll : ∀ m ∈ Line62Data, farOK pts m := by
  intro m hm
  simp only [Line62Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line62m0_far,Line62m1_far,Line62m2_far,Line62m3_far,Line62m4_far,Line62m5_far,Line62m6_far,Line62m7_far]
theorem Line62_okAll : ∀ m ∈ Line62Data, axisOK pts m = true := by
  intro m hm
  simp only [Line62Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line62m0_ok,Line62m1_ok,Line62m2_ok,Line62m3_ok,Line62m4_ok,Line62m5_ok,Line62m6_ok,Line62m7_ok]
end CatalanCore.Cert.SigmaQuarter
