module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line7m0 : Macro := { x0 := (950932602880), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5429863255683680651687213731),(4782747980779714916657266688),(4793081200773410783232),(0),(886973340089086509056),(4410797806416586)), boxes := [
    (((950798385152),(951066820608),(0),(0)),((633865590101),(634044547072),(-7294530421),(0)))
] }
theorem Line7m0_far : farOK pts Line7m0 := by decide +kernel
theorem Line7m0_ok : axisOK pts Line7m0 = true := by decide +kernel
def Line7m1 : Macro := { x0 := (951201038336), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5467231031215258513376919227),(4781616661510063055366258688),(4794234122278017630208),(0),(886973340089086509056),(4408647571069268)), boxes := [
    (((951066820608),(951335256064),(0),(0)),((634044547072),(634223504043),(-7294660494),(0)))
] }
theorem Line7m1_far : farOK pts Line7m1 := by decide +kernel
theorem Line7m1_ok : axisOK pts Line7m1 = true := by decide +kernel
def Line7m2 : Macro := { x0 := (951469473792), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5504587279565637032071151048),(4780486024343621121023082496),(4795387043782624477184),(0),(886973340089086509056),(4406499054408718)), boxes := [
    (((951335256064),(951603691520),(0),(0)),((634223504042),(634402461014),(-7294788076),(0)))
] }
theorem Line7m2_far : farOK pts Line7m2 := by decide +kernel
theorem Line7m2_ok : axisOK pts Line7m2 = true := by decide +kernel
def Line7m3 : Macro := { x0 := (951737909248), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5541925562321043952104118887),(4779356107631452355151527936),(4796539965287231324160),(0),(886973340089086509056),(4404352282173328)), boxes := [
    (((951603691520),(951872126976),(0),(0)),((634402461013),(634581417984),(-7294914607),(0)))
] }
theorem Line7m3_far : farOK pts Line7m3 := by decide +kernel
theorem Line7m3_ok : axisOK pts Line7m3 = true := by decide +kernel
def Line7m4 : Macro := { x0 := (952006344704), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5579258788229410460488672894),(4778226614894344882331648000),(4797692886791838171136),(0),(886973340089086509056),(4402206973540060)), boxes := [
    (((951872126976),(952140562432),(0),(0)),((634581417984),(634760374955),(-7295040748),(0)))
] }
theorem Line7m4_far : farOK pts Line7m4 := by decide +kernel
theorem Line7m4_ok : axisOK pts Line7m4 = true := by decide +kernel
def Line7m5 : Macro := { x0 := (952274780160), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5616586027204085289892622557),(4777097797733836429042778112),(4798845808296445018112),(0),(886973340089086509056),(4400063373648296)), boxes := [
    (((952140562432),(952408997888),(0),(0)),((634760374954),(634939331926),(-7295163045),(0)))
] }
theorem Line7m5_far : farOK pts Line7m5 := by decide +kernel
theorem Line7m5_ok : axisOK pts Line7m5 = true := by decide +kernel
def Line7m6 : Macro := { x0 := (952543215616), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5653888425028655858264553065),(4775969272210596587123310592),(4799998729801051865088),(0),(886973340089086509056),(4397921131711549)), boxes := [
    (((952408997888),(952677433344),(0),(0)),((634939331925),(635118288896),(-7295286161),(0)))
] }
theorem Line7m6_far : farOK pts Line7m6 := by decide +kernel
theorem Line7m6_ok : axisOK pts Line7m6 = true := by decide +kernel
def Line7m7 : Macro := { x0 := (952811651072), y0 := (0), i0 := 1200, i1 := 1200, fd := ((5691194625220516905350947922),(4774841287650372610821390336),(4801151651305658712064),(0),(886973340089086509056),(4395780464385696)), boxes := [
    (((952677433344),(952945868800),(0),(0)),((635118288896),(635297245867),(-7295405479),(0)))
] }
theorem Line7m7_far : farOK pts Line7m7 := by decide +kernel
theorem Line7m7_ok : axisOK pts Line7m7 = true := by decide +kernel
def Line7Data : List Macro := [Line7m0,Line7m1,Line7m2,Line7m3,Line7m4,Line7m5,Line7m6,Line7m7]
theorem Line7_farAll : ∀ m ∈ Line7Data, farOK pts m := by
  intro m hm
  simp only [Line7Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line7m0_far,Line7m1_far,Line7m2_far,Line7m3_far,Line7m4_far,Line7m5_far,Line7m6_far,Line7m7_far]
theorem Line7_okAll : ∀ m ∈ Line7Data, axisOK pts m = true := by
  intro m hm
  simp only [Line7Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line7m0_ok,Line7m1_ok,Line7m2_ok,Line7m3_ok,Line7m4_ok,Line7m5_ok,Line7m6_ok,Line7m7_ok]
end CatalanCore.Cert.SigmaQuarter
