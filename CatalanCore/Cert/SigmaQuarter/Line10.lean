module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line10m0 : Macro := { x0 := (957307944960), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6314805678324672117005843253),(4756028298082390679324786688),(4820463086507823398912),(0),(886973340089086509056),(4360157913584266)), boxes := [
    (((957240836096),(957375053824),(0),(0)),((638160557397),(638250035883),(-7295838207),(0)))
] }
theorem Line10m0_far : farOK pts Line10m0 := by decide +kernel
theorem Line10m0_ok : axisOK pts Line10m0 = true := by decide +kernel
def Line10m1 : Macro := { x0 := (957442162688), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6333397860451776764068563667),(4755469140204586002515689472),(4821039547260126822400),(0),(886973340089086509056),(4359101367431935)), boxes := [
    (((957375053824),(957509271552),(0),(0)),((638250035882),(638339514368),(-7295886903),(0)))
] }
theorem Line10m1_far : farOK pts Line10m1 := by decide +kernel
theorem Line10m1_ok : axisOK pts Line10m1 = true := by decide +kernel
def Line10m2 : Macro := { x0 := (957576380416), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6351968379776557362078332070),(4754909861451072040199520256),(4821616008012430245888),(0),(886973340089086509056),(4358044992021256)), boxes := [
    (((957509271552),(957643489280),(0),(0)),((638339514368),(638428992854),(-7295929588),(0)))
] }
theorem Line10m2_far : farOK pts Line10m2 := by decide +kernel
theorem Line10m2_ok : axisOK pts Line10m2 = true := by decide +kernel
def Line10m3 : Macro := { x0 := (957710598144), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6370540491618451238844916655),(4754351006339375926416179200),(4822192468764733669376),(0),(886973340089086509056),(4356989259203696)), boxes := [
    (((957643489280),(957777707008),(0),(0)),((638428992853),(638518471339),(-7295973104),(0)))
] }
theorem Line10m3_far : farOK pts Line10m3 := by decide +kernel
theorem Line10m3_ok : axisOK pts Line10m3 = true := by decide +kernel
def Line10m4 : Macro := { x0 := (957844815872), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6389109154325130316231267458),(4753791943902392194595618816),(4822768929517037092864),(0),(886973340089086509056),(4355933600311631)), boxes := [
    (((957777707008),(957911924736),(0),(0)),((638518471338),(638607949824),(-7296012190),(0)))
] }
theorem Line10m4_far : farOK pts Line10m4 := by decide +kernel
theorem Line10m4_ok : axisOK pts Line10m4 = true := by decide +kernel
def Line10m5 : Macro := { x0 := (957979033600), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6407679831494878721830408134),(4753233247657371658977345536),(4823345390269340516352),(0),(886973340089086509056),(4354878554745102)), boxes := [
    (((957911924736),(958046142464),(0),(0)),((638607949824),(638697428310),(-7296054714),(0)))
] }
theorem Line10m5_far : farOK pts Line10m5 := by decide +kernel
theorem Line10m5_ok : axisOK pts Line10m5 = true := by decide +kernel
def Line10m6 : Macro := { x0 := (958113251328), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6426248709084719563790202359),(4752674591042001332618461184),(4823921851021643939840),(0),(886973340089086509056),(4353823801544364)), boxes := [
    (((958046142464),(958180360192),(0),(0)),((638697428309),(638786906795),(-7296096059),(0)))
] }
theorem Line10m6_far : farOK pts Line10m6 := by decide +kernel
theorem Line10m6_ok : axisOK pts Line10m6 = true := by decide +kernel
def Line10m7 : Macro := { x0 := (958247469056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((6444810658144027482941101490),(4752116148856118398488084480),(4824498311773947363328),(0),(886973340089086509056),(4352769503903818)), boxes := [
    (((958180360192),(958314577920),(0),(0)),((638786906794),(638876385280),(-7296138069),(0)))
] }
theorem Line10m7_far : farOK pts Line10m7 := by decide +kernel
theorem Line10m7_ok : axisOK pts Line10m7 = true := by decide +kernel
def Line10Data : List Macro := [Line10m0,Line10m1,Line10m2,Line10m3,Line10m4,Line10m5,Line10m6,Line10m7]
theorem Line10_farAll : ∀ m ∈ Line10Data, farOK pts m := by
  intro m hm
  simp only [Line10Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line10m0_far,Line10m1_far,Line10m2_far,Line10m3_far,Line10m4_far,Line10m5_far,Line10m6_far,Line10m7_far]
theorem Line10_okAll : ∀ m ∈ Line10Data, axisOK pts m = true := by
  intro m hm
  simp only [Line10Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line10m0_ok,Line10m1_ok,Line10m2_ok,Line10m3_ok,Line10m4_ok,Line10m5_ok,Line10m6_ok,Line10m7_ok]
end CatalanCore.Cert.SigmaQuarter
