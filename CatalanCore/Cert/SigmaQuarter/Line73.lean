module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line73m0 : Macro := { x0 := (1087700467712), y0 := (0), i0 := 1200, i1 := 1200, fd := ((23404915702524601745113156635),(4268383853860172571282767872),(5380494707370599317504),(0),(886973340089086509056),(3490439677191402)), boxes := [
    (((1075889307648),(1078036791296),(0),(0)),((717259538432),(718691194198),(-7129349838),(0))),
    (((1078036791296),(1080184274944),(0),(0)),((718691194197),(720122849963),(-7119445045),(0))),
    (((1080184274944),(1082331758592),(0),(0)),((720122849962),(721554505728),(-7109110546),(0))),
    (((1082331758592),(1084479242240),(0),(0)),((721554505728),(722986161494),(-7098298299),(0))),
    (((1084479242240),(1086626725888),(0),(0)),((722986161493),(724417817259),(-7086951295),(0))),
    (((1086626725888),(1088774209536),(0),(0)),((724417817258),(725849473024),(-7075007798),(0))),
    (((1088774209536),(1090921693184),(0),(0)),((725849473024),(727281128790),(-7062388896),(0))),
    (((1090921693184),(1093069176832),(0),(0)),((727281128789),(728712784555),(-7048964738),(0))),
    (((1093069176832),(1095216660480),(0),(0)),((728712784554),(730144440320),(-7034590220),(0))),
    (((1095216660480),(1097364144128),(0),(0)),((730144440320),(731576096086),(-7019212395),(0))),
    (((1097364144128),(1099511627776),(0),(0)),((731576096085),(733007751851),(-7158744757),(0)))
] }
theorem Line73m0_far : farOK pts Line73m0 := by decide +kernel
theorem Line73m0_ok : axisOK pts Line73m0 = true := by decide +kernel
def Line73Data : List Macro := [Line73m0]
theorem Line73_farAll : ∀ m ∈ Line73Data, farOK pts m := by
  intro m hm
  simp only [Line73Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Line73m0_far]
theorem Line73_okAll : ∀ m ∈ Line73Data, axisOK pts m = true := by
  intro m hm
  simp only [Line73Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl
  exacts [Line73m0_ok]
end CatalanCore.Cert.SigmaQuarter
