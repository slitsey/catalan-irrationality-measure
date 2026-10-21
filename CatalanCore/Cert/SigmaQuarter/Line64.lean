module

public import CatalanCore.Cert.SigmaQuarter.Data
public import CatalanCore.Cert.SigmaQuarter.Macros

@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def Line64m0 : Macro := { x0 := (982406660096), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9751314398806590698751387501),(4653680526273930250483335168),(4928261247188563591168),(0),(886973340089086509056),(4169071805768955)), boxes := [
    (((982339551232),(982473768960),(0),(0)),((654893034154),(654982512640),(-7296119185),(0)))
] }
theorem Line64m0_far : farOK pts Line64m0 := by decide +kernel
theorem Line64m0_ok : axisOK pts Line64m0 = true := by decide +kernel
def Line64m1 : Macro := { x0 := (982540877824), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9769479777662882709270898089),(4653144858497303098562510848),(4928837707940867014656),(0),(886973340089086509056),(4168083924774305)), boxes := [
    (((982473768960),(982607986688),(0),(0)),((654982512640),(655071991126),(-7296074937),(0)))
] }
theorem Line64m1_far : farOK pts Line64m1 := by decide +kernel
theorem Line64m1_ok : axisOK pts Line64m1 = true := by decide +kernel
def Line64m2 : Macro := { x0 := (982675095552), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9787660336572378003485612664),(4652609452058227729078026240),(4929414168693170438144),(0),(886973340089086509056),(4167096514685903)), boxes := [
    (((982607986688),(982742204416),(0),(0)),((655071991125),(655161469611),(-7296031045),(0)))
] }
theorem Line64m2_far : farOK pts Line64m2 := by decide +kernel
theorem Line64m2_ok : axisOK pts Line64m2 = true := by decide +kernel
def Line64m3 : Macro := { x0 := (982809313280), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9805832294698427880649711105),(4652074312881920051658424320),(4929990629445473861632),(0),(886973340089086509056),(4166109584172820)), boxes := [
    (((982742204416),(982876422144),(0),(0)),((655161469610),(655250948096),(-7295989427),(0)))
] }
theorem Line64m3_far : farOK pts Line64m3 := by decide +kernel
theorem Line64m3_ok : axisOK pts Line64m3 = true := by decide +kernel
def Line64m4 : Macro := { x0 := (982943531008), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9824002729028802711329767837),(4651539296372977182778785792),(4930567090197777285120),(0),(886973340089086509056),(4165123007045999)), boxes := [
    (((982876422144),(983010639872),(0),(0)),((655250948096),(655340426582),(-7295944235),(0)))
] }
theorem Line64m4_far : farOK pts Line64m4 := by decide +kernel
theorem Line64m4_ok : axisOK pts Line64m4 = true := by decide +kernel
def Line64m5 : Macro := { x0 := (983077748736), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9842169431757676581934881070),(4651004196173767322113802240),(4931143550950080708608),(0),(886973340089086509056),(4164136590619491)), boxes := [
    (((983010639872),(983144857600),(0),(0)),((655340426581),(655429905067),(-7295899151),(0)))
] }
theorem Line64m5_far : farOK pts Line64m5 := by decide +kernel
theorem Line64m5_ok : axisOK pts Line64m5 = true := by decide +kernel
def Line64m6 : Macro := { x0 := (983211966464), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9860341684530566595260060927),(4650469419051349014837919744),(4931720011702384132096),(0),(886973340089086509056),(4163150709027766)), boxes := [
    (((983144857600),(983279075328),(0),(0)),((655429905066),(655519383552),(-7295850374),(0)))
] }
theorem Line64m6_far : farOK pts Line64m6 := by decide +kernel
theorem Line64m6_ok : axisOK pts Line64m6 = true := by decide +kernel
def Line64m7 : Macro := { x0 := (983413293056), y0 := (0), i0 := 1200, i1 := 1200, fd := ((9887582178063238657451596959),(4649667333816929577471639552),(4932584702830839267328),(0),(886973340089086509056),(4161672408669332)), boxes := [
    (((983279075328),(983547510784),(0),(0)),((655519383552),(655698340523),(-7297108613),(0)))
] }
theorem Line64m7_far : farOK pts Line64m7 := by decide +kernel
theorem Line64m7_ok : axisOK pts Line64m7 = true := by decide +kernel
def Line64Data : List Macro := [Line64m0,Line64m1,Line64m2,Line64m3,Line64m4,Line64m5,Line64m6,Line64m7]
theorem Line64_farAll : ∀ m ∈ Line64Data, farOK pts m := by
  intro m hm
  simp only [Line64Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line64m0_far,Line64m1_far,Line64m2_far,Line64m3_far,Line64m4_far,Line64m5_far,Line64m6_far,Line64m7_far]
theorem Line64_okAll : ∀ m ∈ Line64Data, axisOK pts m = true := by
  intro m hm
  simp only [Line64Data, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Line64m0_ok,Line64m1_ok,Line64m2_ok,Line64m3_ok,Line64m4_ok,Line64m5_ok,Line64m6_ok,Line64m7_ok]
end CatalanCore.Cert.SigmaQuarter
