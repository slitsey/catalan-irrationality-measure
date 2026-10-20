module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanFrames.P6Hybrid.IntervalContentFinal

@[expose] public section

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- All common-node deletions share the improved periodic content denominator. -/
theorem p6_minor_content (d : ℕ) :
    HasContent (commonMinorFam p6Frame P6Adm9 d) (2159207 / 645120) :=
  p6_interval_minor_content d

end CatalanFrames.P6Hybrid
