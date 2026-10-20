module

public import CatalanFrames.P6Hybrid.Admissible
public import CatalanCore.Rect.MinorContent

@[expose] public section

open CatalanCore CatalanCore.Rect CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

/-- All common-node deletions share the base family's tropical denominator. -/
theorem p6_minor_content (d : ℕ) :
    HasContent (commonMinorFam p6Frame P6Adm9 d) (10339 / 3072) :=
  hasContent_commonMinorFam p6Inst P6Adm9 d _ (p6_log_Dhyb_uniform (fun _ _ h => h))

end CatalanFrames.P6Hybrid
