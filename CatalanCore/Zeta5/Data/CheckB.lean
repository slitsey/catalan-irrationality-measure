module

public import CatalanCore.Zeta5.Data.CellsDef

@[expose] public section
set_option maxRecDepth 100000

namespace CatalanCore.Zeta5.Data
open CatalanCore.Zeta5.Cells

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_000 : cellOkB desB tabB cellB_000 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_001 : cellOkB desB tabB cellB_001 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_002 : cellOkB desB tabB cellB_002 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_003 : cellOkB desB tabB cellB_003 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_004 : cellOkB desB tabB cellB_004 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_005 : cellOkB desB tabB cellB_005 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_006 : cellOkB desB tabB cellB_006 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_007 : cellOkB desB tabB cellB_007 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_008 : cellOkB desB tabB cellB_008 = true := by
  decide +kernel

-- kcost: 0.44 s per cell measured (pilot), estimated
theorem okB_009 : cellOkB desB tabB cellB_009 = true := by
  decide +kernel

end CatalanCore.Zeta5.Data
