module

public import CatalanCore.Zeta5.Data.CheckA1
public import CatalanCore.Zeta5.Data.CheckA2
public import CatalanCore.Zeta5.Data.CheckA3
public import CatalanCore.Zeta5.Data.CheckA4
public import CatalanCore.Zeta5.Data.CheckB

@[expose] public section
set_option maxRecDepth 100000

namespace CatalanCore.Zeta5.Data
open CatalanCore.Zeta5.Cells

theorem allA_cons {p : CellA → Bool} {a : CellA} {l : List CellA} (h : p a = true)
    (hl : l.all p = true) : (a :: l).all p = true := by simp [h, hl]

theorem allB_cons {p : CellB → Bool} {a : CellB} {l : List CellB} (h : p a = true)
    (hl : l.all p = true) : (a :: l).all p = true := by simp [h, hl]

theorem cellsA_ok : cellsOkA desA tabA cellsA = true :=
  allA_cons okA_000 (allA_cons okA_001 (allA_cons okA_002 (allA_cons okA_003 (allA_cons okA_004 (allA_cons okA_005 (allA_cons okA_006 (allA_cons okA_007 (allA_cons okA_008 (allA_cons okA_009 (allA_cons okA_010 (allA_cons okA_011 (allA_cons okA_012 (allA_cons okA_013 (allA_cons okA_014 (allA_cons okA_015 (allA_cons okA_016 (allA_cons okA_017 (allA_cons okA_018 (allA_cons okA_019 (allA_cons okA_020 (allA_cons okA_021 (allA_cons okA_022 (allA_cons okA_023 (allA_cons okA_024 (allA_cons okA_025 (allA_cons okA_026 (allA_cons okA_027 (allA_cons okA_028 (allA_cons okA_029 (allA_cons okA_030 (allA_cons okA_031 (allA_cons okA_032 (allA_cons okA_033 (allA_cons okA_034 (allA_cons okA_035 (allA_cons okA_036 (allA_cons okA_037 (allA_cons okA_038 (allA_cons okA_039 (allA_cons okA_040 (allA_cons okA_041 (allA_cons okA_042 (allA_cons okA_043 (allA_cons okA_044 (allA_cons okA_045 (allA_cons okA_046 (allA_cons okA_047 (allA_cons okA_048 (allA_cons okA_049 (allA_cons okA_050 (allA_cons okA_051 (allA_cons okA_052 (allA_cons okA_053 (allA_cons okA_054 (allA_cons okA_055 (allA_cons okA_056 (allA_cons okA_057 (allA_cons okA_058 (allA_cons okA_059 (allA_cons okA_060 (allA_cons okA_061 (allA_cons okA_062 (allA_cons okA_063 (allA_cons okA_064 (allA_cons okA_065 (allA_cons okA_066 (allA_cons okA_067 (allA_cons okA_068 (allA_cons okA_069 (allA_cons okA_070 (allA_cons okA_071 (allA_cons okA_072 (allA_cons okA_073 (allA_cons okA_074 (allA_cons okA_075 (allA_cons okA_076 (allA_cons okA_077 (allA_cons okA_078 (allA_cons okA_079 (allA_cons okA_080 (allA_cons okA_081 (allA_cons okA_082 (allA_cons okA_083 (allA_cons okA_084 (allA_cons okA_085 (allA_cons okA_086 (allA_cons okA_087 (allA_cons okA_088 (allA_cons okA_089 (allA_cons okA_090 (allA_cons okA_091 (allA_cons okA_092 (allA_cons okA_093 (allA_cons okA_094 (allA_cons okA_095 (allA_cons okA_096 (allA_cons okA_097 (allA_cons okA_098 (allA_cons okA_099 (rfl))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

theorem cellsB_ok : cellsOkB desB tabB cellsB = true :=
  allB_cons okB_000 (allB_cons okB_001 (allB_cons okB_002 (allB_cons okB_003 (allB_cons okB_004 (allB_cons okB_005 (allB_cons okB_006 (allB_cons okB_007 (allB_cons okB_008 (allB_cons okB_009 (rfl))))))))))

noncomputable section

open Set CatalanCore.Zeta5.Potential

theorem wCellA : ∀ k < desA.ws.length,
    (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ)) k = ((desA.ws.getD k 0 : ℚ) : ℝ) := by
  intro k hk
  have hk' : k < 60 := by simpa [desA, wsList_length] using hk
  exact wR_eq k hk'

theorem wCellB : ∀ k < desB.ws.length,
    (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ)) k = ((desB.ws.getD k 0 : ℚ) : ℝ) := by
  intro k hk
  have hk' : k < 60 := by simpa [desB, wsList_length] using hk
  exact wR_eq k hk'

/-- **ZD17 at the design**: region A. -/
theorem zd17_design :
    ZD17 (cR 0) (43 / 50) (3 / 40) (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ)) 60 (desA.M0 : ℝ) := by
  have h := regionA_sound desA tabA (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ))
    (by norm_num [desA]) (by norm_num [desA]) wCellA rfl rfl rfl rfl rfl rfl L0q_enc
    cellsA coverA_ok cellsA_ok
  have e1 : ((desA.lam : ℚ) : ℝ) = cR 0 := by rw [cR_zero]; norm_num [desA]
  have e2 : ((desA.yb : ℚ) : ℝ) = 43 / 50 := by norm_num [desA]
  have e3 : ((desA.α : ℚ) : ℝ) = 3 / 40 := by norm_num [desA]
  have e4 : desA.ws.length = 60 := wsList_length
  rw [e1, e2, e3, e4] at h
  exact h

/-- **ZD18 at the design**: region B. -/
theorem zd18_design :
    ZD18 (cR 0) (43 / 50) (3 / 40) (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ)) 60 (desA.M0 : ℝ) := by
  have h := regionB_sound desB tabB (fun k => cR (k + 1) / ((k + 1 : ℕ) : ℝ))
    desOkB_design wCellB rfl rfl rfl rfl rfl L0q_enc
    cellsB coverB_ok cellsB_ok
  have e1 : ((desB.lam : ℚ) : ℝ) = cR 0 := by rw [cR_zero]; norm_num [desB]
  have e2 : ((desB.yb : ℚ) : ℝ) = 43 / 50 := by norm_num [desB]
  have e3 : ((desB.α : ℚ) : ℝ) = 3 / 40 := by norm_num [desB]
  have e4 : desB.ws.length = 60 := wsList_length
  have e5 : ((desB.M0 : ℚ) : ℝ) = (desA.M0 : ℝ) := rfl
  rw [e1, e2, e3, e4, e5] at h
  exact h

end

end CatalanCore.Zeta5.Data
