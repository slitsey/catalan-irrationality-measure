module

public import CatalanCore.Zeta5.Cells.Bridge
public import CatalanCore.Zeta5.Cells.Data
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option maxRecDepth 100000

/-!
# Z5-DATA, part 1: the design

The sum-of-squares design `h_0, …, h_60` (integers) of the comparison density, `c_k = (λ/a_0) a_k`
with `a_0 = Σ h_j²`, `a_k = 2 Σ h_j h_{j+k}` (`Potential.sosCoef`), `λ = 37/40`, `N = 60`,
`y_b = 43/50`, `α = 3/40`.  The weights `ws = (c_k / k)` are a literal (`decodeQ raw_ints%`) checked
once against the integer formula (`ws_formula`).  The tables `TabA`/`TabB` are computed from `ws`
(`wTabAux`, `wTabB`, `trA`) and the enclosure `L0` of `log (y_b²/4)` (`logQ 6`).
-/

namespace CatalanCore.Zeta5.Data

open Set CatalanCore.Zeta5.Cells CatalanCore.Zeta5.Potential CatalanMeasure.CellCert
  CatalanMeasure.GenD.Signed.LogEval

/-! ### integer data -/

def hRaw : List ℤ := raw_ints% [
    -2573, -2919, -6471, -5888, -9709, -7666, -11642, -7983, -12228, -6948, -11703, -4857, -10404, -2091, -8745,
    955, -7102, 3966, -5799, 6657, -5054, 8855, -5008, 10526, -5663, 11703, -6985, 12479, -8878, 13004, -11177,
    13504, -13672, 14217, -16175, 15364, -18509, 17140, -20540, 19677, -22210, 22975, -23579, 26913, -24772, 31207,
    -25916, 35396, -27049, 38715, -27836, 39816, -26914, 35753, -19878, 18099, 9651, -50147, 166898, -717730,
    673554]

def hI (j : ℕ) : ℤ := hRaw.getD j 0

/-- `a_0 = Σ_{j ≤ 60} h_j²`, `a_k = 2 Σ_{j ≤ 60 − k} h_j h_{j+k}` -/
def aI (k : ℕ) : ℤ :=
  if k = 0 then ∑ j ∈ Finset.range (60 + 1), hI j ^ 2
  else 2 * ∑ j ∈ Finset.range (60 + 1 - k), hI j * hI (j + k)

/-- the weights `ws_k = c_{k+1} / (k+1)`, `k = 0..59`, as reduced fractions -/
def wsList : List ℚ := decodeQ raw_ints% [
    -23199153051721, 20340816151600, 6142451406771, 40681632303200, -623907457973, 20340816151600, 70431562343,
    40681632303200, 777184405077, 101704080758000, -1176426308791, 122044896909600, 210135508109, 20340816151600,
    -217772842537, 23246647030400, 22582191389, 2542602018950, -156409299801, 20340816151600, 159037648303,
    22374897766760, -1865582291, 305112242274, 741867053559, 132215304985400, -1381975172987, 284771426122400,
    32231314533, 7264577197000, -1261955108007, 325453058425600, 610566473201, 172896937288600, -1144113839383,
    366134690728800, 1095318175743, 386475506880400, -1033371096831, 406816323032000, 245009533397,
    106789284795900, -116347583249, 55937244416900, 54751840427, 29239923217925, -278765796677, 162726529212800,
    97937102973, 63565050473750, -53535809157, 37775801424400, 175309480331, 137300509023300, -335053338051,
    284771426122400, 313884415053, 294941834198200, -21352358231, 21793731591000, 280776020589, 315282650349800,
    -1520228731, 1859731762432, 6514155583, 8717492636400, -236191673343, 345793874577200, 223316423777,
    355964282653000, -418689113519, 732269381457600, 10700629549, 20340816151600, -11571655169, 24154719180025,
    12457729097, 28331851068300, -20401334577, 50852040379000, 305259681827, 833973462215600, -95598774679,
    284771426122400, 263633911857, 874655094518800, -25140346747, 89499591067040, 111909633271, 457668363411000,
    -15789856967, 66834110212400, 37075428903, 191203671825040, -38983204033, 195271835055360, 3006588957,
    20340816151600, -34597827429, 203408161516000, 10952390461, 103738162373160, -77180715249, 528861219941600,
    73199169373, 1078063256034800, -22993533709, 183067345364400, 39665532651, 1118744888338000, -60531841529,
    569542852244800, 1693531477, 165632360091600, -49819438433, 589883668396400, -1104309733, 300027038236100,
    -1526738437, 29058308788000]

-- kcost: 60 rational values from 61·61 integer products, < 0.1 s estimated
theorem wsList_length : wsList.length = 60 := by decide +kernel

-- kcost: 60 values of aI (≤ 61 products each) and 60 rational comparisons, < 0.2 s estimated
theorem ws_formula : ∀ k < 60, wsList.getD k 0 =
    (37 / 40 : ℚ) * ((aI (k + 1) : ℤ) : ℚ) / (((aI 0 : ℤ) : ℚ) * ((k + 1 : ℕ) : ℚ)) := by
  decide +kernel

theorem aI_zero_pos : 0 < aI 0 := by decide +kernel

/-! ### the real density -/

noncomputable section

def hR (j : ℕ) : ℝ := ((hI j : ℤ) : ℝ)

/-- `c_k = (λ / a_0) a_k` -/
def cR (k : ℕ) : ℝ := (37 / 40 : ℝ) / (∑ j ∈ Finset.range (60 + 1), hR j ^ 2) * sosCoef hR 60 k

theorem sum_hR : ∑ j ∈ Finset.range (60 + 1), hR j ^ 2 = ((aI 0 : ℤ) : ℝ) := by
  simp only [aI, ite_true, hR]
  push_cast
  rfl

theorem a0_ne : (((aI 0 : ℤ) : ℚ)) ≠ 0 := by
  have := aI_zero_pos
  exact_mod_cast this.ne'

theorem a0R_pos : (0 : ℝ) < ((aI 0 : ℤ) : ℝ) := by exact_mod_cast aI_zero_pos

theorem sosCoef_eq (k : ℕ) : sosCoef hR 60 k = ((aI k : ℤ) : ℝ) := by
  unfold sosCoef aI
  split_ifs with hk
  · simp only [hR]; push_cast; rfl
  · simp only [hR]; push_cast; rfl

theorem hpos_design : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF cR 60 x := by
  intro x hx
  have hs : (0 : ℝ) ≤ (37 / 40 : ℝ) / (∑ j ∈ Finset.range (60 + 1), hR j ^ 2) := by
    rw [sum_hR]; exact div_nonneg (by norm_num) a0R_pos.le
  exact chebF_sos_nonneg hR 60 hs hx

theorem cR_zero : cR 0 = 37 / 40 := by
  have := sos_const_eq hR 60 (37 / 40 : ℝ) (by rw [sum_hR]; exact a0R_pos.ne')
  exact this

theorem cR_succ (k : ℕ) : cR (k + 1) = (37 / 40 : ℝ) * ((aI (k + 1) : ℤ) : ℝ) / ((aI 0 : ℤ) : ℝ) := by
  unfold cR
  rw [sum_hR, sosCoef_eq]
  ring

theorem wR_eq : ∀ k < 60, cR (k + 1) / ((k + 1 : ℕ) : ℝ) = ((wsList.getD k 0 : ℚ) : ℝ) := by
  intro k hk
  rw [ws_formula k hk, cR_succ]
  push_cast
  have h1 : ((aI 0 : ℤ) : ℝ) ≠ 0 := a0R_pos.ne'
  have h2 : ((k : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-! ### the energy `E = Σ c_k² / (2k)` -/

def csList : List ℚ :=
  (List.range 60).map fun k => (37 / 40 : ℚ) * ((aI (k + 1) : ℤ) : ℚ) / ((aI 0 : ℤ) : ℚ)

theorem csList_length : csList.length = 60 := by simp [csList]

def Eq0 : ℚ := energyAux 1 csList

theorem E_eq : ∑ k ∈ Finset.range 60, cR (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ)) = ((Eq0 : ℚ) : ℝ) := by
  have h := energyAux_cast cR csList 1 (fun i hi => by
    have hi' : i < 60 := by simpa [csList] using hi
    rw [show 1 + i = i + 1 by ring, cR_succ]
    simp [csList])
  unfold Eq0
  rw [h, csList_length]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 1 + k = k + 1 by ring]

end

/-! ### the parameters and tables -/

/-- design of region A -/
def desA : DesA := DesA.mk (3 / 40) (43 / 50) (37 / 40) wsList (-3330031 / 500000) 6

/-- design of region B (global pole-distance bounds) -/
def desB : DesB := DesB.mk (3 / 40) (43 / 50) (37 / 40) wsList (-3330031 / 500000) 6 (13189 / 10000) (1079 / 1250)

/-- the enclosure of `log (y_b²/4)` -/
def L0q : ℚ × ℚ := (logQ 6 ((43 / 50 : ℚ) ^ 2 / 4)).getD (0, 0)

def tabA : TabA := TabA.mk (wTabAux 0 0 wsList) (wTabAux 0 1 wsList) (wTabAux 0 2 wsList)
  (wTabAux 0 3 wsList) (wTabAux 0 4 wsList) (trA wsList) L0q

def tabB : TabB := TabB.mk (wTabB 0 0 wsList) (wTabB 0 1 wsList) (wTabB 0 2 wsList)
  (wTabB 0 3 wsList) (wTabB 0 4 wsList) L0q

def cellAOf (l : List ℤ) : CellA :=
  match decodeQ l with
  | [m, r, a, b] => CellA.mk m r a b
  | _ => CellA.mk 0 0 0 0

def cellBOf (l : List ℤ) : CellB :=
  match decodeQ l with
  | [ρ, r, z] => CellB.mk ρ r z
  | _ => CellB.mk 0 0 0

-- kcost: one logQ at series length 6, < 0.05 s estimated
theorem L0q_some : logQ 6 ((43 / 50 : ℚ) ^ 2 / 4) = some L0q := by decide +kernel

theorem desOkB_design : desOkB desB = true := by decide +kernel

noncomputable section

theorem L0q_enc : Enc (Real.log (((43 / 50 : ℚ) : ℝ) ^ 2 / 4)) L0q := by
  have h := (logQ_spec L0q_some).2
  have e : (((43 / 50 : ℚ) ^ 2 / 4 : ℚ) : ℝ) = ((43 / 50 : ℚ) : ℝ) ^ 2 / 4 := by push_cast; ring
  rw [e] at h
  exact h

end

end CatalanCore.Zeta5.Data
