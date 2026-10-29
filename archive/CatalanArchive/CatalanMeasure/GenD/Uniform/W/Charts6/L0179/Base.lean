module
public import CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8
public import CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Geom146
public import CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
public import CatalanMeasure.GenD.Uniform.W.Charts4.Extras
@[expose] public section
set_option Elab.async false

/-!
# L0179 packet (window `(11, 78/7]`, `A`-low, J from 0): base facts

Packet `Pk.L0179_k89_8.pk` (28 coordinates = the profile coordinates for 6 blocks, 2 graph coordinates).
Coordinates: block `k = 0..5` (absolute block `k-1`): `A:F = 4k`, `A:E = 4k+1`, `C:F = 4k+2`, `C:E = 4k+3`; centre `Z:F = 24`, `Z:E = 25`;
graph `jet_0 = 26`, `@low:raw[0,1] = 27`.  The `bottom_virtual` rows are `E_zero` (point 0, order `p`) and `F_degree` (`∞`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0179
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.Parametric
noncomputable section

/-- Local names for the packet module (avoids ambiguity with other `Win`, `wInt`, ... in opened namespaces). -/
abbrev pk := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk
abbrev Win := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.Win
abbrev wInt := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt
abbrev wNat := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wNat
abbrev cNat := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.cNat
abbrev chart := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.chart
abbrev pk_len := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk_len

abbrev dsg : Parameters := CatalanMeasure.GenD.D58.Odd.design

theorem pk_n : pk.n = 28 := rfl
theorem pk_d : pk.d = 4 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk_d

/-! ### Widths -/

def wd (N p i : ℕ) : ℕ := ((wInt N p).getD i 0).toNat

theorem wNat_eq (g : Fin pk.charts.length) (N p : ℕ) : wNat g N p = wd N p g.val := rfl

section widths
variable {N p : ℕ}
theorem wd0 (h : Win N p) : wd N p 0 = (p - 1) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd1 (h : Win N p) : wd N p 1 = 78 * N - 7 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd2 (h : Win N p) : wd N p 2 = p - 9 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd3 (h : Win N p) : wd N p 3 = 7 * p - 69 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd4 (h : Win N p) : wd N p 4 = 3 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega

theorem wd5 (h : Win N p) : wd N p 5 = p - 6 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd6 (h : Win N p) : wd N p 6 = 6 * N - (p - 1) / 2 - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd7 (h : Win N p) : wd N p 7 = p - 8 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd8 (h : Win N p) : wd N p 8 = 5 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega

theorem wd9 (h : Win N p) : wd N p 9 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]
theorem wd10 (h : Win N p) : wd N p 10 = 5 * p - 53 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
theorem wd11 (h : Win N p) : wd N p 11 = 2 * p - 22 * N - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.wInt]; omega
end widths

/-! ### Geometry of the window -/

section geom
variable {N p : ℕ}
theorem geom_k0 (h : Win N p) : gk0 (dsg.g N) p = -1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : (0 : ℤ) < p := by omega
  unfold gk0
  rw [Pilot146O.design_g]
  exact ((Int.ediv_emod_unique (r := (p : ℤ) - 5 * N) hp).mpr ⟨by push_cast; ring, by omega, by omega⟩).1

theorem geom_k1 (h : Win N p) : gk1 (dsg.n N) (dsg.g N) p = 4 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : (0 : ℤ) < p := by omega
  unfold gk1
  rw [Pilot146O.design_n, Pilot146O.design_g]
  exact ((Int.ediv_emod_unique (r := 53 * (N : ℤ) - 1 - 4 * p) hp).mpr ⟨by push_cast; ring, by omega, by omega⟩).1

theorem geom_b (h : Win N p) : gb (dsg.n N) (dsg.g N) p = 6 := by
  have := geom_k0 h; have := geom_k1 h
  unfold gb; rw [‹gk1 _ _ _ = 4›, ‹gk0 _ _ = -1›]; rfl

theorem geom_bN (h : Win N p) : bN dsg N p = 6 := geom_b h

theorem geom_ja (h : Win N p) : gja (dsg.g N) p = p - 5 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold gja; rw [geom_k0 ⟨h1, h2, h3, h4⟩, Pilot146O.design_g]; omega

theorem geom_rho (h : Win N p) : grho (dsg.n N) (dsg.g N) p = 53 * N - 1 - 4 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold grho; rw [geom_k1 ⟨h1, h2, h3, h4⟩, Pilot146O.design_n, Pilot146O.design_g]; omega

theorem geom_hmod (h : Win N p) : dsg.h N % p = 3 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Pilot146O.design_h]; exact Nat.mod_eq_of_lt (by omega)

theorem geom_hdiv (h : Win N p) : dsg.h N / p = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [Pilot146O.design_h]; exact Nat.div_eq_of_lt (by omega)

theorem design_q (N : ℕ) : dsg.q N = 3 * N := rfl
theorem design_H (N : ℕ) : dsg.H N = 78 * N := CatalanMeasure.GenD.D58.Odd.design_H N
theorem design_L (N : ℕ) : dsg.L N = 70 * N := CatalanMeasure.GenD.D58.Odd.design_L N
theorem design_b (N : ℕ) : dsg.b N = 9 * N := by
  simp [Parameters.b, Parameters.C, Parameters.L, Parameters.n, Parameters.q,
    Parameters.g, Parameters.h, dsg, CatalanMeasure.GenD.D58.Odd.design]; try ring

theorem geom_qmod (h : Win N p) : dsg.q N % p = 3 * N := by
  rw [design_q]; exact Nat.mod_eq_of_lt (by have := h.2.1; have := h.1; omega)
theorem geom_qdiv (h : Win N p) : dsg.q N / p = 0 := by
  rw [design_q]; exact Nat.div_eq_of_lt (by have := h.2.1; have := h.1; omega)

theorem hKp (hW : Win N p) : 28 = bN dsg N p * 4 + 2 + 2 := by
  have : bN dsg N p = 6 := geom_b hW
  rw [this]
end geom

/-! ### Row incidence data (kernel checked) -/

def oRows (g : ℕ) : List (List ℤ) := (chart g).rows

theorem chart_rows (g : Fin pk.charts.length) : (pk.chart g).rows = oRows g.val := by
  obtain ⟨i, hi⟩ := g
  have : i < 12 := lt_of_lt_of_eq hi pk_len
  simp [CatalanMeasure.GenD.Uniform.W.Prof.Packet.chart, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0179_k89_8.pk, List.getElem_map, List.getElem_range, oRows]

/-- The unit row `e_c` (28 coordinates). -/
def unitL (c : ℕ) : List ℤ := (List.range 28).map fun k => if k = c then 1 else 0
/-- The row `e_a - 2 e_b`. -/
def diff2L (a b : ℕ) : List ℤ := (List.range 28).map fun k => (if k = a then 1 else 0) - (if k = b then 2 else 0)
/-- The row `e_1 - e_3 + e_25` (bottom virtual, `E_zero`). -/
def virtEL : List ℤ := (List.range 28).map fun k =>
  (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0) + (if k = 25 then 1 else 0)
/-- The row `e_0 - e_2 + e_24` (bottom virtual, `F_degree`). -/
def virtFL : List ℤ := (List.range 28).map fun k =>
  (if k = 0 then 1 else 0) - (if k = 2 then 1 else 0) + (if k = 24 then 1 else 0)
/-- The top virtual row `e_21 + e_23`. -/
def virtTL : List ℤ := (List.range 28).map fun k => (if k = 21 then 1 else 0) + (if k = 23 then 1 else 0)

def hasRow (g : ℕ) (r : List ℤ) : Bool := (oRows g).contains r

set_option maxRecDepth 100000 in
theorem pt1_AF : ∀ k : Fin 6, hasRow 4 (unitL (4 * k)) = true ∧ hasRow 5 (unitL (4 * k)) = true ∧
    hasRow 6 (unitL (4 * k)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_ZF : hasRow 4 (unitL 24) = true ∧ hasRow 5 (unitL 24) = true ∧ hasRow 6 (unitL 24) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_CF : ∀ k : Fin 6, hasRow 4 (unitL (4 * k + 2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_jet0 : hasRow 4 (unitL 26) = true ∧ hasRow 5 (unitL 26) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_C : ∀ k : Fin 6, hasRow 0 (diff2L (4 * k + 2) (4 * k + 3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_Z : hasRow 0 (diff2L 24 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt0_vE : hasRow 1 virtEL = true ∧ hasRow 2 virtEL = true ∧ hasRow 3 virtEL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_AE : ∀ k : Fin 6, hasRow 7 (unitL (4 * k + 1)) = true ∧ hasRow 8 (unitL (4 * k + 1)) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem inf_ZE : hasRow 7 (unitL 25) = true ∧ hasRow 8 (unitL 25) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_CE : ∀ k : Fin 6, hasRow 7 (unitL (4 * k + 3)) = true ∧ hasRow 8 (unitL (4 * k + 3)) = true ∧
    hasRow 9 (unitL (4 * k + 3)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtF : hasRow 7 virtFL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtT : hasRow 7 virtTL = true ∧ hasRow 8 virtTL = true ∧ hasRow 9 virtTL = true ∧
    hasRow 10 virtTL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_low : hasRow 7 (unitL 27) = true ∧ hasRow 8 (unitL 27) = true ∧ hasRow 9 (unitL 27) = true ∧
    hasRow 10 (unitL 27) = true ∧ hasRow 11 (unitL 27) = true := by decide +kernel

end
end CatalanMeasure.GenD.Uniform.W.Charts6.L0179
