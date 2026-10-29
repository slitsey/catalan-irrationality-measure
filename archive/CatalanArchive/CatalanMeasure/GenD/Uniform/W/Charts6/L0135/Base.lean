module
public import CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left
public import CatalanMeasure.GenD.Uniform.W.Charts4.Pilot.Geom146
public import CatalanMeasure.GenD.Uniform.W.Charts4.JetsGeneric
public import CatalanMeasure.GenD.Uniform.W.Charts4.Extras
@[expose] public section
set_option Elab.async false

/-!
# L0135 packet (window `(69/13, 16/3]`, `A`-high, two `@low` coordinates): base facts

Packet `Pk.L0135_left.pk` (37 coordinates, label rows).  Coordinates: block `k = 0..10` (absolute block `k-1`):
`A:E = 3k`, `C:F = 3k+1`, `C:E = 3k+2`; centre `E = 33`; graph `jet_0 = 34`, `@low:raw[13,0] = 35`, `@low:raw[1,1] = 36`.
Profile coordinates (`K = 49`): `A:F = 4k`, `A:E = 4k+1`, `C:F = 4k+2`, `C:E = 4k+3`, `Z:F = 44`, `Z:E = 45`, `jet_0 = 46`, lows `47, 48`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts6.L0135
open Module Polynomial CatalanMeasure.GenD.Uniform.W.Charts4 CatalanMeasure.Parametric
noncomputable section

/-- Local names for the packet module (avoids ambiguity with other `Win`, `wInt`, ... in opened namespaces). -/
abbrev pk := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk
abbrev Win := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.Win
abbrev wInt := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt
abbrev wNat := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wNat
abbrev cNat := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.cNat
abbrev chart := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.chart
abbrev pk_len := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk_len

abbrev dsg : Parameters := CatalanMeasure.GenD.D58.Odd.design

theorem pk_n : pk.n = 37 := rfl
theorem pk_d : pk.d = 1 := CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk_d

/-! ### Widths -/

def wd (N p i : ℕ) : ℕ := ((wInt N p).getD i 0).toNat

theorem wNat_eq (g : Fin pk.charts.length) (N p : ℕ) : wNat g N p = wd N p g.val := rfl

section widths
variable {N p : ℕ}
theorem wd0 (h : Win N p) : wd N p 0 = (p - 1) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd1 (h : Win N p) : wd N p 1 = 78 * N - 14 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd2 (h : Win N p) : wd N p 2 = 2 * p - 9 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd3 (h : Win N p) : wd N p 3 = 3 * N - (p - 1) / 2 - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd4 (h : Win N p) : wd N p 4 = 3 * ((p - 1) / 2) + 2 - 6 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd5 (h : Win N p) : wd N p 5 = 6 * N - p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd6 (h : Win N p) : wd N p 6 = 15 * p - 78 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd7 (h : Win N p) : wd N p 7 = 75 * N - 14 * p := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd8 (h : Win N p) : wd N p 8 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]
theorem wd9 (h : Win N p) : wd N p 9 = 10 * p - 53 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
theorem wd10 (h : Win N p) : wd N p 10 = 48 * N - 9 * p - 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h; simp [wd, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.wInt]; omega
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

theorem geom_k1 (h : Win N p) : gk1 (dsg.n N) (dsg.g N) p = 9 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hp : (0 : ℤ) < p := by omega
  unfold gk1
  rw [Pilot146O.design_n, Pilot146O.design_g]
  exact ((Int.ediv_emod_unique (r := 53 * (N : ℤ) - 1 - 9 * p) hp).mpr ⟨by push_cast; ring, by omega, by omega⟩).1

theorem geom_b (h : Win N p) : gb (dsg.n N) (dsg.g N) p = 11 := by
  have := geom_k0 h; have := geom_k1 h
  unfold gb; rw [‹gk1 _ _ _ = 9›, ‹gk0 _ _ = -1›]; rfl

theorem geom_bN (h : Win N p) : bN dsg N p = 11 := geom_b h

theorem geom_ja (h : Win N p) : gja (dsg.g N) p = p - 5 * N := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold gja; rw [geom_k0 ⟨h1, h2, h3, h4⟩, Pilot146O.design_g]; omega

theorem geom_rho (h : Win N p) : grho (dsg.n N) (dsg.g N) p = 53 * N - 1 - 9 * p := by
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

theorem hKp (hW : Win N p) : 49 = bN dsg N p * 4 + 2 + 3 := by
  have : bN dsg N p = 11 := geom_b hW
  rw [this]
end geom

/-! ### Row incidence data (kernel checked) -/

def oRows (g : ℕ) : List (List ℤ) := (chart g).rows

theorem chart_rows (g : Fin pk.charts.length) : (pk.chart g).rows = oRows g.val := by
  obtain ⟨i, hi⟩ := g
  have : i < 11 := lt_of_lt_of_eq hi pk_len
  simp [CatalanMeasure.GenD.Uniform.W.Prof.Packet.chart, CatalanMeasure.GenD.Uniform.Bank532.Pk.L0135_left.pk, List.getElem_map, List.getElem_range, oRows]

/-- The unit row `e_c` (33 coordinates). -/
def unitL (c : ℕ) : List ℤ := (List.range 37).map fun k => if k = c then 1 else 0
/-- The row `e_a - 2 e_b`. -/
def diff2L (a b : ℕ) : List ℤ := (List.range 37).map fun k => (if k = a then 1 else 0) - (if k = b then 2 else 0)
/-- The row `-2 e_c`. -/
def neg2L (c : ℕ) : List ℤ := (List.range 37).map fun k => if k = c then -2 else 0
/-- The bottom virtual row `e_0 - e_2 + e_33`. -/
def virtBL : List ℤ := (List.range 37).map fun k =>
  (if k = 0 then 1 else 0) - (if k = 2 then 1 else 0) + (if k = 33 then 1 else 0)
/-- The top virtual row `e_30 + e_32`. -/
def virtTL : List ℤ := (List.range 37).map fun k => (if k = 30 then 1 else 0) + (if k = 32 then 1 else 0)

def hasRow (g : ℕ) (r : List ℤ) : Bool := (oRows g).contains r

set_option maxRecDepth 100000 in
theorem pt1_AE : ∀ k : Fin 11, hasRow 3 (unitL (3 * k)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_ZE : hasRow 3 (unitL 33) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_CF : ∀ k : Fin 11, hasRow 3 (unitL (3 * k + 1)) = true ∧ hasRow 4 (unitL (3 * k + 1)) = true ∧
    hasRow 5 (unitL (3 * k + 1)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem pt1_jet0 : hasRow 3 (unitL 34) = true ∧ hasRow 4 (unitL 34) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_C : ∀ k : Fin 11, hasRow 0 (diff2L (3 * k + 1) (3 * k + 2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem ptm1_Z : hasRow 0 (neg2L 33) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_AE : ∀ k : Fin 11, hasRow 6 (unitL (3 * k)) = true ∧ hasRow 7 (unitL (3 * k)) = true := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem inf_ZE : hasRow 6 (unitL 33) = true ∧ hasRow 7 (unitL 33) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_CE : ∀ k : Fin 11, hasRow 6 (unitL (3 * k + 2)) = true ∧ hasRow 7 (unitL (3 * k + 2)) = true ∧
    hasRow 8 (unitL (3 * k + 2)) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtB : hasRow 6 virtBL = true ∧ hasRow 7 virtBL = true ∧ hasRow 8 virtBL = true ∧
    hasRow 9 virtBL = true ∧ hasRow 10 virtBL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_virtT : hasRow 6 virtTL = true ∧ hasRow 7 virtTL = true ∧ hasRow 8 virtTL = true ∧
    hasRow 9 virtTL = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_low13 : hasRow 6 (unitL 35) = true ∧ hasRow 7 (unitL 35) = true ∧ hasRow 8 (unitL 35) = true ∧
    hasRow 9 (unitL 35) = true ∧ hasRow 10 (unitL 35) = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem inf_low1 : hasRow 6 (unitL 36) = true := by decide +kernel

end
end CatalanMeasure.GenD.Uniform.W.Charts6.L0135
