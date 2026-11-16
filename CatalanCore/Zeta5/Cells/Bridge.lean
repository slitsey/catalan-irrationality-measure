module

public import CatalanCore.Zeta5.Cells.ZD17
public import CatalanCore.Zeta5.Cells.ZD18
public import CatalanCore.Zeta5.Potential.All
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import CatalanCore.Zeta5.Decay.All
public import CatalanCore.Zeta5.Cells.Const

@[expose] public section

/-!
# Z5-CELLS, part 13: the bridge to the energy chain

`PointwiseCell c N b M0` is the pointwise cell hypothesis of Z5-ENERGY: `2 U_ν(t) − V(t) ≤ M₀`
for `t ∈ [0, 4]` (`U_ν = logPot (nu c N b)`, `V = Vfld`).  `cells_imply_pointwise` derives it from
`ZD17` (region A, `t = b cos²φ`, `φ ∈ [0, π/2]`) and `ZD18` (region B,
`t = (b/2)(1 + cosh x)`, `x ∈ [0, 3]`) together with `4 ≤ (b/2)(1 + cosh 3)` (`t(w_T) > 4`):
the change of variable is `φ = arccos √(t/b)` resp. `x = arcosh(2t/b − 1)`, and the closed forms
are Z5-POTENTIAL `logPot_nu_inside_cos`, `logPot_nu_cosh` and `Vfld_sq`.
`four_lt_t_three` is the numeric fact for `y_b = 43/50` (`e³ > 20.08`).
-/

namespace CatalanCore.Zeta5.Cells

open Set Real MeasureTheory CatalanCore.Zeta5.Potential

noncomputable section

/-- the pointwise cell hypothesis of the energy chain -/
def PointwiseCell (c : ℕ → ℝ) (N : ℕ) (b M0 : ℝ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 4, 2 * logPot (nu c N b) t - Vfld t ≤ M0

theorem four_lt_t_three : (4 : ℝ) < ((43 / 50 : ℝ) ^ 2 / 2) * (1 + Real.cosh 3) := by
  have h1 := Real.exp_one_gt_d9
  have h3 : (2.7182818283 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h4 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h5 : 0 < Real.exp (-3) := Real.exp_pos _
  have : Real.cosh 3 = (Real.exp 3 + Real.exp (-3)) / 2 := Real.cosh_eq 3
  rw [this]
  nlinarith

theorem cells_imply_pointwise {c : ℕ → ℝ} {N : ℕ} {yb M0 : ℝ} (hyb : 0 < yb)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hT : 4 ≤ (yb ^ 2 / 2) * (1 + Real.cosh 3))
    (hA : ZD17 (c 0) yb (3 / 40) (fun k => c (k + 1) / ((k + 1 : ℕ) : ℝ)) N M0)
    (hB : ZD18 (c 0) yb (3 / 40) (fun k => c (k + 1) / ((k + 1 : ℕ) : ℝ)) N M0) :
    PointwiseCell c N (yb ^ 2) M0 := by
  intro t ht
  have hb : 0 < yb ^ 2 := by positivity
  by_cases htb : t ≤ yb ^ 2
  · -- region A
    have hs : 0 ≤ t / yb ^ 2 := div_nonneg ht.1 hb.le
    have hs1 : √(t / yb ^ 2) ≤ 1 := Real.sqrt_le_one.mpr ((div_le_one hb).mpr htb)
    have hsn : 0 ≤ √(t / yb ^ 2) := Real.sqrt_nonneg _
    set φ := Real.arccos √(t / yb ^ 2) with hφdef
    have hcos : Real.cos φ = √(t / yb ^ 2) := Real.cos_arccos (by linarith) hs1
    have hφ : φ ∈ Icc (0 : ℝ) (π / 2) :=
      ⟨Real.arccos_nonneg _, Real.arccos_le_pi_div_two.mpr hsn⟩
    have ht' : t = yb ^ 2 * Real.cos φ ^ 2 := by
      rw [hcos, Real.sq_sqrt hs]; field_simp
    have hU := logPot_nu_inside_cos hb hpos φ
    rw [← ht'] at hU
    have hcn : 0 ≤ yb * Real.cos φ := by rw [hcos]; positivity
    have hV : Vfld t = Vy (3 / 40) (yb * Real.cos φ) := by
      rw [← Vfld_sq hcn, ht']; congr 1; ring
    have h := hA φ hφ
    unfold gA at h
    rw [hU, hV]
    have hsum : ∑ k ∈ Finset.range N, c (k + 1) * Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ) /
        ((k + 1 : ℕ) : ℝ) = ∑ k ∈ Finset.range N, c (k + 1) / ((k + 1 : ℕ) : ℝ) *
          Real.cos (2 * ((k + 1 : ℕ) : ℝ) * φ) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    linarith
  · -- region B
    have htb' := not_le.mp htb
    have hx1 : (1 : ℝ) < 2 * t / yb ^ 2 - 1 := by
      rw [lt_sub_iff_add_lt, lt_div_iff₀ hb]; linarith
    set x := Real.arcosh (2 * t / yb ^ 2 - 1) with hxdef
    have hcosh : Real.cosh x = 2 * t / yb ^ 2 - 1 := Real.cosh_arcosh hx1.le
    have hx0 : 0 < x := Real.arcosh_pos hx1
    have hx3 : x ≤ 3 := by
      have h4 : 2 * t / yb ^ 2 - 1 ≤ Real.cosh 3 := by
        have : 2 * t / yb ^ 2 ≤ 8 / yb ^ 2 := by
          rw [div_le_div_iff_of_pos_right hb]; linarith [ht.2]
        have h5 : 8 / yb ^ 2 - 1 ≤ Real.cosh 3 := by
          rw [div_sub_one hb.ne', div_le_iff₀ hb]; nlinarith
        linarith
      have := (Real.cosh_le_cosh (x := x) (y := 3)).mp (by rw [hcosh]; exact h4)
      rw [abs_of_pos hx0, abs_of_pos (by norm_num)] at this
      exact this
    have ht' : t = yb ^ 2 / 2 * (1 + Real.cosh x) := by
      rw [hcosh]; field_simp; ring
    have hU := logPot_nu_cosh hb hpos hx0
    rw [← ht'] at hU
    have hcn : 0 ≤ yb * Real.cosh (x / 2) := by positivity
    have hV : Vfld t = Vy (3 / 40) (yb * Real.cosh (x / 2)) := by
      rw [← Vfld_sq hcn]
      congr 1
      have h2 : Real.cosh x = 2 * Real.cosh (x / 2) ^ 2 - 1 := by
        have := Real.cosh_two_mul (x / 2)
        rw [show 2 * (x / 2) = x by ring, Real.cosh_sq] at this
        rw [this]; nlinarith [Real.cosh_sq (x / 2)]
      rw [ht', h2]; ring
    have h := hB x ⟨hx0.le, hx3⟩
    unfold gB at h
    rw [hU, hV]
    have hsum : ∑ k ∈ Finset.range N, c (k + 1) * Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) /
        ((k + 1 : ℕ) : ℝ) = ∑ k ∈ Finset.range N, c (k + 1) / ((k + 1 : ℕ) : ℝ) *
          Real.exp (-(((k + 1 : ℕ) : ℝ) * x)) :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    linarith

/-- **`hcell` of `Decay.zeta5_decay`, in exactly its form.**  Region A (`t ∈ [0, b]`) and region B
(`t ∈ [b, t(3)]`, `t(3) ≥ 4`) cover `[0, 4]`. -/
theorem hcell_of_cells {c : ℕ → ℝ} {N : ℕ} {yb M0 : ℝ} (hyb : 0 < yb)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x)
    (hT : 4 ≤ (yb ^ 2 / 2) * (1 + Real.cosh 3))
    (hA : ZD17 (c 0) yb (3 / 40) (fun k => c (k + 1) / ((k + 1 : ℕ) : ℝ)) N M0)
    (hB : ZD18 (c 0) yb (3 / 40) (fun k => c (k + 1) / ((k + 1 : ℕ) : ℝ)) N M0) :
    ∀ t ∈ Icc (0 : ℝ) 4, 2 * CatalanCore.Zeta5.Energy.potU (nu c N (yb ^ 2)) t -
      CatalanCore.Zeta5.Energy.Vfield t ≤ M0 :=
  fun t ht => cells_imply_pointwise hyb hpos hT hA hB t ht

/-- **`hconst` of `Decay.zeta5_decay`**: `ZD22` at `D0 = 138500086/10^8` gives
`D0 ≤ Dnu c N b M₀` (`Dnu_eq`, `c 0 = 37/40`, `b = yb²`, `E = Σ c_{k+1}²/(2(k+1))`). -/
theorem hconst_of_zd22 {c : ℕ → ℝ} {N : ℕ} {yb M0 : ℝ} (h0 : c 0 = 37 / 40)
    (hz : ZD22 (37 / 40) (3 / 40) yb
      (∑ k ∈ Finset.range N, c (k + 1) ^ 2 / (2 * ((k + 1 : ℕ) : ℝ))) M0 (138500086 / 10 ^ 8)) :
    (138500086 : ℝ) / 10 ^ 8 ≤ CatalanCore.Zeta5.Decay.Dnu c N (yb ^ 2) M0 := by
  rw [CatalanCore.Zeta5.Decay.Dnu_eq N _ _ h0]
  exact hz.le

end

end CatalanCore.Zeta5.Cells
