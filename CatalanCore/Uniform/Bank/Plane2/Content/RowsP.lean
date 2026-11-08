module

public import CatalanCore.Uniform.Bank.Plane2.Content.RowsE
public import CatalanCore.Uniform.Content.Sweep.Rows

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# Plane 2 content: the rows `P₄ .. P₇` as `Real` (lane H, wave P210-B; ledger P210, N2)

`Sweep.row_P4 .. row_P7` carry `u ≠ 0` (through `Tphi_le`, `Tphi_ge`).  The potential `φ` of `u = 0` is
pointwise at most that of `u = 1` (`half p 0 = 0`), so `Tphi p u n ≤ Tphi p 1 n` for every `u`
(`Tphi_mono`) and the four rows hold for all `(v, u)` with the same closed forms (`rowP4_all .. rowP7_all`).
They need neither `p ∤ v` nor the guard: only `2 (r + 2m) < p²` and `2m ≤ r`.
-/

namespace CatalanCore.Uniform.Bank.Plane2.Content

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm KExpr CatalanCore.Uniform.Content.BankShared.TwoTerm

/-- The potential of `u` is at most that of `u = 1` (the half map of `u = 0` is `0`). -/
theorem Tphi_mono (p : ℕ) (u : ℤ) (n : ℕ) : Tphi p u n ≤ Tphi p 1 n := by
  unfold Tphi
  refine sum_le_sum fun t _ => ?_
  by_cases hu : u = 0
  · subst hu
    unfold phi half
    split_ifs <;> omega
  · have : half p u t = half p 1 t := by unfold half; simp [hu]
    unfold phi
    rw [this]

section AllU

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {ι : Type} [Fintype ι] [DecidableEq ι] (cn : ι → ℕ)
  (hinj : Function.Injective cn) {r m : ℕ} (hcr : ∀ a, cn a < r)
  (hN : 2 * (r + 2 * m) < p * p) (hm : 2 * m ≤ r) (hp5 : 5 ≤ p)

include hinj hcr hN hp5 in
theorem rowP4_all (hpr : p ≤ r) : GLE p (6 * r + 6 * m - 5 * p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := p2_odd (p := p) hp5
  have h1 := Tphi_mono p u r
  have h2 := Tphi_mono p u (r + 2 * m)
  rw [Tphi_ge p 1 one_ne_zero ho hpr] at h1
  rw [Tphi_ge p 1 one_ne_zero ho (by omega)] at h2
  omega

include hinj hcr hN hp5 hm in
theorem rowP5_all (hrp : r ≤ p) (hpN : p ≤ r + 2 * m) :
    GLE p (r + 3 * (r + 2 * m) - 3 * p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := p2_odd (p := p) hp5
  have h1 := Tphi_mono p u r
  have h2 := Tphi_mono p u (r + 2 * m)
  rw [Tphi_le p 1 one_ne_zero ho hrp] at h1
  rw [Tphi_ge p 1 one_ne_zero ho hpN] at h2
  omega

include hinj hcr hN hp5 in
theorem rowP6_all (hNp : r + 2 * m ≤ p) (hp2 : p ≤ 2 * r) :
    GLE p (2 * r + 2 * m + 1 - p) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := p2_odd (p := p) hp5
  have h1 := Tphi_mono p u r
  have h2 := Tphi_mono p u (r + 2 * m)
  rw [Tphi_le p 1 one_ne_zero ho (by omega)] at h1
  rw [Tphi_le p 1 one_ne_zero ho hNp] at h2
  omega

include hinj hcr hN hp5 hm in
theorem rowP7_all (hp2 : 2 * r ≤ p) : GLE p (r + 2 * m - (p - 1) / 2) (rowDet v u cn r m) := by
  refine (det_gle_phi v u cn hinj hcr hN).mono ?_
  have ho := p2_odd (p := p) hp5
  have h1 := Tphi_mono p u r
  have h2 := Tphi_mono p u (r + 2 * m)
  rw [Tphi_le p 1 one_ne_zero ho (by omega)] at h1
  by_cases hNp : r + 2 * m ≤ p
  · rw [Tphi_le p 1 one_ne_zero ho hNp] at h2
    omega
  · rw [Tphi_ge p 1 one_ne_zero ho (by omega)] at h2
    omega

end AllU

/-! ### `Real` -/

/-- The common set-up of the four rows: the member as the determinant and the conditions. -/
theorem p2_rowP_setup (v u : ℤ) (r p : ℕ) [Fact p.Prime] (S : Finset (p2G.geometry r).C) (hr : r % 2 = 0)
    (n : ℕ) (h : GLE p n (rowDet v u (fun a : S => ((a.1 : (p2G.geometry r).C) : ℕ)) r (p2G.borderSize r))) :
    GLE p n (p2Q v u r S) := by
  rw [p2Q_eq_m v u r hr S (p2_k_eq r)]
  exact h

theorem real_P4 (v u : ℤ) : Real v u brP4 := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hc1 := holds_ns (hcond ⟨1, -1, 0, [], 0, false⟩ (by simp [brP4]))
  refine ⟨6 * r + 6 * p2G.borderSize r - 5 * p, ?_, ?_⟩
  · exact p2_rowP_setup v u r p S hr _ (rowP4_all v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hp5
      (by simp at hc1; omega))
  · simp only [brP4, KExpr.evalN]
    omega

theorem real_P5 (v u : ℤ) : Real v u brP5 := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hm := p2_two_m_le hr hr0
  have hc1 := holds_ns (hcond ⟨-1, 1, 0, [], 0, false⟩ (by simp [brP5]))
  have hc2 := holds_ns (hcond ⟨1, -1, 2, [], 0, false⟩ (by simp [brP5]))
  refine ⟨r + 3 * (r + 2 * p2G.borderSize r) - 3 * p, ?_, ?_⟩
  · exact p2_rowP_setup v u r p S hr _ (rowP5_all v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hm hp5
      (by simp at hc1; omega) (by simp at hc2; omega))
  · simp only [brP5, Nx, KExpr.evalN]
    omega

theorem real_P6 (v u : ℤ) : Real v u brP6 := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hm := p2_two_m_le hr hr0
  have hc1 := holds_ns (hcond ⟨-1, 1, -2, [], 0, false⟩ (by simp [brP6]))
  have hc2 := holds_ns (hcond ⟨2, -1, 0, [], 0, false⟩ (by simp [brP6]))
  refine ⟨2 * r + 2 * p2G.borderSize r + 1 - p, ?_, ?_⟩
  · exact p2_rowP_setup v u r p S hr _ (rowP6_all v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hp5
      (by simp at hc1; omega) (by simp at hc2; omega))
  · simp only [brP6, KExpr.evalN]
    omega

theorem real_P7 (v u : ℤ) : Real v u brP7 := by
  intro r p _ S kv hr hr0 hPb hN0 hN hk hcond
  have hp5 := p2_hp5 hPb
  have hm := p2_two_m_le hr hr0
  have hc1 := holds_ns (hcond ⟨-2, 1, 0, [], 0, false⟩ (by simp [brP7]))
  refine ⟨r + 2 * p2G.borderSize r - (p - 1) / 2, ?_, ?_⟩
  · exact p2_rowP_setup v u r p S hr _ (rowP7_all v u _ (p2Q_inj r S) (p2Q_lt r hr S) hN hm hp5
      (by simp at hc1; omega))
  · simp only [brP7, Nx, CatalanCore.Uniform.Bank.Plane2.Content.hk, KExpr.evalN]
    omega

end CatalanCore.Uniform.Bank.Plane2.Content

#print axioms CatalanCore.Uniform.Bank.Plane2.Content.Tphi_mono
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_P4
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_P5
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_P6
#print axioms CatalanCore.Uniform.Bank.Plane2.Content.real_P7
