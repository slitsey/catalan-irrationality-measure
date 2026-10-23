module
public import CatalanCore.Arith.Hybrid.ShiftCell
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

open ChainClasses

namespace ChainModel
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

/-- `Q` does not depend on the zone nodes. -/
lemma Q_swap : Q Fr p r ys xs = Q Fr p r xs ys := by
  ext i j; rw [Q_apply, Q_apply]

lemma Q_symm : (Q Fr p r xs ys).transpose = Q Fr p r xs ys := by
  ext i j
  rw [Matrix.transpose_apply, Q_apply, Q_apply, Mn_symm (Fr := Fr) j.val i.val]
  simp [eq_comm]

lemma Nm_swap (i k : Fin r) : Nm Fr p r ys xs i k = Nm Fr p r xs ys i k := by
  rw [Nm_apply, Nm_apply, Q_swap]

lemma Nm_symm (i k : Fin r) : Nm Fr p r xs ys i k = Nm Fr p r xs ys k i := by
  rw [Nm_apply, Nm_apply]
  have := congrFun (congrFun (Matrix.adjugate_transpose (Q Fr p r xs ys)) i) k
  rw [Q_symm] at this
  simp only [Matrix.transpose_apply] at this
  rw [this]

lemma B_eq_C_swap (j : Fin r) (y : Z) :
    (full Fr p r xs ys).toBlocks₁₂ j y = (full Fr p r ys xs).toBlocks₂₁ y j := by
  rw [full_B_apply, full_C_apply, Mn_symm]

lemma aC_eq_aR_swap (y : Z) : aC Fr p r xs ys y = aR Fr p r ys xs y := by
  unfold aC aR colB rowB
  rw [Q_swap]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  rw [B_eq_C_swap, mul_comm]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  rw [Nm_swap, Nm_symm]

lemma bC_eq_bR_swap (y : Z) : bC Fr p r xs ys y = bR Fr p r ys xs y := by
  unfold bC bR colP rowP
  rw [Q_swap]
  congr 2
  apply Finset.sum_congr rfl; intro j _
  rw [B_eq_C_swap, mul_comm]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  rw [Nm_swap, Nm_symm, mul_comm]

end ChainModel


section Assemble
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

lemma gle0_C_nat (m : ℕ) : GLE p 0 (C (m:ℚ)) :=
  GLE.C_iff.2 (by simpa using natCast_mem (LocRing p) m)

lemma redI_C_nat (m : ℕ) : redI p (C (m:ℚ)) = rfC p (m : ZMod p) := by
  rw [redI_C (by simpa using natCast_mem (LocRing p) m)]
  have := (Good.natCast (ℓ := p) m).eq
  rw [this]

lemma rfC_ne_zero' {x : ZMod p} (h : x ≠ 0) : rfC p x ≠ 0 :=
  (map_ne_zero (rfCHom p)).2 h

variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)

include hL hp hN hr hx hy

/-- The leading identity after reduction: for every lift `g'` of `p T_zy`,
`det · 16 (y - z) · g' = α_z (pβ'_y) - (pβ_z) α'_y` in `𝔽_p(X)`. -/
theorem lead_identity_red (z y : Z) (g' : (LocRing p)[X])
    (hg' : toQ p g' = C (p:ℚ) * LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
      (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
      (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
      (ChainModel.Nm Fr p r xs ys) z y) :
    redI p (ChainModel.Q Fr p r xs ys).det * (rfC p 16 * (rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p)))
        * phiP p g' =
      redI p (ChainModel.aR Fr p r xs ys z) * redI p (ChainModel.bC Fr p r xs ys y) -
      redI p (ChainModel.bR Fr p r xs ys z) * redI p (ChainModel.aC Fr p r xs ys y) := by
  have H := congrArg (redI p) (ChainModel.T_lead_identity (Fr := Fr) (p := p) (r := r)
    (xs := xs) (ys := ys) z y)
  rw [← hg'] at H
  have hdet := ChainModel.gle0_det (xs := xs) (ys := ys) hL hp hN hr
  have hn : redI p (C Fr.norm) = rfC p 16 := by
    have := redI_C_nat (p := p) 16
    rw [hL.norm_eq]
    simpa using this
  have hCn : GLE p 0 (C Fr.norm) := by
    rw [hL.norm_eq]; simpa using gle0_C_nat (p := p) 16
  have hd : GLE p 0 (C (ys y : ℚ) - C (xs z : ℚ)) := by
    have := gle0_of_int1 ((int1_of_gle0 (gle0_C_nat (p := p) (ys y))).sub
      (int1_of_gle0 (gle0_C_nat (p := p) (xs z))))
    exact this
  have hd' : redI p (C (ys y : ℚ) - C (xs z : ℚ)) =
      rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p) := by
    rw [redI_sub (gle0_C_nat _) (gle0_C_nat _), redI_C_nat, redI_C_nat]
  have hlhs : redI p ((ChainModel.Q Fr p r xs ys).det * (C Fr.norm * (C (ys y : ℚ) - C (xs z : ℚ))) *
      toQ p g') = redI p (ChainModel.Q Fr p r xs ys).det *
      (rfC p 16 * (rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p))) * phiP p g' := by
    rw [redI_mul (gle0_mul hdet (gle0_mul hCn hd)) (gle0_toQ p g'), redI_toQ,
      redI_mul hdet (gle0_mul hCn hd), redI_mul hCn hd, hn, hd']
  have hA := ChainModel.int1_aR hL hp hN hr hx hy z
  have hB := ChainModel.int1_bC hL hp hN hr hx hy y
  have hA' := ChainModel.int1_aC hL hp hN hr hx hy y
  have hB' := ChainModel.int1_bR hL hp hN hr hx hy z
  rw [← hlhs, H, redI_sub (gle0_mul (gle0_of_int1 hA) (gle0_of_int1 hB))
    (gle0_mul (gle0_of_int1 hB') (gle0_of_int1 hA')),
    redI_mul (gle0_of_int1 hA) (gle0_of_int1 hB),
    redI_mul (gle0_of_int1 hB') (gle0_of_int1 hA')]

include hk in
/-- Column versions of the leading moments, from the row versions of the swapped model. -/
theorem redI_aC (y : Z) (hyy : r ≤ ys y) :
    redI p (ChainModel.aC Fr p r xs ys y) = redI p (ChainModel.Q Fr p r xs ys).det *
      sourceB Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) := by
  rw [ChainModel.aC_eq_aR_swap]
  have := redI_aR (xs := ys) (ys := xs) hL hp hN hr hk hy hx y hyy
  rw [this, ChainModel.Q_swap]

include hk in
theorem redI_bC (y : Z) (hyy : r ≤ ys y) :
    redI p (ChainModel.bC Fr p r xs ys y) = redI p (ChainModel.Q Fr p r xs ys).det *
      sourceA Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) := by
  rw [ChainModel.bC_eq_bR_swap]
  have := redI_bR (xs := ys) (ys := xs) hL hp hN hr hk hy hx y hyy
  rw [this, ChainModel.Q_swap]

omit hx hy in
theorem redI_det_ne_zero : redI p (ChainModel.Q Fr p r xs ys).det ≠ 0 :=
  redI_ne_zero_of_gn_eq_one (ChainModel.gle0_det hL hp hN hr)
    (Periodic.Model.Q_primitive (Periodic.lamPoleData hL hp (by omega)) (by omega) hr)


end Assemble

section Lead
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)
include hL hp hN hr hk hx hy

/-- **`lead_cross_cell`, rows.**  For a set `CR` of rows in one cut-free interval and a column `y`
whose node is not congruent to any of them, `p T_zy` reduces to `κ(y) / (y - z)` with `κ`
independent of `z ∈ CR`. -/
theorem lead_cross_cell_rows (CR : Finset Z) (hCR : ∀ z ∈ CR, r ≤ xs z)
    (hcell : ∀ z ∈ CR, ∀ z' ∈ CR, xs z ≤ xs z' →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs z : ℤ) (xs z' : ℤ))
    (hd : ∀ z ∈ CR, ∀ y, ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0) (y : Z) :
    ∃ k0 : RatFunc (ZMod p), ∀ z ∈ CR, ∀ g' : (LocRing p)[X],
      toQ p g' = C (p:ℚ) * LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
        (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
        (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
        (ChainModel.Nm Fr p r xs ys) z y →
      phiP p g' = k0 * rfC p ((((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))⁻¹) := by
  by_cases hne : CR.Nonempty
  · obtain ⟨SA, SB, hS⟩ := sourceAB_const (r := r) hL CR xs hne hcell
    have h16 : (rfC p 16 : RatFunc (ZMod p)) ≠ 0 := by
      apply rfC_ne_zero'
      have h4 := four_ne_zmod p hp
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    refine ⟨(SB * redI p (ChainModel.bC Fr p r xs ys y) -
        SA * redI p (ChainModel.aC Fr p r xs ys y)) / rfC p 16, fun z hz g' hg' => ?_⟩
    have H := lead_identity_red hL hp hN hr hx hy z y g' hg'
    rw [redI_aR hL hp hN hr hk hx hy z (hCR z hz), redI_bR hL hp hN hr hk hx hy z (hCR z hz),
      (hS z hz).1, (hS z hz).2] at H
    have hdet := redI_det_ne_zero hL hp hN hr (xs := xs) (ys := ys)
    set d : ZMod p := ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) with hdd
    have hd' : (rfC p d : RatFunc (ZMod p)) ≠ 0 := rfC_ne_zero' (hd z hz y)
    have hrfd : rfC p (d⁻¹) = (rfC p d)⁻¹ := map_inv₀ (rfCHom p) d
    have hsub : rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p) = rfC p d := by
      simp only [hdd, ← rfCHom_apply, map_sub]
    rw [hsub] at H
    rw [hrfd]
    field_simp
    field_simp at H
    linear_combination H
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, fun z hz => absurd hz (by simp [hne])⟩

/-- **`lead_cross_cell`, columns.** -/
theorem lead_cross_cell_cols (CC : Finset Z) (hCC : ∀ y ∈ CC, r ≤ ys y)
    (hcell : ∀ y ∈ CC, ∀ y' ∈ CC, ys y ≤ ys y' →
      NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (ys y : ℤ) (ys y' : ℤ))
    (hd : ∀ y ∈ CC, ∀ z, ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0) (z : Z) :
    ∃ k0 : RatFunc (ZMod p), ∀ y ∈ CC, ∀ g' : (LocRing p)[X],
      toQ p g' = C (p:ℚ) * LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
        (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
        (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
        (ChainModel.Nm Fr p r xs ys) z y →
      phiP p g' = k0 * rfC p ((((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))⁻¹) := by
  by_cases hne : CC.Nonempty
  · obtain ⟨SA, SB, hS⟩ := sourceAB_const (r := r) hL CC ys hne hcell
    have h16 : (rfC p 16 : RatFunc (ZMod p)) ≠ 0 := by
      apply rfC_ne_zero'
      have h4 := four_ne_zmod p hp
      have : (16 : ZMod p) = 4 * 4 := by norm_num
      rw [this]; exact mul_ne_zero h4 h4
    refine ⟨(redI p (ChainModel.aR Fr p r xs ys z) * SA -
        redI p (ChainModel.bR Fr p r xs ys z) * SB) / rfC p 16, fun y hy' g' hg' => ?_⟩
    have H := lead_identity_red hL hp hN hr hx hy z y g' hg'
    rw [redI_aC hL hp hN hr hk hx hy y (hCC y hy'), redI_bC hL hp hN hr hk hx hy y (hCC y hy'),
      (hS y hy').1, (hS y hy').2] at H
    have hdet := redI_det_ne_zero hL hp hN hr (xs := xs) (ys := ys)
    set d : ZMod p := ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) with hdd
    have hd' : (rfC p d : RatFunc (ZMod p)) ≠ 0 := rfC_ne_zero' (hd y hy' z)
    have hrfd : rfC p (d⁻¹) = (rfC p d)⁻¹ := map_inv₀ (rfCHom p) d
    have hsub : rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p) = rfC p d := by
      simp only [hdd, ← rfCHom_apply, map_sub]
    rw [hsub] at H
    rw [hrfd]
    field_simp
    field_simp at H
    linear_combination H
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨0, fun y hy' => absurd hy' (by simp [hne])⟩

end Lead


section Integral
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}
variable (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
  (hk : (4:ZMod p)*k=(o:ZMod p)) (hx : ∀ z, xs z<N) (hy : ∀ y, ys y<N)
include hL hp hN hr hk hx hy

/-- **Integrality of the same-cell block (first conjunct of `weighted_same_cell`).**  If the row
node and the column node lie in one cut-free interval, `p T_zy` is divisible by `p`: its leading
part `α_z (pβ'_y) - (pβ_z) α'_y` cancels because both nodes have the same source moments. -/
theorem T_integral_same_cell (z y : Z) (hxz : r ≤ xs z) (hyy : r ≤ ys y)
    (hnc₁ : xs z ≤ ys y → NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs z : ℤ) (ys y : ℤ))
    (hnc₂ : ys y ≤ xs z → NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (ys y : ℤ) (xs z : ℤ))
    (hd : ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0)
    (hint : GLE p 1 (LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
      (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
      (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
      (ChainModel.Nm Fr p r xs ys) z y)) :
    ∃ T' : (LocRing p)[X], toQ p T' = LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
      (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
      (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
      (ChainModel.Nm Fr p r xs ys) z y := by
  obtain ⟨g', hg'⟩ := exists_lift p hint
  rw [pow_one] at hg'
  have H := lead_identity_red hL hp hN hr hx hy z y g' hg'
  have hAB : sourceA Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) =
        sourceA Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) ∧
      sourceB Fr p o (fun j : ChainIndex p r (ys y) => (chainNode j).val) (ys y) =
        sourceB Fr p o (fun j : ChainIndex p r (xs z) => (chainNode j).val) (xs z) := by
    rcases le_total (xs z) (ys y) with h | h
    · exact sourceAB_chainTransport hL h (hnc₁ h)
    · have := sourceAB_chainTransport hL h (hnc₂ h)
      exact ⟨this.1.symm, this.2.symm⟩
  rw [redI_aR hL hp hN hr hk hx hy z hxz, redI_bR hL hp hN hr hk hx hy z hxz,
    redI_aC hL hp hN hr hk hx hy y hyy, redI_bC hL hp hN hr hk hx hy y hyy, hAB.1, hAB.2] at H
  have h16 : (rfC p 16 : RatFunc (ZMod p)) ≠ 0 := by
    apply rfC_ne_zero'
    have h4 := four_ne_zmod p hp
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have hdet := redI_det_ne_zero hL hp hN hr (xs := xs) (ys := ys)
  have hd' : (rfC p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) : RatFunc (ZMod p)) ≠ 0 :=
    rfC_ne_zero' hd
  have hsub : rfC p (ys y : ZMod p) - rfC p (xs z : ZMod p) =
      rfC p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) := by
    simp only [← rfCHom_apply, map_sub]
  rw [hsub] at H
  have h0 : phiP p g' = 0 := by
    have : redI p (ChainModel.Q Fr p r xs ys).det * (rfC p 16 *
        rfC p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))) * phiP p g' = 0 := by
      rw [H]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero hdet (mul_ne_zero h16 hd'))
    · exact h
  rw [phiP_eq_zero_iff] at h0
  obtain ⟨T'', hT''⟩ := h0
  refine ⟨T'', ?_⟩
  have hCp : toQ p (C ((p:ℕ) : LocRing p)) = C (p:ℚ) := by simp [toQ]
  have : C (p:ℚ) * toQ p T'' = C (p:ℚ) * LemmaE.Tscaled (ChainModel.Q Fr p r xs ys).det
      (ChainModel.full Fr p r xs ys).toBlocks₁₁ (ChainModel.full Fr p r xs ys).toBlocks₁₂
      (ChainModel.full Fr p r xs ys).toBlocks₂₁ (ChainModel.full Fr p r xs ys).toBlocks₂₂
      (ChainModel.Nm Fr p r xs ys) z y := by
    rw [← hg', hT'', map_mul, hCp]
  exact mul_left_cancel₀ (by
    rw [Ne, Polynomial.C_eq_zero]
    exact_mod_cast (Fact.out : p.Prime).ne_zero) this

end Integral

#print axioms T_integral_same_cell
end CatalanCore.Arith.Hybrid
