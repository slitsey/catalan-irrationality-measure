module

public import CatalanCore.Uniform.Content.UFFamily2.SevHCell
public import CatalanCore.Uniform.Content.UFFamily.SevELayer

@[expose] public section

/-!
# UF family H (non-empty fibers): explicit price and debit layer (lane H, H11)

`cellH_bound`: the Smith price bound of `cellH` is the explicit number `baseH r p`
(`m = r/12`, `σ = (k₁ - r) - m`, `u = (k₁ - p) + (m - (k₁-r)/2) + (m - (k₁-r+1)/2)`):

  `baseH r p = 2 (r + m) - (m + σ + (σ - (p - u)))`.

`layerH` is the `DebitLayer` of the family (`ufLayerW`).  Pilot of a family with non-empty fibers,
end to end.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFFamily2.SevH

variable {Fr : Frame}

/-- Explicit price of the family. -/
def baseH (r p : ℕ) : ℕ :=
  2 * (r + r / 12) - (r / 12 + ((k1 p - r) - r / 12) +
    (((k1 p - r) - r / 12) - (p - ((k1 p - 1 + 1 - p) + (r / 12 - (k1 p - r) / 2) +
      (r / 12 - (k1 p - r + 1) / 2)))))

theorem cellH_bound (T : TwoTermData Fr 7 5) {r p : ℕ} [Fact p.Prime] (h : Valid' Fr r p) :
    (cellH T h).toF.bound = baseH r p := by
  have hv := h.v
  have hr12 := hv.hr12
  have hlo := hv.hlo
  have hk1 := hv.k1_lo
  have hk2 := hv.k1_hi
  have hr2 : r % 2 = 0 := by omega
  have hs := altGeom_hybShape cE cE_pos hr2
  have hkm : k1 p ≤ r + 2 * (r / 12) := by omega
  have hbs := borderSize_H hv
  have hk : ((altGeom cE cE_pos).geometry r).k = r / 12 := by
    show ((altGeom cE cE_pos).geometry r).X'.card = _
    rw [altGeom_X cE cE_pos hr2, Finset.card_image_of_injective _ (fun a b hab => by simp at hab; omega),
      Finset.card_range, hbs]
  have hC : Fintype.card ((altGeom cE cE_pos).geometry r).C = r := by
    rw [Fintype.card_coe, hs.C_eq, Finset.card_range]
  have hRows : (winRows (r := r) cE cE_pos r (k1 p - 1)).card = (k1 p - r + 1) / 2 := by
    unfold winRows
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      2 * (i : ℕ) < k1 p - r) (fun i _ => by rw [hs.xs_eq]; exact win_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k1 p - r), card_lt, hk, (cnt_arith hk1 hkm).1]
  have hCols : (winCols (r := r) cE cE_pos r (k1 p - 1)).card = (k1 p - r) / 2 := by
    unfold winCols
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      2 * (i : ℕ) < k1 p - r - 1) (fun i _ => by rw [hs.ys_eq]; exact wincol_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k1 p - r - 1), card_lt, hk, (cnt_arith hk1 hkm).2]
  have hTR : (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
      k1 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card = r / 12 - (k1 p - r + 1) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      ¬ 2 * (i : ℕ) < k1 p - r) (fun i _ => by rw [hs.xs_eq]; exact ge_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k1 p - r), card_ge, hk, (cnt_arith hk1 hkm).1]
  have hTC : (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
      k1 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card = r / 12 - (k1 p - r) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      ¬ 2 * (i : ℕ) < k1 p - r - 1) (fun i _ => by rw [hs.ys_eq]; exact gec_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k1 p - r - 1), card_ge, hk, (cnt_arith hk1 hkm).2]
  unfold UFCellF.bound UFCellF.sigma
  have e1 : (cellH T h).toF.t0 = r := rfl
  have e2 : (cellH T h).toF.tmax = k1 p - 1 := rfl
  have e3 : (cellH T h).toF.u = (k1 p - 1 + 1 - p) +
      (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
        k1 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card +
      (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
        k1 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card := rfl
  rw [e1, e2, e3, hRows, hCols, hTC, hTR, hk, Fintype.card_sum, hC, Fintype.card_fin, baseH]
  clear hRows hCols hTR hTC hs hbs hk hC e1 e2 e3 h hv
  omega

/-- Validity of the layer. -/
def validH (Fr : Frame) (r p : ℕ) : Prop :=
  Valid r p ∧ Fr.norm = 1 ∧ ∀ [Fact p.Prime], Fr.norm ∈ S p ∧ red p Fr.norm ≠ 0

/-- **The UF debit layer of the non-empty-fiber family H**. -/
noncomputable def layerH (T : TwoTermData Fr 7 5) {depth : ℕ} :
    DebitLayer (altGeom cE cE_pos) Fr depth :=
  ufLayerW (T := T) (validH Fr) baseH
    (fun r p _ h => cellH T ⟨h.1, h.2.2.1, h.2.2.2, h.2.1⟩)
    (fun r p _ h => (cellH_bound T ⟨h.1, h.2.2.1, h.2.2.2, h.2.1⟩).le)

theorem layerH_base (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerH (depth := depth) T).base = baseH := rfl

theorem layerH_debit (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerH (depth := depth) T).debit = 1 := rfl

theorem layerH_valid (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerH (depth := depth) T).valid = validH Fr := rfl

theorem layerH_eff (T : TwoTermData Fr 7 5) {depth : ℕ} (r p : ℕ) :
    (layerH (depth := depth) T).eff r p = baseH r p + depth := by
  simp [DebitLayer.eff, layerH_base, layerH_debit]

end CatalanCore.Uniform.Content.UFFamily2.SevH
