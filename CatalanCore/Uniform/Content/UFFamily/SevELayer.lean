module

public import CatalanCore.Uniform.Content.UFFamily.SevECell
public import CatalanCore.Uniform.Content.Wire.Shape

@[expose] public section

/-!
# UF families, sevenths `a = 2`, `p ≡ 5 (mod 7)`: explicit price and debit layer (lane H10)

`cellE_bound`: the Smith price bound of `cellE` is the explicit number

  `baseE r p = 2 (r + m) - (m + σ + (σ - (p - 14 m)))`,   `m = r/12`,  `σ = (k₀ - r) - m`,  `k₀ = (6p+5)/7`

(window `[r, k₀ - 1]` contains `k₀ - r` border nodes, the killed nodes `≥ k₀` complete `u = 14 m`).
`layerE` is the `DebitLayer` of the family (`ufLayerW`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire

namespace CatalanCore.Uniform.Content.UFFamily.SevE

theorem card_fin_filter (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i : Fin k => P i).card = ((Finset.range k).filter P).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext n
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i.2, hi⟩
  · rintro ⟨hn, hP⟩; exact ⟨⟨n, hn⟩, hP, rfl⟩

theorem card_lt (k a : ℕ) :
    ((Finset.range k).filter fun i => 2 * i < a).card = min k ((a + 1) / 2) := by
  have : (Finset.range k).filter (fun i => 2 * i < a) = Finset.range (min k ((a + 1) / 2)) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.card_range]

theorem card_ge (k a : ℕ) :
    ((Finset.range k).filter fun i => ¬ 2 * i < a).card = k - min k ((a + 1) / 2) := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.range k) (fun i => 2 * i < a)
  rw [card_lt, Finset.card_range] at h
  omega

theorem win_iff {r k0 : ℕ} (i : ℕ) (h : r + 2 ≤ k0) :
    (r ≤ r + 2 * i ∧ r + 2 * i ≤ k0 - 1) ↔ 2 * i < k0 - r := by omega

theorem wincol_iff {r k0 : ℕ} (i : ℕ) (h : r + 2 ≤ k0) :
    (r ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ k0 - 1) ↔ 2 * i < k0 - r - 1 := by omega

theorem ge_iff {r k0 : ℕ} (i : ℕ) : k0 ≤ r + 2 * i ↔ ¬ 2 * i < k0 - r := by omega

theorem gec_iff {r k0 : ℕ} (i : ℕ) : k0 ≤ r + 2 * i + 1 ↔ ¬ 2 * i < k0 - r - 1 := by omega

theorem cnt_arith {r k0 m : ℕ} (h1 : r + 2 ≤ k0) (h2 : k0 ≤ r + 2 * m) :
    min m ((k0 - r + 1) / 2) = (k0 - r + 1) / 2 ∧ min m ((k0 - r - 1 + 1) / 2) = (k0 - r) / 2 := by
  refine ⟨min_eq_right (by omega), ?_⟩
  rw [Nat.sub_add_cancel (by omega : 1 ≤ k0 - r)]
  exact min_eq_right (by omega)

variable {Fr : Frame}

/-- Explicit price of the family. -/
def baseE (r p : ℕ) : ℕ :=
  2 * (r + r / 12) - (r / 12 + ((k0 p - r) - r / 12) +
    (((k0 p - r) - r / 12) - (p - 14 * (r / 12))))

theorem cellE_bound (T : TwoTermData Fr 7 5) {r p : ℕ} [Fact p.Prime] (h : Valid' Fr r p) :
    (cellE T h).toF.bound = baseE r p := by
  have hv := h.v
  have hr12 := hv.hr12
  have hlo := hv.hlo
  have hk1 := hv.k0_lo
  have hk2 := hv.k0_hi
  have hr2 : r % 2 = 0 := by omega
  have hs := altGeom_hybShape cE cE_pos hr2
  have hkm : k0 p ≤ r + 2 * (r / 12) := by omega
  have hbs := borderSize_E hv
  have hk : ((altGeom cE cE_pos).geometry r).k = r / 12 := by
    show ((altGeom cE cE_pos).geometry r).X'.card = _
    rw [altGeom_X cE cE_pos hr2, Finset.card_image_of_injective _ (fun a b hab => by simp at hab; omega),
      Finset.card_range, hbs]
  have hC : Fintype.card ((altGeom cE cE_pos).geometry r).C = r := by
    rw [Fintype.card_coe, hs.C_eq, Finset.card_range]
  have hRows : (winRows (r := r) cE cE_pos r (k0 p - 1)).card = (k0 p - r + 1) / 2 := by
    unfold winRows
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      2 * (i : ℕ) < k0 p - r) (fun i _ => by rw [hs.xs_eq]; exact win_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k0 p - r), card_lt, hk, (cnt_arith hk1 hkm).1]
  have hCols : (winCols (r := r) cE cE_pos r (k0 p - 1)).card = (k0 p - r) / 2 := by
    unfold winCols
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      2 * (i : ℕ) < k0 p - r - 1) (fun i _ => by rw [hs.ys_eq]; exact wincol_iff i hk1),
      card_fin_filter _ (fun n => 2 * n < k0 p - r - 1), card_lt, hk, (cnt_arith hk1 hkm).2]
  have hTR : (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
      k0 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card = r / 12 - (k0 p - r + 1) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      ¬ 2 * (i : ℕ) < k0 p - r) (fun i _ => by rw [hs.xs_eq]; exact ge_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k0 p - r), card_ge, hk, (cnt_arith hk1 hkm).1]
  have hTC : (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
      k0 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card = r / 12 - (k0 p - r) / 2 := by
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom cE cE_pos).geometry r).k =>
      ¬ 2 * (i : ℕ) < k0 p - r - 1) (fun i _ => by rw [hs.ys_eq]; exact gec_iff i),
      card_fin_filter _ (fun n => ¬ 2 * n < k0 p - r - 1), card_ge, hk, (cnt_arith hk1 hkm).2]
  unfold UFCellF.bound UFCellF.sigma
  have e1 : (cellE T h).toF.t0 = r := rfl
  have e2 : (cellE T h).toF.tmax = k0 p - 1 := rfl
  have e3 : (cellE T h).toF.u = k0 p +
      (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
        k0 p ≤ ((altGeom cE cE_pos).geometry r).ys j).card +
      (Finset.univ.filter fun j : Fin ((altGeom cE cE_pos).geometry r).k =>
        k0 p ≤ ((altGeom cE cE_pos).geometry r).xs j).card := rfl
  rw [e1, e2, e3, hRows, hCols, hTC, hTR, hk, Fintype.card_sum, hC, Fintype.card_fin, baseE]
  clear hRows hCols hTR hTC hs hbs hk hC e1 e2 e3 h hv
  omega

/-- Validity of the layer. -/
def validE (Fr : Frame) (r p : ℕ) : Prop :=
  Valid r p ∧ ∀ [Fact p.Prime], Fr.norm ∈ S p ∧ red p Fr.norm ≠ 0

/-- **The UF debit layer of the sevenths family** `a = 2`, `p ≡ 5 (mod 7)`. -/
noncomputable def layerE (T : TwoTermData Fr 7 5) {depth : ℕ} :
    DebitLayer (altGeom cE cE_pos) Fr depth :=
  ufLayerW (T := T) (validE Fr) baseE
    (fun r p _ h => cellE T ⟨h.1, h.2.1, h.2.2⟩)
    (fun r p _ h => (cellE_bound T ⟨h.1, h.2.1, h.2.2⟩).le)

theorem layerE_base (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerE (depth := depth) T).base = baseE := rfl

theorem layerE_debit (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerE (depth := depth) T).debit = 1 := rfl

theorem layerE_valid (T : TwoTermData Fr 7 5) {depth : ℕ} :
    (layerE (depth := depth) T).valid = validE Fr := rfl

theorem layerE_eff (T : TwoTermData Fr 7 5) {depth : ℕ} (r p : ℕ) :
    (layerE (depth := depth) T).eff r p = baseE r p + depth := by
  simp [DebitLayer.eff, layerE_base, layerE_debit]

end CatalanCore.Uniform.Content.UFFamily.SevE
