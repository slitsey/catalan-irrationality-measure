module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3C
public import CatalanCore.Arith.Hybrid.LemmaE.LabelE2

@[expose] public section

/-!
# Lemma E, class 3: block structure of the reduction

`Pt = C \ Cz` (weights `1`, `1`), `Wt = Cz` (weights `0`, `2`).  Evaluation of `TEw3` on `Pt × Pt`
(pairs and diagonal), `Pt × Wt`, `Wt × Wt`, and the borders.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

abbrev Wt3 (p r m : ℕ) := {c : Fin r // isCz p r m (c : ℕ)}
abbrev Pt3 (p r m : ℕ) := {c : Fin r // ¬ isCz p r m (c : ℕ)}

/-- Reindexing `Fin r ⊕ Fin m ≃ (Pt ⊕ Wt) ⊕ Fin m`. -/
def e3 (p r m : ℕ) : Fin r ⊕ Fin m ≃ (Pt3 p r m ⊕ Wt3 p r m) ⊕ Fin m :=
  (((Equiv.sumCompl (fun c : Fin r => isCz p r m (c : ℕ))).symm.trans
    (Equiv.sumComm _ _)).sumCongr (Equiv.refl (Fin m)))

lemma e3_symm_ll (c : Pt3 p r m) : (e3 p r m).symm (Sum.inl (Sum.inl c)) = Sum.inl c.1 := by
  rw [Equiv.symm_apply_eq]
  have h1 : (Equiv.sumCompl (fun c : Fin r => isCz p r m (c : ℕ))).symm c.1 = Sum.inr c :=
    @Equiv.sumCompl_symm_apply_of_neg _ (fun c : Fin r => isCz p r m (c : ℕ)) _ c.1 c.2
  simp [e3, h1]

lemma e3_symm_lr (w : Wt3 p r m) : (e3 p r m).symm (Sum.inl (Sum.inr w)) = Sum.inl w.1 := by
  rw [Equiv.symm_apply_eq]
  have h1 : (Equiv.sumCompl (fun c : Fin r => isCz p r m (c : ℕ))).symm w.1 = Sum.inl w :=
    @Equiv.sumCompl_symm_apply_of_pos _ (fun c : Fin r => isCz p r m (c : ℕ)) _ w.1 w.2
  simp [e3, h1]

lemma e3_symm_r (y : Fin m) : (e3 p r m).symm (Sum.inr y) = Sum.inr y := by
  rw [Equiv.symm_apply_eq]; simp [e3]

/-- The reduction matrix in block form. -/
noncomputable def Mat3 (p r m : ℕ) [Fact p.Prime] (D : SingData p (r + 2 * m) k1) :
    Matrix ((Pt3 p r m ⊕ Wt3 p r m) ⊕ Fin m) ((Pt3 p r m ⊕ Wt3 p r m) ⊕ Fin m)
      (RatFunc (ZMod p)) :=
  (BE3 p r m D).submatrix (e3 p r m).symm (e3 p r m).symm

variable (D : SingData p (r + 2 * m) k1)

lemma Mat3_pp (c c' : Pt3 p r m) : Mat3 p r m D (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inl c')) =
    rfC p (TEw3 p r m D c.1 c'.1) := by
  simp [Mat3, e3_symm_ll, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_pw (c : Pt3 p r m) (w : Wt3 p r m) :
    Mat3 p r m D (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inr w)) = rfC p (TEw3 p r m D c.1 w.1) := by
  simp [Mat3, e3_symm_ll, e3_symm_lr, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_wp (w : Wt3 p r m) (c : Pt3 p r m) :
    Mat3 p r m D (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inl c)) = rfC p (TEw3 p r m D w.1 c.1) := by
  simp [Mat3, e3_symm_ll, e3_symm_lr, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_ww (w w' : Wt3 p r m) :
    Mat3 p r m D (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w')) = rfC p (TEw3 p r m D w.1 w'.1) := by
  simp [Mat3, e3_symm_lr, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_py (c : Pt3 p r m) (y : Fin m) :
    Mat3 p r m D (Sum.inl (Sum.inl c)) (Sum.inr y) =
      rfC p (TEw3 p r m D c.1 (r + 2 * (y : ℕ) + 1)) := by
  simp [Mat3, e3_symm_ll, e3_symm_r, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_wy (w : Wt3 p r m) (y : Fin m) :
    Mat3 p r m D (Sum.inl (Sum.inr w)) (Sum.inr y) =
      rfC p (TEw3 p r m D w.1 (r + 2 * (y : ℕ) + 1)) := by
  simp [Mat3, e3_symm_lr, e3_symm_r, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_xp (x : Fin m) (c : Pt3 p r m) :
    Mat3 p r m D (Sum.inr x) (Sum.inl (Sum.inl c)) =
      rfC p (TEw3 p r m D (r + 2 * (x : ℕ)) c.1) := by
  simp [Mat3, e3_symm_ll, e3_symm_r, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_xw (x : Fin m) (w : Wt3 p r m) :
    Mat3 p r m D (Sum.inr x) (Sum.inl (Sum.inr w)) =
      rfC p (TEw3 p r m D (r + 2 * (x : ℕ)) w.1) := by
  simp [Mat3, e3_symm_lr, e3_symm_r, BE3, Frame.hybRow, Frame.hybCol]

lemma Mat3_xy (x y : Fin m) :
    Mat3 p r m D (Sum.inr x) (Sum.inr y) =
      rfC p (TEw3 p r m D (r + 2 * (x : ℕ)) (r + 2 * (y : ℕ) + 1)) := by
  simp [Mat3, e3_symm_r, BE3, Frame.hybRow, Frame.hybCol]

/-! ### Weights on the label classes -/

lemma wr_Pt (c : Pt3 p r m) : wr p r m (c.1 : ℕ) = 1 := by
  unfold wr; rw [if_pos c.1.2, if_neg c.2]

lemma wc_Pt (c : Pt3 p r m) : wc p r m (c.1 : ℕ) = 1 := by
  unfold wc; rw [if_pos c.1.2, if_neg c.2]

lemma wr_Wt (w : Wt3 p r m) : wr p r m (w.1 : ℕ) = 0 := by
  unfold wr; rw [if_pos w.1.2, if_pos w.2]

lemma wc_Wt (w : Wt3 p r m) : wc p r m (w.1 : ℕ) = 2 := by
  unfold wc; rw [if_pos w.1.2, if_pos w.2]

lemma wr_zone {z : ℕ} (hz : r ≤ z) : wr p r m z = 0 := by
  unfold wr; rw [if_neg (by omega)]

lemma wc_zone {z : ℕ} (hz : r ≤ z) : wc p r m z = 1 := by
  unfold wc; rw [if_neg (by omega)]

end

end CatalanCore.Arith.Hybrid
