module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3K
public import CatalanCore.Arith.Hybrid.RankWit

@[expose] public section

/-!
# Lemma E, class 3: the rank bound and `gleAt_E3`

For `p ≡ 3 (4)`, `p ∤ 6255` (that is `p ≠ 139` for primes `≥ 7`) and the setting `ESetup3`,
`rank BE3 ≤ r`, hence (rank principle, corank `m`)

  `GLE p (∑u + ∑v - m) (fullPoly)`,   `∑u + ∑v = 2 r + m`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m k1 : ℕ}

variable (S : ESetup3 p r m k1)

include S

lemma card_Pt_Wt : Fintype.card (Pt3 p r m) + Fintype.card (Wt3 p r m) = r := by
  have := Fintype.card_congr (Equiv.sumCompl (fun c : Fin r => isCz p r m (c : ℕ)))
  rw [Fintype.card_sum, Fintype.card_fin] at this
  change Fintype.card (Wt3 p r m) + Fintype.card (Pt3 p r m) = r at this
  omega

lemma card_Wt : Fintype.card (Wt3 p r m) = m := by
  have hN := S.hN; have hpr := S.hpr
  have hb : Function.Bijective (fun x : Fin m => ww S x) := by
    constructor
    · intro x x' h
      have := congrArg (fun t : Wt3 p r m => (t.1 : ℕ)) h
      simp only [ww_val] at this
      apply Fin.ext
      have := x.2; have := x'.2
      omega
    · intro w
      have hw := w.2
      have hw1 := w.1.2
      unfold isCz at hw
      refine ⟨⟨(w.1.val - (r - p)) / 2, by omega⟩, ?_⟩
      apply Subtype.ext; apply Fin.ext
      rw [ww_val]
      simp only
      omega
  have := Fintype.card_of_bijective hb
  simpa using this.symm

lemma rank_BE3_le (h6255 : ¬ p ∣ 6255) : (BE3 p r m (sd3 S)).rank ≤ r := by
  have hp5 := S.p5
  have hp3 := S.hp3
  have hN := S.hN; have hpr := S.hpr; have hk2r := S.hk2r; have hk1 := S.hk1
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h5 : (5 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have h6255' : (6255 : ZMod p) ≠ 0 := by
    intro h
    apply h6255
    have h' : ((6255 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h'
  letI := M0_invertible S h3 h5 h6255'
  have hD1 : (Matrix.of fun w w' : Wt3 p r m =>
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w'))) = 1 := by
    ext w w'
    simp only [Matrix.of_apply, Mat3_ww]
    rw [TE3_WW S w.1.2 w.2 w'.1.2 w'.2]
    by_cases h : w' = w
    · subst h; simp [rfC_one]
    · have h1 : (w'.1 : ℕ) ≠ w.1 := fun hh => h (Subtype.ext (Fin.ext hh))
      rw [if_neg h1, Matrix.one_apply, if_neg (Ne.symm h), rfC_zero]
  letI : Invertible (Matrix.of fun w w' : Wt3 p r m =>
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inr w)) (Sum.inl (Sum.inr w'))) :=
    invertibleOfRightInverse _ 1 (by rw [hD1]; simp)
  have hA12 : ∀ (c : Pt3 p r m) (w : Wt3 p r m),
      Mat3 p r m (sd3 S) (Sum.inl (Sum.inl c)) (Sum.inl (Sum.inr w)) = 0 := by
    intro c w
    rw [Mat3_pw, TE3_PW S c.1.2 c.2 w.1.2 w.2, rfC_zero]
  have hD : ∀ x y : Fin m, Mat3 p r m (sd3 S) (Sum.inr x) (Sum.inr y) = 0 := by
    intro x y
    have hx := x.2; have hy := y.2
    rw [Mat3_xy, TE3_ZZ S (show r ≤ r + 2 * (x : ℕ) by omega)
      (show r ≤ r + 2 * (y : ℕ) + 1 by omega) (by omega) (by omega) (by omega), rfC_zero]
  have := rank_E3_abs (Mat3 p r m (sd3 S)) hA12 hD (V1 S) V2 (h1_sys S) (h2_sys S) (h3_sys S)
  have hr : (Mat3 p r m (sd3 S)).rank = (BE3 p r m (sd3 S)).rank :=
    Matrix.rank_submatrix _ _ _
  have hc := card_Pt_Wt S
  omega

/-- **Lemma E at a class-3 prime, dual form.** -/
theorem gleAt_E3_wit (hL : LamData Fr) (h6255 : ¬ p ∣ 6255) :
    HasRankWit Fr p r m (fun a => wr p r m (Frame.hybRow r m a))
      (fun b => wc p r m (Frame.hybCol r m b)) m := by
  have hrank := rank_BE3_le S h6255
  refine ⟨BE3 p r m (sd3 S), fun a b => hred_E3 hL S a b, ?_⟩
  omega

/-- **Lemma E at a class-3 prime, dual form.** -/
theorem gleAt_E3 (hL : LamData Fr) (h6255 : ¬ p ∣ 6255) :
    GLE p (∑ a, wr p r m (Frame.hybRow r m a) + ∑ b, wc p r m (Frame.hybCol r m b) - m)
      (Fr.fullPoly r m) :=
  (gleAt_E3_wit S hL h6255).gle

end

end CatalanCore.Arith.Hybrid
