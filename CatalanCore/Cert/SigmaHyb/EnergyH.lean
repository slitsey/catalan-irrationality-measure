module

public import CatalanCore.Cert.SigmaHyb.IData

@[expose] public section

/-!
# `I_ρ(σ_h) ≤ Ibound` for the hybrid data

`I_ρ(wtH) = (64/81) (I(σ300) + 2 I(σ300, λ) + I(λ))`, `I(σ300) ≤ IBOUND` (legacy), the cross and
`λλ` terms from the scaled-integer lower log bounds (`logLoS`).
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

lemma totL (B : List Pt) : ∀ A : List Pt,
    (A.map (fun p => (B.map (Jr p)).sum)).sum = -(iTotL B A : ℝ) / 2 ^ 129 := by
  intro A
  induction A with
  | nil => simp [iTotL]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, row_eq]
    simp only [iTotL]
    push_cast
    ring

lemma iTotL_append (B a b : List Pt) : iTotL B (a ++ b) = iTotL B a + iTotL B b := by
  induction a with
  | nil => simp [iTotL]
  | cons p ps ih => simp only [List.cons_append, iTotL, ih]; ring

def X1 : ℤ := -136879835399926642005694082446259980794
def X2 : ℤ := -17262073741267614263064636889889374146

theorem X1_val : iTotL lamS sigmaS = X1 := by
  conv_lhs => rw [sigmaS_chunks']
  simp only [iTotL_append]
  rw [X1_0, X1_1, X1_2, X1_3, X1_4, X1_5, X1_6, X1_7, X1_8, X1_9]
  unfold X1; norm_num

theorem X2_val : iTotL lamS lamS = X2 := by
  nth_rewrite 2 [lamS_chunks]
  simp only [iTotL_append]
  rw [X2_0, X2_1, X2_2, X2_3, X2_4, X2_5]
  unfold X2; norm_num

lemma cS_eq (k : Fin 300) : cS k = cpt (ptAt k) := rfl
lemma cL_eq (l : Fin 180) : cL l = cpt (ptAtL lamS l) := rfl

theorem cross_le : ∑ k : Fin 300, ∑ l : Fin 180, mS k * mL l *
      CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS k) (cL l) ≤ -(X1 : ℝ) / 2 ^ 129 := by
  have h1 : ∑ k : Fin 300, ∑ l : Fin 180, mS k * mL l *
      CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS k) (cL l)
      ≤ ∑ k : Fin 300, ∑ l : Fin 180, Jr (ptAt k) (ptAtL lamS l) := by
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAt k) (ptAtL lamS l)
    unfold mS mL mOfL
    exact this
  have h2 : ∑ k : Fin 300, ∑ l : Fin 180, Jr (ptAt k) (ptAtL lamS l)
      = -(iTotL lamS sigmaS : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 300, ∑ l : Fin 180, Jr (ptAt k) (ptAtL lamS l) = (lamS.map (Jr (ptAt k))).sum :=
      fun k => sum_gen lamS 180 lamS_len (Jr (ptAt k))
    simp_rw [e1]
    rw [sum_sigma (fun p => (lamS.map (Jr p)).sum), totL]
  rw [X1_val] at h2
  exact h1.trans h2.le

theorem ll_le : CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL ≤ -(X2 : ℝ) / 2 ^ 129 := by
  have h1 : CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL ≤ ∑ k : Fin 180, ∑ l : Fin 180, Jr (ptAtL lamS k) (ptAtL lamS l) := by
    unfold CatalanLambda.Decay.Irho
    refine Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => ?_))
    have := pair_le (ptAtL lamS k) (ptAtL lamS l)
    unfold mL mOfL
    exact this
  have h2 : ∑ k : Fin 180, ∑ l : Fin 180, Jr (ptAtL lamS k) (ptAtL lamS l)
      = -(iTotL lamS lamS : ℝ) / 2 ^ 129 := by
    have e1 : ∀ k : Fin 180, ∑ l : Fin 180, Jr (ptAtL lamS k) (ptAtL lamS l) = (lamS.map (Jr (ptAtL lamS k))).sum :=
      fun k => sum_gen lamS 180 lamS_len (Jr (ptAtL lamS k))
    simp_rw [e1]
    rw [sum_gen lamS 180 lamS_len (fun p => (lamS.map (Jr p)).sum), totL]
  rw [X2_val] at h2
  exact h1.trans h2.le

lemma krho_symm (z w : ℂ) : CatalanLambda.Decay.krho (1 / 1024 : ℝ) z w = CatalanLambda.Decay.krho (1 / 1024 : ℝ) w z := by
  unfold CatalanLambda.Decay.krho
  rw [norm_sub_rev]

theorem Irho_hyb_expand :
    CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cH wtH
      = (64 / 81) * (CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cS mS
        + 2 * ∑ k : Fin 300, ∑ l : Fin 180, mS k * mL l * CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS k) (cL l)
        + CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL) := by
  unfold CatalanLambda.Decay.Irho wtH mH cH
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hsw : ∑ i : Fin 180, ∑ j : Fin 300, mL i * mS j * CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cL i) (cS j)
      = ∑ j : Fin 300, ∑ i : Fin 180, mS j * mL i * CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS j) (cL i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => ?_))
    rw [krho_symm]; ring
  have e : ∀ a b c : ℝ, a / (1 + 1 / 8) * (b / (1 + 1 / 8)) * c = (64 / 81) * (a * b * c) := by
    intros; ring
  simp_rw [e]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsw]
  ring

def IboundH : ℚ := 200560832 / 10 ^ 8

theorem I_ok_H : CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cH wtH ≤ (IboundH : ℝ) := by
  rw [Irho_hyb_expand]
  have h1 := CatalanLambda.Cert.I_ok
  have h2 := cross_le
  have h3 := ll_le
  have hX : (64 / 81 : ℝ) * ((IBOUND : ℝ) + 2 * (-(X1 : ℝ) / 2 ^ 129) + (-(X2 : ℝ) / 2 ^ 129)) ≤ (IboundH : ℝ) := by
    unfold IBOUND X1 X2 IboundH
    push_cast
    norm_num
  refine le_trans ?_ hX
  have := mul_le_mul_of_nonneg_left (show (CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cS mS
        + 2 * ∑ k : Fin 300, ∑ l : Fin 180, mS k * mL l * CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS k) (cL l)
        + CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL) ≤ (IBOUND : ℝ) + 2 * (-(X1 : ℝ) / 2 ^ 129) + (-(X2 : ℝ) / 2 ^ 129) by linarith)
    (by norm_num : (0 : ℝ) ≤ 64 / 81)
  exact this

end CatalanCore.Cert.SigmaHyb
