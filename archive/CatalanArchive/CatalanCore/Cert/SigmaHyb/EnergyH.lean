module

public import CatalanArchive.CatalanCore.Cert.SigmaHyb.IData
public import CatalanArchive.CatalanCore.Decay.Rect.IrhoAppend
public import CatalanArchive.CatalanCore.Decay.Rect.EnergyGen

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

lemma iTotL_eq (B A : List Pt) : iTotL B A = CatalanCore.Decay.EnergyGen.iTotL iRow B A := by
  induction A with
  | nil => simp [iTotL, CatalanCore.Decay.EnergyGen.iTotL]
  | cons p ps ih => simp only [iTotL, CatalanCore.Decay.EnergyGen.iTotL, ih]

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
  refine CatalanCore.Decay.EnergyGen.sum2_le_gen row_eq _ sigmaS lamS (fun k : Fin 300 => ptAt k) (fun l : Fin 180 => ptAtL lamS l)
    sum_sigma (sum_gen lamS 180 lamS_len) (fun k l => ?_) X1 (by rw [← iTotL_eq]; exact X1_val)
  have := pair_le (ptAt k) (ptAtL lamS l)
  unfold mS mL mOfL
  exact this

theorem ll_le : CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL ≤ -(X2 : ℝ) / 2 ^ 129 := by
  unfold CatalanLambda.Decay.Irho
  refine CatalanCore.Decay.EnergyGen.sum2_le_gen row_eq _ lamS lamS (fun k : Fin 180 => ptAtL lamS k) (fun l : Fin 180 => ptAtL lamS l)
    (sum_gen lamS 180 lamS_len) (sum_gen lamS 180 lamS_len) (fun k l => ?_) X2
    (by rw [← iTotL_eq]; exact X2_val)
  have := pair_le (ptAtL lamS k) (ptAtL lamS l)
  unfold mL mOfL
  exact this

theorem Irho_hyb_expand :
    CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cH wtH
      = (64 / 81) * (CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cS mS
        + 2 * ∑ k : Fin 300, ∑ l : Fin 180, mS k * mL l * CatalanLambda.Decay.krho (1 / 1024 : ℝ) (cS k) (cL l)
        + CatalanLambda.Decay.Irho (1 / 1024 : ℝ) cL mL) := by
  have h := CatalanCore.Decay.Irho_append_div (1 / 1024 : ℝ) (1 + 1 / 8) (by norm_num) cS mS cL mL
  have e : (fun k : Fin (300 + 180) => (Fin.append mS mL k) / (1 + (1 / 8 : ℝ))) = wtH := rfl
  rw [e] at h
  unfold cH
  rw [h]
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
