module
public import CatalanCore.Li2.DecayCert.Holder.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
noncomputable section

theorem endPhi_le_of_upper (d : SegmentData) (b e : ℂ) (D Z H : ℝ) (hD : 0 ≤ D)
    (hZ : endZ d b e D ≤ Z) (hH : Z ≤ H) (hsq : Z^2+1 ≤ (H-Z)^2) :
    endPhi d b e D ≤ H := by
  have hz := endZ_nonneg d b e D hD
  have hZ0 : 0 ≤ Z := hz.trans hZ
  have hroot : Real.sqrt (Z^2+1) ≤ H-Z := Real.sqrt_le_iff.2 ⟨sub_nonneg.mpr hH,hsq⟩
  have hmono : Real.sqrt ((endZ d b e D)^2+1) ≤ Real.sqrt (Z^2+1) :=
    Real.sqrt_le_sqrt (by nlinarith)
  unfold endPhi
  linarith

theorem qsegment_F_bound (d : QSegment) (Φ H : ℝ) (hΦ : 0 ≤ Φ) (hH : Φ ≤ H) :
    (∑ k ∈ Finset.range (d.coeff.length-1+1),|(d.c k:ℝ)| *Φ^k) ≤
      ∑ k ∈ Finset.range d.coeff.length,|(d.c k:ℝ)| *H^k := by
  by_cases hz : d.coeff=[]
  · simp [hz,QSegment.c]
  · have hn : d.coeff.length-1+1=d.coeff.length := by
      have hh := List.length_pos_iff.mpr hz
      omega
    rw [hn]
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΦ hH k) (abs_nonneg _)

theorem qsegment_A_bound (d : QSegment) (Φ H : ℝ) (hΦ : 0 ≤ Φ) (hH : Φ ≤ H) :
    (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *Φ^k) ≤
      ∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *H^k := by
  apply Finset.sum_le_sum
  intro k hk
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΦ hH k) (by positivity)

theorem branch_majorant_le (F A l Fq Aq L root den : ℝ)
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hl : 0 ≤ l) (hFq : F ≤ Fq) (hAq : A ≤ Aq)
    (hL : l ≤ L) (hroot : 0 ≤ root) (hsq : L ≤ root^2)
    (hden : 0 < den) (hdsq : den^2 ≤ 2-L) :
    F*(2*Real.sqrt l/Real.sqrt (2-l))+A*l ≤ 2*Fq*root/den+Aq*L := by
  have hsqrt : Real.sqrt l ≤ root := Real.sqrt_le_iff.2 ⟨hroot,hL.trans hsq⟩
  have hden' : den ≤ Real.sqrt (2-l) := (Real.le_sqrt hden.le (by nlinarith [sq_nonneg den] : 0 ≤ 2-l)).2 (by linarith)
  have hfac : 2*Real.sqrt l/Real.sqrt (2-l) ≤ 2*root/den := by
    apply div_le_div₀ (by positivity) (by linarith) hden (by linarith)
  have hprod := mul_le_mul hFq hfac (by positivity : 0 ≤ 2*Real.sqrt l/Real.sqrt (2-l))
    (hF.trans hFq)
  have hprod2 := mul_le_mul hAq hL hl (hA.trans hAq)
  calc
    _ ≤ Fq*(2*root/den)+Aq*L := add_le_add hprod hprod2
    _ = _ := by ring

theorem off_majorant_le (F A l d1 d2 Fq Aq L D1 D2 den : ℝ)
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hl : 0 ≤ l) (hFq : F ≤ Fq) (hAq : A ≤ Aq)
    (hL : l ≤ L) (hd1 : D1 ≤ d1) (hd2 : D2 ≤ d2) (hL1 : L < D1) (hL2 : L < D2)
    (hden : 0 < den) (hdsq : den^2 ≤ (D1-L)*(D2-L)) :
    F*(l/Real.sqrt ((d1-l)*(d2-l)))+A*l ≤ Fq*L/den+Aq*L := by
  have h1 : 0 ≤ D1-L := sub_nonneg.mpr hL1.le
  have h2 : 0 ≤ D2-L := sub_nonneg.mpr hL2.le
  have hp : (D1-L)*(D2-L) ≤ (d1-l)*(d2-l) :=
    mul_le_mul (by linarith) (by linarith) h2 (by linarith)
  have hden' : den ≤ Real.sqrt ((d1-l)*(d2-l)) := (Real.le_sqrt hden.le (by nlinarith [sq_nonneg den] : 0 ≤ (d1-l)*(d2-l))).2 (hdsq.trans hp)
  have hfac : l/Real.sqrt ((d1-l)*(d2-l)) ≤ L/den := by
    apply div_le_div₀ (hl.trans hL) hL hden (by linarith)
  have hprod := mul_le_mul hFq hfac (by positivity : 0 ≤ l/Real.sqrt ((d1-l)*(d2-l))) (hF.trans hFq)
  have hprod2 := mul_le_mul hAq hL hl (hA.trans hAq)
  calc
    _ ≤ Fq*(L/den)+Aq*L := add_le_add hprod hprod2
    _ = _ := by ring
#print axioms endPhi_le_of_upper
#print axioms qsegment_F_bound
#print axioms qsegment_A_bound
#print axioms branch_majorant_le
#print axioms off_majorant_le
end
end CatalanCore.Li2.DecayCert
