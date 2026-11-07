module

public import CatalanMeasure.GenD.Signed.DesignConst
public import CatalanMeasure.GenD.PayW
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option Elab.async false

/-! Generic payment gates. -/

namespace CatalanMeasure.GenD.Signed
open CatalanMeasure.GenD
noncomputable section

/-- Generic payment gate with window `w`. -/
theorem payB_of_w (w d0 rho eta delta B : ℝ) (hrho : 0 < rho) (hw : 0 < w) (hd : 0 < delta)
    (he : 0 < eta) (he2 : eta < 2 * d0) (hk : 2 * w * rho < B)
    (hwin : rho < 2 * (w * rho - delta * (2 * B - w * rho)))
    (hpay : d0 * rho + 4 * d0 * delta * B < eta * B) :
    PayW w d0 rho eta (B / rho) delta B := by
  have hB : 0 < B := by nlinarith
  have hkap : 0 < B / rho := by positivity
  have e : B / rho * rho = B := by field_simp
  refine ⟨by rw [mul_comm]; exact e, he, hrho, hw, ?_, hd, ?_, he2, ?_⟩
  · rw [lt_div_iff₀ hrho]; exact hk
  · have : 2 * (w - delta * (2 * (B / rho) - w)) * rho = 2 * (w * rho - delta * (2 * B - w * rho)) := by
      field_simp
    have h2 : 1 * rho < 2 * (w - delta * (2 * (B / rho) - w)) * rho := by rw [this]; linarith
    exact lt_of_mul_lt_mul_right h2 hrho.le
  · have : (d0 + 4 * d0 * delta * (B / rho)) * rho = d0 * rho + 4 * d0 * delta * B := by
      field_simp
    have h2 : (d0 + 4 * d0 * delta * (B / rho)) * rho < eta * (B / rho) * rho := by
      have e2 : eta * (B / rho) * rho = eta * B := by field_simp
      rw [this, e2]; exact hpay
    exact lt_of_mul_lt_mul_right h2 hrho.le

/-- Generic S2 gate: `payB_of_w` for the criterion `PayW'` (no floor `B > rho`).  The conclusion
type is `PayW'`, not `PayW`, so Theorem410 cannot consume it unchanged.  Hypotheses are the
`PayW'` clauses cleared of `kappa = B / rho`. -/
theorem payB'_of_w (w d0 rho eta delta B : ℝ) (hrho : 0 < rho) (hw : 0 < w) (hd : 0 < delta)
    (hd3 : delta < 1 / 3) (he : 0 < eta) (he2 : eta < 2 * d0) (hk : w * rho < B)
    (hs2 : d0 * rho ≤ (B - w * rho) * (eta + 2 * d0 * (1 - 3 * delta)))
    (hwin : rho < 2 * (w * rho - delta * (2 * B - w * rho)))
    (hpay : d0 * rho + 4 * d0 * delta * B < eta * B) :
    PayW' w d0 rho eta (B / rho) delta B := by
  have e : B / rho * rho = B := by field_simp
  refine ⟨by rw [mul_comm]; exact e, he, hrho, hw, ?_, hd, hd3, ?_, ?_, he2, ?_⟩
  · rw [lt_div_iff₀ hrho]; exact hk
  · have h2 : d0 * rho ≤ ((B / rho - w) * (eta + 2 * d0 * (1 - 3 * delta))) * rho := by
      have : ((B / rho - w) * (eta + 2 * d0 * (1 - 3 * delta))) * rho
          = (B - w * rho) * (eta + 2 * d0 * (1 - 3 * delta)) := by field_simp
      rw [this]; exact hs2
    exact le_of_mul_le_mul_right h2 hrho
  · have : 2 * (w - delta * (2 * (B / rho) - w)) * rho = 2 * (w * rho - delta * (2 * B - w * rho)) := by
      field_simp
    have h2 : 1 * rho < 2 * (w - delta * (2 * (B / rho) - w)) * rho := by rw [this]; linarith
    exact lt_of_mul_lt_mul_right h2 hrho.le
  · have : (d0 + 4 * d0 * delta * (B / rho)) * rho = d0 * rho + 4 * d0 * delta * B := by
      field_simp
    have h2 : (d0 + 4 * d0 * delta * (B / rho)) * rho < eta * (B / rho) * rho := by
      have e2 : eta * (B / rho) * rho = eta * B := by field_simp
      rw [this, e2]; exact hpay
    exact lt_of_mul_lt_mul_right h2 hrho.le

namespace Generic

/-- The payment criterion instantiated at the determinant degree of a shared design. -/
theorem payB (dc : DesignConst) (w rho eta delta B : ℝ)
    (hrho : 0 < rho) (hw : 0 < w) (hd : 0 < delta)
    (he : 0 < eta) (he2 : eta < 2 * (dc.d0 : ℝ)) (hk : 2 * w * rho < B)
    (hwin : rho < 2 * (w * rho - delta * (2 * B - w * rho)))
    (hpay : (dc.d0 : ℝ) * rho + 4 * (dc.d0 : ℝ) * delta * B < eta * B) :
    PayW w (dc.d0 : ℝ) rho eta (B / rho) delta B :=
  payB_of_w w dc.d0 rho eta delta B hrho hw hd he he2 hk hwin hpay

/-- The primed criterion remains separate; concrete public wrappers keep `PayW`. -/
theorem payB' (dc : DesignConst) (w rho eta delta B : ℝ)
    (hrho : 0 < rho) (hw : 0 < w) (hd : 0 < delta) (hd3 : delta < 1 / 3)
    (he : 0 < eta) (he2 : eta < 2 * (dc.d0 : ℝ)) (hk : w * rho < B)
    (hs2 : (dc.d0 : ℝ) * rho ≤ (B - w * rho) * (eta + 2 * (dc.d0 : ℝ) * (1 - 3 * delta)))
    (hwin : rho < 2 * (w * rho - delta * (2 * B - w * rho)))
    (hpay : (dc.d0 : ℝ) * rho + 4 * (dc.d0 : ℝ) * delta * B < eta * B) :
    PayW' w (dc.d0 : ℝ) rho eta (B / rho) delta B :=
  payB'_of_w w dc.d0 rho eta delta B hrho hw hd hd3 he he2 hk hs2 hwin hpay

/-- A certified baseline budget and gain leave the requested decay margin. -/
theorem gain_ok (base eta A tD price : ℝ) (hT : tD = base + A)
    (hgain : eta - A < base - price) : eta < tD - price := by
  rw [hT]
  linarith only [hgain]

end Generic

end
end CatalanMeasure.GenD.Signed
#print axioms CatalanMeasure.GenD.Signed.payB_of_w
#print axioms CatalanMeasure.GenD.Signed.payB'_of_w

#print axioms CatalanMeasure.GenD.Signed.Generic.payB
#print axioms CatalanMeasure.GenD.Signed.Generic.payB'
#print axioms CatalanMeasure.GenD.Signed.Generic.gain_ok

