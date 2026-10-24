module

public import CatalanCore.Decay.Rect.WindowMinor

@[expose] public section

open Finset Polynomial

namespace CatalanCore

variable {sl : ℝ}

open Decay

/-- **The rectangular window.** -/
theorem window_rect {Fr : Frame} (hFr : Fr.DecayOKs' sl) {e : ℝ} (he0 : 0 < e) (he1 : e < 1)
    {m0 : ℝ} (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i) {r m N0 : ℕ} {R : ℝ}
    (hR : (N0 : ℝ) ≤ R) {T0 cc : ℝ}
    (hEn : ∀ (k : ℕ) (s : Fin k → Fin (r + m)), Function.Injective s →
        (∀ b : Fin (r + m), r ≤ (b : ℕ) → ∃ i, s i = b) →
        Frame.RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0) (T0 + r * (((r : ℝ) + m) - k) * cc)
          (fun i => xnode r (s i)) (fun i => ynode r (s i)))
    {t : ℝ} (ht : |t| ≤ Real.exp (-cc * r)) :
    |Polynomial.aeval (Fr.const + t) (Fr.fullPoly r m)|
      ≤ 2 ^ r * Real.exp (T0 + ((r : ℝ) + m) * Real.log (Fr.Wabs * R
          + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (Fr.Aco ^ e / Frame.betaE sl e) + 1))) := by
  rw [Rect.aeval_fullPoly]
  simpa using (window_rect_common (ι := Fin r) hFr he0 he1 hm0xs hm0μ hR
    (fun a => a) Function.injective_id hEn ht)

end CatalanCore
