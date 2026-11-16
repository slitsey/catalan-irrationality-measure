module

public import CatalanCore.Zeta5.Cells.Enclosures

@[expose] public section

/-!
# Z5-CELLS, part 11: ZD22, the exact constant inequality

`D = I − λ M₀ − C` with `I = λ² log(b/4) − E` (`E = Σ c_k²/(2k)`, the energy of Z5-POTENTIAL
`energy_nu`) and `C = −2λ + 12αλ(1 − log α) + 3λ² − 2λ² log(2λ)`.  `zd22_sound`: the Boolean check
`zd22Ok` (three certified logarithms, `logQ`, and exact rational arithmetic) implies
`D0 < D` for the rational threshold `D0` (plan: `D0 = 1288519/10⁶ + 33574799/348000000`, so that
`D > D0` gives `μ < 87`; the design value is `D = 1.38500086`).  Generic in `λ, α, b, E, M₀`.
-/

namespace CatalanCore.Zeta5.Cells

open Real CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Cert (qabs)

noncomputable section

/-- `D = I − λ M₀ − C` with `I = λ² log(b/4) − E`, `b = y_b²`. -/
def Dval (lam α yb E M0 : ℝ) : ℝ :=
  (lam ^ 2 * Real.log (yb ^ 2 / 4) - E) - lam * M0 -
    (-2 * lam + 12 * α * lam * (1 - Real.log α) + 3 * lam ^ 2 - 2 * lam ^ 2 * Real.log (2 * lam))

/-- **ZD22** as a proposition. -/
def ZD22 (lam α yb E M0 D0 : ℝ) : Prop := D0 < Dval lam α yb E M0

def DEnc (lam α E M0 : ℚ) (La Lb Lc : ℚ × ℚ) : ℚ × ℚ :=
  (lam ^ 2 * La.1 + 12 * α * lam * Lb.1 + 2 * lam ^ 2 * Lc.1 - E - lam * M0 + 2 * lam
      - 12 * α * lam - 3 * lam ^ 2,
    qabs (lam ^ 2) * La.2 + qabs (12 * α * lam) * Lb.2 + qabs (2 * lam ^ 2) * Lc.2)

theorem DEnc_spec (lam α yb E M0 : ℚ) {La Lb Lc : ℚ × ℚ}
    (hLa : Enc (Real.log ((yb : ℝ) ^ 2 / 4)) La) (hLb : Enc (Real.log (α : ℝ)) Lb)
    (hLc : Enc (Real.log (2 * (lam : ℝ))) Lc) :
    Enc (Dval (lam : ℝ) (α : ℝ) (yb : ℝ) (E : ℝ) (M0 : ℝ)) (DEnc lam α E M0 La Lb Lc) := by
  have a1 := hLa.mulQ (lam ^ 2)
  have a2 := hLb.mulQ (12 * α * lam)
  have a3 := hLc.mulQ (2 * lam ^ 2)
  have a4 := (a1.add a2).add a3
  unfold Enc at a4 ⊢
  have e : Dval (lam : ℝ) (α : ℝ) (yb : ℝ) (E : ℝ) (M0 : ℝ) =
      (((lam ^ 2 : ℚ) : ℝ) * Real.log ((yb : ℝ) ^ 2 / 4) +
        ((12 * α * lam : ℚ) : ℝ) * Real.log (α : ℝ) +
        ((2 * lam ^ 2 : ℚ) : ℝ) * Real.log (2 * (lam : ℝ))) +
      (((-E - lam * M0 + 2 * lam - 12 * α * lam - 3 * lam ^ 2 : ℚ)) : ℝ) := by
    unfold Dval; push_cast; ring
  rw [e]
  have h := a4
  simp only at h
  have hc : |(((lam ^ 2 : ℚ) : ℝ) * Real.log ((yb : ℝ) ^ 2 / 4) +
        ((12 * α * lam : ℚ) : ℝ) * Real.log (α : ℝ) +
        ((2 * lam ^ 2 : ℚ) : ℝ) * Real.log (2 * (lam : ℝ))) -
      (((lam ^ 2 * La.1 + 12 * α * lam * Lb.1 + 2 * lam ^ 2 * Lc.1 : ℚ)) : ℝ)| ≤
      (((qabs (lam ^ 2) * La.2 + qabs (12 * α * lam) * Lb.2 + qabs (2 * lam ^ 2) * Lc.2 : ℚ)) :
        ℝ) := by
    have := h
    push_cast at this ⊢
    convert this using 2
  have hd : ((DEnc lam α E M0 La Lb Lc).1 : ℝ) =
      (((lam ^ 2 * La.1 + 12 * α * lam * Lb.1 + 2 * lam ^ 2 * Lc.1 : ℚ)) : ℝ) +
      (((-E - lam * M0 + 2 * lam - 12 * α * lam - 3 * lam ^ 2 : ℚ)) : ℝ) := by
    unfold DEnc; push_cast; ring
  rw [hd]
  have := hc
  convert this using 2 <;> first | rfl | (unfold DEnc; rfl) | ring

/-- the Boolean check -/
def zd22Ok (n : ℕ) (lam α yb E M0 D0 : ℚ) : Bool :=
  match logQ n (yb ^ 2 / 4), logQ n α, logQ n (2 * lam) with
  | some La, some Lb, some Lc =>
      decide (D0 < (DEnc lam α E M0 La Lb Lc).1 - (DEnc lam α E M0 La Lb Lc).2)
  | _, _, _ => false

theorem zd22_sound {n : ℕ} {lam α yb E M0 D0 : ℚ} (h : zd22Ok n lam α yb E M0 D0 = true) :
    ZD22 (lam : ℝ) (α : ℝ) (yb : ℝ) (E : ℝ) (M0 : ℝ) (D0 : ℝ) := by
  unfold zd22Ok at h
  split at h
  · rename_i La Lb Lc h1 h2 h3
    simp only [decide_eq_true_eq] at h
    have eLa := (logQ_spec h1).2
    have eLb := (logQ_spec h2).2
    have eLc := (logQ_spec h3).2
    push_cast at eLa eLc
    have := DEnc_spec lam α yb E M0 eLa eLb eLc
    have hl := this.ge_lower
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    unfold ZD22
    linarith
  · simp at h

end

end CatalanCore.Zeta5.Cells
