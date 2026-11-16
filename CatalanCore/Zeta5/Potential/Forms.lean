module

public import CatalanCore.Zeta5.Potential.Closed
public import CatalanCore.Zeta5.Potential.Eval

/-!
# Z5-POTENTIAL, part 7: the closed forms with the rational evaluators plugged in

The three statements the decay cells consume, in terms of `energyAux`, `chebAux` and `tailAux`
(`Eval`): the energy, the potential inside the support at a rational point, and the cosh branch at
a rational `r = e^{-w}`.
-/

@[expose] public section

open MeasureTheory Set Polynomial

namespace CatalanCore.Zeta5.Potential

noncomputable section

theorem energy_nu_eval {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) (cs : List ℚ) (hlen : cs.length = N)
    (hc : ∀ i (hi : i < cs.length), c (i + 1) = ((cs[i] : ℚ) : ℝ)) :
    ∫ t, logPot (nu c N b) t ∂(nu c N b) =
      c 0 ^ 2 * Real.log (b / 4) - ((energyAux 1 cs : ℚ) : ℝ) := by
  rw [energy_nu hb hpos, energyAux_cast c cs 1 (fun i hi => by rw [add_comm]; exact hc i hi), hlen]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]

theorem logPot_nu_outside_eval {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {q : ℚ} (hq : (q : ℝ) ∈ Ioo (0 : ℝ) 1)
    (cs : List ℚ) (hlen : cs.length = N)
    (hc : ∀ i (hi : i < cs.length), c (i + 1) = ((cs[i] : ℚ) : ℝ)) :
    logPot (nu c N b) (b * (1 + (q : ℝ)) ^ 2 / (4 * (q : ℝ))) =
      c 0 * (Real.log (b / 4) - Real.log (q : ℝ)) - ((tailAux q 1 q cs : ℚ) : ℝ) := by
  rw [logPot_nu_outside hb hpos hq,
    tailAux_cast q c cs 1 q (by simp) (fun i hi => by rw [add_comm]; exact hc i hi), hlen]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1 k]

theorem logPot_nu_inside_eval {c : ℕ → ℝ} {N : ℕ} {b : ℝ} (hb : 0 < b)
    (hpos : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ chebF c N x) {x : ℚ} (hx : (x : ℝ) ∈ Icc (-1 : ℝ) 1)
    (σ : ℚ) (cs : List ℚ) (hlen : cs.length = N)
    (hc : ∀ i (hi : i < cs.length), ((cs[i] : ℚ) : ℝ) * (σ : ℝ) ^ (i + 1) = c (i + 1)) :
    logPot (nu c N b) (b / 2 * (1 + (x : ℝ))) =
      c 0 * Real.log (b / 4) - ((chebAux σ x 1 1 (σ * x) cs : ℚ) : ℝ) := by
  have ht : b / 2 * (1 + (x : ℝ)) ∈ Icc (0 : ℝ) b :=
    ⟨by nlinarith [hx.1], by nlinarith [hx.2]⟩
  have hx2 : 2 * (b / 2 * (1 + (x : ℝ))) / b - 1 = (x : ℝ) := by field_simp; ring
  rw [logPot_nu_inside hb hpos ht, hx2]
  have h := chebAux_cast σ x c cs 0 1 (σ * x) (by simp [chebN]) (by
      simp [chebN, Chebyshev.T_one]) (fun i hi => by
        have := hc i hi
        rw [show 0 + 1 + i = i + 1 by ring]; exact this)
  rw [show (0 : ℕ) + 1 = 1 from rfl] at h
  rw [h, hlen]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 0 + 1 + k = k + 1 by ring]
  rfl

end

end CatalanCore.Zeta5.Potential
