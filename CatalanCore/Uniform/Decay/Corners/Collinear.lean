module

public import CatalanCore.Uniform.Decay.Corners.CollinearLimit

@[expose] public section

/-!
# Boundary-energy identity for coincident supporting lines (`B² = A C`)

`BE_collinear`: for `A, C > 0` and `B² = A C` (the vectors `u, v` are real multiples of each other,
so `qf = A (s + (B/A) t)²` vanishes on a whole line through the origin) the boundary-energy identity
holds on every rectangle `[a,b] × [c,d]`, including those crossed by the singular line.  Proof: the
identity holds for the positive definite forms `(A+δ, B, C+δ)` (`BE_pd`); let `δ → 0⁺` (dominated
convergence, majorant `S^i T^j (c + |log (s + κ t)|)`, `κ = B/A`).

`BE_parallel`: combined statement for every real form with `B² ≤ A C`, `A, C > 0`.
The remaining configuration, **parallel distinct** supporting lines, is not a centred form: the
kernel is then non-singular (distance between the lines is positive) and the centred-monomial
identity is not the relevant statement (spec v8 §3.1 rejection).  The vector-level statement `BE_vectors` covers every pair of nonzero direction vectors `u, v`
(supporting lines through the common point `0`); distinct parallel lines have no common point and
are outside this set-up.
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory Filter Topology
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C : ℝ}

theorem BE_collinear (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 = A * C) (i j : ℕ) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) : BE A B C i j a b c d := by
  obtain ⟨ib, tb⟩ := edge_t_limit hA hC hB i j b hcd
  obtain ⟨ia, ta⟩ := edge_t_limit hA hC hB i j a hcd
  obtain ⟨id', td⟩ := edge_s_limit hA hC hB i j d hab
  obtain ⟨ic, tc⟩ := edge_s_limit hA hC hB i j c hab
  set P : ℝ := (b ^ (i + 1) - a ^ (i + 1)) * (d ^ (j + 1) - c ^ (j + 1))
    / (((i : ℝ) + 1) * ((j : ℝ) + 1)) with hP
  have eLim : BER A B C i j a b c d =
      (((∫ t in c..d, b ^ (i + 1) * t ^ j * Lq A B C b t)
        - ∫ t in c..d, a ^ (i + 1) * t ^ j * Lq A B C a t)
      + ((∫ s in a..b, s ^ i * d ^ (j + 1) * Lq A B C s d)
        - ∫ s in a..b, s ^ i * c ^ (j + 1) * Lq A B C s c)) - P := by
    unfold BER
    rw [intervalIntegral.integral_sub ib ia, intervalIntegral.integral_sub id' ic]
  have eDel : ∀ᶠ δ in 𝓝[>] (0 : ℝ), BER (A + δ) B (C + δ) i j a b c d =
      (((∫ t in c..d, b ^ (i + 1) * t ^ j * Lq (A + δ) B (C + δ) b t)
        - ∫ t in c..d, a ^ (i + 1) * t ^ j * Lq (A + δ) B (C + δ) a t)
      + ((∫ s in a..b, s ^ i * d ^ (j + 1) * Lq (A + δ) B (C + δ) s d)
        - ∫ s in a..b, s ^ i * c ^ (j + 1) * Lq (A + δ) B (C + δ) s c)) - P := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hpd := PD_reg hA hC hB hδ
    unfold BER
    rw [intervalIntegral.integral_sub (edge_t_integrable hpd i j b c d)
      (edge_t_integrable hpd i j a c d),
      intervalIntegral.integral_sub (edge_s_integrable hpd i j d a b)
      (edge_s_integrable hpd i j c a b)]
  have tBER : Tendsto (fun δ : ℝ => BER (A + δ) B (C + δ) i j a b c d) (𝓝[>] 0)
      (𝓝 (BER A B C i j a b c d)) := by
    rw [eLim]
    refine Tendsto.congr' (eDel.mono fun δ h => h.symm) ?_
    exact (((tb.sub ta).add (td.sub tc)).sub tendsto_const_nhds)
  have tL := (tendsto_BEL hA hC hB i j hab hcd).const_mul ((i : ℝ) + j + 2)
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ((i : ℝ) + j + 2) * BEL (A + δ) B (C + δ) i j a b c d
      = BER (A + δ) B (C + δ) i j a b c d := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact BE_pd (PD_reg hA hC hB hδ) i j hab hcd
  exact tendsto_nhds_unique (tL.congr' hev) tBER

/-- **Boundary-energy identity for every form `|s u - t v|²` with `u, v ≠ 0` and non-diverging
supporting lines**: `A, C > 0`, `B² ≤ A C` (`B² < A C`: transversal lines, `B² = A C`: coincident
lines).  Valid for every rectangle. -/
theorem BE_parallel_or_transversal (hA : 0 < A) (hC : 0 < C) (hB : B ^ 2 ≤ A * C) (i j : ℕ)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) : BE A B C i j a b c d := by
  rcases hB.lt_or_eq with h | h
  · exact BE_pd (PD.of_posdef hA hC h) i j hab hcd
  · exact BE_collinear hA hC h i j hab hcd

/-- Lagrange identity: `A C - B² = (u × v)²` for `A = |u|²`, `B = -u·v`, `C = |v|²`. -/
theorem disc_eq (ur ui vr vi : ℝ) :
    (ur ^ 2 + ui ^ 2) * (vr ^ 2 + vi ^ 2) - (-(ur * vr + ui * vi)) ^ 2 = (ur * vi - ui * vr) ^ 2 := by
  ring

/-- `qf` is `|s u - t v|²` for `A = |u|²`, `B = -u·v`, `C = |v|²`. -/
theorem qf_eq_sq (ur ui vr vi s t : ℝ) :
    qf (ur ^ 2 + ui ^ 2) (-(ur * vr + ui * vi)) (vr ^ 2 + vi ^ 2) s t
      = (s * ur - t * vr) ^ 2 + (s * ui - t * vi) ^ 2 := by
  unfold qf; ring

/-- **Boundary-energy identity for two nonzero direction vectors `u = (ur, ui)`, `v = (vr, vi)`**
(supporting lines through the common point `0`; transversal or coincident), every rectangle. -/
theorem BE_vectors {ur ui vr vi : ℝ} (hu : ur ^ 2 + ui ^ 2 ≠ 0) (hv : vr ^ 2 + vi ^ 2 ≠ 0)
    (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    BE (ur ^ 2 + ui ^ 2) (-(ur * vr + ui * vi)) (vr ^ 2 + vi ^ 2) i j a b c d := by
  refine BE_parallel_or_transversal (lt_of_le_of_ne (by positivity) (Ne.symm hu))
    (lt_of_le_of_ne (by positivity) (Ne.symm hv)) ?_ i j hab hcd
  nlinarith [disc_eq ur ui vr vi, sq_nonneg (ur * vi - ui * vr)]

end CatalanCore.Uniform.Decay.Corners
