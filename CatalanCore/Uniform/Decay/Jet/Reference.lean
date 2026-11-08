module

public import CatalanLambda.Decay.CauchyDetFull
public import CatalanLambda.Decay.ThmNLog
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section
set_option Elab.async false

/-!
# Jets to the reference: Lemma J (lane H, wave H2c; ledger P208, S15)

`Dj κ ε s σ x` is the Cauchy determinant `det [(x_l - s_i)⁻¹]` in which the rows `l ∈ σ` carry the jet
`κ_l v + ε_l v′` (`v = (x - s)⁻¹`, `v′ = -(x - s)⁻²`).

* `Dj_insert`: `Dj (insert l σ) x = κ_l · Dj σ x + ε_l · ∂_l (Dj σ) x` (multilinearity of the determinant in
  the row `l`; no partial-derivative interchange is needed because each step differentiates the determinant
  of an explicit matrix in one row).
* `norm_Dj_le`: the iterated Cauchy estimate of Lemma J.  If `Dj ∅` is bounded by `M` on the polydisc of radius
  `ρ` around `c` in the variables of `J` and the poles `s_i` stay outside the discs, then
  `‖Dj J c‖ ≤ ∏_{l∈J} (‖κ_l‖ + ‖ε_l‖ / ρ) · M`.

* `norm_cexpr_le`: the ratio of the Cauchy expressions of two position lists (the pair factors and the node
  factors against a reference), and `lemmaJ_abstract`: **Lemma J**,
  `‖Dj J c‖ ≤ ∏_{l∈J}(‖κ_l‖ + ‖ε_l‖/ρ) · exp(jetExponent) · ‖cexpr(x⁰, s)‖` for a reference `x⁰` and a polydisc
  within `eJ` of it; `jetExponent` is the sum of `(e_l + e_l′)/d_{ll′}` over the pairs not flagged tight and of
  `e_l / m_{li}` over positions and nodes.
* The two sums that make the exponent `O(k log k)`: `sum_inv_node_le` (distinct naturals: harmonic, with
  `harmonic_shift_le`) and `sum_inv_sep_le` (points of a line at least `g` apart, harmonic in the count).

Everything here is generic in the nodes `s`, the centres `c`, the radii, the jet coefficients and the reference
(GD9: no reference frame, weight or `xs` appears; the plane 2 values live in `Bank.Plane2.Const`).
-/

open Matrix Finset Complex Function

namespace CatalanCore.Uniform.Decay.Jet

variable {k : ℕ}

/-- The Cauchy row `((w - s_i)⁻¹)_i`. -/
noncomputable def vr (s : Fin k → ℕ) (w : ℂ) : Fin k → ℂ := fun i => (w - (s i : ℂ))⁻¹

/-- Its derivative `(-(w - s_i)⁻²)_i`. -/
noncomputable def dvr (s : Fin k → ℕ) (w : ℂ) : Fin k → ℂ := fun i => -((w - (s i : ℂ))⁻¹) ^ 2

/-- The jet row `κ v + ε v′`. -/
noncomputable def jr (κ ε : ℂ) (s : Fin k → ℕ) (w : ℂ) : Fin k → ℂ := κ • vr s w + ε • dvr s w

/-- The partially jetted Cauchy determinant. -/
noncomputable def Dj (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (σ : Finset (Fin k)) (x : Fin k → ℂ) : ℂ :=
  (Matrix.of fun l => if l ∈ σ then jr (κ l) (ε l) s (x l) else vr s (x l)).det

/-- Linear in the row `l`. -/
noncomputable def rowDetLin (N : Matrix (Fin k) (Fin k) ℂ) (l : Fin k) : (Fin k → ℂ) →ₗ[ℂ] ℂ where
  toFun v := (N.updateRow l v).det
  map_add' u v := Matrix.det_updateRow_add N l u v
  map_smul' c u := by
    simpa using Matrix.det_updateRow_smul N l c u

theorem rowDetLin_apply (N : Matrix (Fin k) (Fin k) ℂ) (l : Fin k) (v : Fin k → ℂ) :
    rowDetLin N l v = (N.updateRow l v).det := rfl

/-- The matrix of `Dj σ (update x l w)` with the row `l` removed. -/
noncomputable def restM (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (σ : Finset (Fin k)) (x : Fin k → ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun l => if l ∈ σ then jr (κ l) (ε l) s (x l) else vr s (x l)

theorem Dj_update (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (σ : Finset (Fin k)) (x : Fin k → ℂ) (l : Fin k)
    (hl : l ∉ σ) (w : ℂ) :
    Dj κ ε s σ (update x l w) = rowDetLin (restM κ ε s σ x) l (vr s w) := by
  rw [rowDetLin_apply]
  unfold Dj
  congr 1
  ext l' j
  by_cases h : l' = l
  · subst h
    simp [Matrix.updateRow_self, hl]
  · simp [Matrix.updateRow_ne h, restM, update_of_ne h]

theorem hasDerivAt_vr (s : Fin k → ℕ) {w : ℂ} (hw : ∀ i, w ≠ (s i : ℂ)) :
    HasDerivAt (vr s) (dvr s w) w := by
  rw [hasDerivAt_pi]
  intro i
  have h1 : HasDerivAt (fun y : ℂ => y - (s i : ℂ)) 1 w := (hasDerivAt_id w).sub_const _
  have h2 := h1.inv (sub_ne_zero.2 (hw i))
  refine h2.congr_deriv ?_
  show -1 / (w - (s i : ℂ)) ^ 2 = -((w - (s i : ℂ))⁻¹) ^ 2
  rw [inv_pow]
  ring

theorem hasDerivAt_Dj (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (σ : Finset (Fin k)) (x : Fin k → ℂ) (l : Fin k)
    (hl : l ∉ σ) (hw : ∀ i, x l ≠ (s i : ℂ)) :
    HasDerivAt (fun w => Dj κ ε s σ (update x l w))
      (rowDetLin (restM κ ε s σ x) l (dvr s (x l))) (x l) := by
  have hfun : (fun w => Dj κ ε s σ (update x l w)) =
      (rowDetLin (restM κ ε s σ x) l).toContinuousLinearMap ∘ vr s := by
    funext w
    exact Dj_update κ ε s σ x l hl w
  rw [hfun]
  exact (rowDetLin (restM κ ε s σ x) l).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (x l)
    (hasDerivAt_vr s hw)

/-- **One jet step.**  Differentiating the row `l`. -/
theorem Dj_insert (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (σ : Finset (Fin k)) (x : Fin k → ℂ) (l : Fin k)
    (hl : l ∉ σ) (hw : ∀ i, x l ≠ (s i : ℂ)) :
    Dj κ ε s (insert l σ) x = κ l * Dj κ ε s σ x +
      ε l * deriv (fun w => Dj κ ε s σ (update x l w)) (x l) := by
  rw [(hasDerivAt_Dj κ ε s σ x l hl hw).deriv]
  have h1 : Dj κ ε s (insert l σ) x = rowDetLin (restM κ ε s σ x) l (jr (κ l) (ε l) s (x l)) := by
    rw [rowDetLin_apply]
    unfold Dj
    congr 1
    ext l' j
    by_cases h : l' = l
    · subst h
      simp [Matrix.updateRow_self]
    · simp [Matrix.updateRow_ne h, restM, h]
  have h2 : Dj κ ε s σ x = rowDetLin (restM κ ε s σ x) l (vr s (x l)) := by
    have := Dj_update κ ε s σ x l hl (x l)
    simpa using this
  rw [h1, h2, jr, map_add, map_smul, map_smul]
  simp

/-- **The iterated Cauchy estimate** (Lemma J, first half).  If `Dj ∅` is bounded by `M` on the polydisc of
radius `ρ` around `c` in the variables of `J` (the other variables sitting at their centres) and the poles
`s_i` lie outside the closed discs, then the jetted determinant at the centre is at most
`∏_{l∈J} (‖κ_l‖ + ‖ε_l‖ / ρ) · M`. -/
theorem norm_Dj_le (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (c : Fin k → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (J : Finset (Fin k)) (hpole : ∀ l ∈ J, ∀ i, ρ < ‖c l - (s i : ℂ)‖)
    {M : ℝ} (hM : ∀ x : Fin k → ℂ, (∀ l ∈ J, ‖x l - c l‖ ≤ ρ) → (∀ l, l ∉ J → x l = c l) →
      ‖Dj κ ε s ∅ x‖ ≤ M) :
    ‖Dj κ ε s J c‖ ≤ (∏ l ∈ J, (‖κ l‖ + ‖ε l‖ / ρ)) * M := by
  classical
  have key : ∀ σ : Finset (Fin k), σ ⊆ J → ∀ x : Fin k → ℂ,
      (∀ l ∈ J, l ∉ σ → ‖x l - c l‖ ≤ ρ) → (∀ l, l ∈ σ ∨ l ∉ J → x l = c l) →
      ‖Dj κ ε s σ x‖ ≤ (∏ l ∈ σ, (‖κ l‖ + ‖ε l‖ / ρ)) * M := by
    intro σ
    induction σ using Finset.induction_on with
    | empty =>
      intro _ x hx1 hx2
      simp only [Finset.prod_empty, one_mul]
      exact hM x (fun l hl => hx1 l hl (Finset.notMem_empty l))
        (fun l hl => hx2 l (Or.inr hl))
    | insert l σ hl ih =>
      intro hsub x hx1 hx2
      have hlJ : l ∈ J := hsub (Finset.mem_insert_self l σ)
      have hσJ : σ ⊆ J := (Finset.subset_insert l σ).trans hsub
      have hxl : x l = c l := hx2 l (Or.inl (Finset.mem_insert_self l σ))
      have hB0 : 0 ≤ (∏ l' ∈ σ, (‖κ l'‖ + ‖ε l'‖ / ρ)) * M := by
        -- M bounds a norm, so it is nonnegative once the polydisc is nonempty
        have := hM c (fun l' hl' => by simp [hρ.le]) (fun l' _ => rfl)
        have hM0 : 0 ≤ M := (norm_nonneg _).trans this
        exact mul_nonneg (Finset.prod_nonneg fun l' _ => by positivity) hM0
      set B := (∏ l' ∈ σ, (‖κ l'‖ + ‖ε l'‖ / ρ)) * M with hB
      -- the σ-bound on the whole disc in the variable l
      have hall : ∀ w : ℂ, ‖w - c l‖ ≤ ρ → ‖Dj κ ε s σ (update x l w)‖ ≤ B := by
        intro w hw
        refine ih hσJ (update x l w) (fun l' hl' hl'σ => ?_) (fun l' hl' => ?_)
        · by_cases h : l' = l
          · subst h; simpa using hw
          · rw [update_of_ne h]
            exact hx1 l' hl' (by simp [h, hl'σ])
        · by_cases h : l' = l
          · subst h
            rcases hl' with h1 | h1
            · exact absurd h1 hl
            · exact absurd hlJ h1
          · rw [update_of_ne h]
            refine hx2 l' ?_
            rcases hl' with h1 | h1
            · exact Or.inl (Finset.mem_insert_of_mem h1)
            · exact Or.inr h1
      have hw : ∀ i, x l ≠ (s i : ℂ) := by
        intro i hi
        have := hpole l hlJ i
        rw [hxl] at hi
        rw [hi, sub_self, norm_zero] at this
        linarith
      have hdiff : DiffContOnCl ℂ (fun w => Dj κ ε s σ (update x l w)) (Metric.ball (c l) ρ) := by
        refine DifferentiableOn.diffContOnCl ?_
        rw [closure_ball _ hρ.ne']
        intro w hw'
        have hwd : ∀ i, w ≠ (s i : ℂ) := by
          intro i hi
          have h1 := hpole l hlJ i
          have h2 : ‖w - c l‖ ≤ ρ := by simpa [dist_eq_norm] using hw'
          rw [hi] at h2
          rw [norm_sub_rev] at h2
          linarith
        have hd := hasDerivAt_Dj κ ε s σ (update x l w) l hl (by simpa using hwd)
        have hfun : (fun w' => Dj κ ε s σ (update (update x l w) l w')) =
            (fun w' => Dj κ ε s σ (update x l w')) := by
          funext w'; rw [update_idem]
        rw [hfun] at hd
        simpa using hd.differentiableAt.differentiableWithinAt
      have hsph : ∀ w ∈ Metric.sphere (c l) ρ, ‖Dj κ ε s σ (update x l w)‖ ≤ B := by
        intro w hw'
        exact hall w (by simp [dist_eq_norm] at hw'; exact hw'.le)
      have hder := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdiff hsph
      rw [Dj_insert κ ε s σ x l hl hw, Finset.prod_insert hl]
      have hxσ : ‖Dj κ ε s σ x‖ ≤ B := by
        have := hall (x l) (by rw [hxl]; simp [hρ.le])
        simpa using this
      rw [hxl]
      calc ‖κ l * Dj κ ε s σ x + ε l * deriv (fun w => Dj κ ε s σ (update x l w)) (c l)‖
          ≤ ‖κ l‖ * ‖Dj κ ε s σ x‖ + ‖ε l‖ * ‖deriv (fun w => Dj κ ε s σ (update x l w)) (c l)‖ := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ ‖κ l‖ * B + ‖ε l‖ * (B / ρ) := by
            gcongr
        _ = (‖κ l‖ + ‖ε l‖ / ρ) * B := by ring
        _ = (‖κ l‖ + ‖ε l‖ / ρ) * (∏ l' ∈ σ, (‖κ l'‖ + ‖ε l'‖ / ρ)) * M := by rw [hB]; ring
  have := key J subset_rfl c (fun l hl hlJ => absurd hl hlJ) (fun l _ => rfl)
  exact this

/-! ### The Cauchy product against a reference -/

open CatalanLambda.Decay (cexpr)

/-- Without jets, `Dj` is the Cauchy determinant expression. -/
theorem Dj_empty_eq_cexpr (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (hs : Function.Injective s)
    (x : Fin k → ℂ) (hx : ∀ l i, x l ≠ (s i : ℂ)) :
    Dj κ ε s ∅ x = cexpr x (fun i => (s i : ℂ)) := by
  have hy : Function.Injective (fun i => (s i : ℂ)) := fun a b h => hs (Nat.cast_injective (R := ℂ) h)
  unfold Dj cexpr
  have := CatalanLambda.Decay.cauchy_det x (fun i => (s i : ℂ)) hy hx
  simp only [Finset.notMem_empty, if_false]
  rw [← this]
  congr 1
  ext l i
  simp [vr, one_div]

/-- **The ratio of two Cauchy expressions** (Lemma J, second half, pointwise).  `x` against a reference `x0`:
the numerator moves by the pair factors `P`, the denominator by the node factors `q`. -/
theorem norm_cexpr_le (x x0 : Fin k → ℂ) (s : Fin k → ℕ) (hs : Function.Injective s)
    (hx0 : Function.Injective x0) (hx0s : ∀ l i, x0 l ≠ (s i : ℂ)) (hxs : ∀ l i, x l ≠ (s i : ℂ))
    (P : Fin k → Fin k → ℝ) (hP0 : ∀ l l', 0 ≤ P l l')
    (hP : ∀ l l', l < l' → ‖x l' - x l‖ ≤ P l l' * ‖x0 l' - x0 l‖)
    (q : Fin k → Fin k → ℝ) (hq : ∀ l i, ‖x0 l - (s i : ℂ)‖ ≤ q l i * ‖x l - (s i : ℂ)‖) :
    ‖cexpr x (fun i => (s i : ℂ))‖ ≤
      (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') * (∏ l, ∏ i, q l i) * ‖cexpr x0 (fun i => (s i : ℂ))‖ := by
  unfold cexpr
  rw [norm_div, norm_div]
  have hNum : ‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x l' - x l) * ((s l : ℂ) - s l'))‖ ≤
      (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') *
        ‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x0 l' - x0 l) * ((s l : ℂ) - s l'))‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l _ => ?_)
    rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l' hl' => ?_)
    rw [Finset.mem_Ioi] at hl'
    rw [norm_mul, norm_mul]
    calc ‖x l' - x l‖ * ‖(s l : ℂ) - s l'‖ ≤ (P l l' * ‖x0 l' - x0 l‖) * ‖(s l : ℂ) - s l'‖ :=
          mul_le_mul_of_nonneg_right (hP l l' hl') (norm_nonneg _)
      _ = P l l' * (‖x0 l' - x0 l‖ * ‖(s l : ℂ) - s l'‖) := by ring
  have hDen : ‖∏ l, ∏ i, (x0 l - (s i : ℂ))‖ ≤ (∏ l, ∏ i, q l i) * ‖∏ l, ∏ i, (x l - (s i : ℂ))‖ := by
    rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun l _ => ?_)
    rw [norm_prod, norm_prod, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hq l i)
  have hDx0 : 0 < ‖∏ l, ∏ i, (x0 l - (s i : ℂ))‖ :=
    norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun l _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      sub_ne_zero.2 (hx0s l i))
  have hDx : 0 < ‖∏ l, ∏ i, (x l - (s i : ℂ))‖ :=
    norm_pos_iff.2 (Finset.prod_ne_zero_iff.2 fun l _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      sub_ne_zero.2 (hxs l i))
  have hq0 : 0 ≤ ∏ l, ∏ i, q l i := by
    have : 0 ≤ (∏ l, ∏ i, q l i) * ‖∏ l, ∏ i, (x l - (s i : ℂ))‖ := hDx0.le.trans hDen
    exact nonneg_of_mul_nonneg_left this hDx
  rw [div_le_iff₀ hDx]
  calc ‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x l' - x l) * ((s l : ℂ) - s l'))‖
      ≤ (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') *
        ‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x0 l' - x0 l) * ((s l : ℂ) - s l'))‖ := hNum
    _ = (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') *
        (‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x0 l' - x0 l) * ((s l : ℂ) - s l'))‖ /
          ‖∏ l, ∏ i, (x0 l - (s i : ℂ))‖ * ‖∏ l, ∏ i, (x0 l - (s i : ℂ))‖) := by
        rw [div_mul_cancel₀ _ hDx0.ne']
    _ ≤ (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') *
        (‖∏ l, ∏ l' ∈ Finset.Ioi l, ((x0 l' - x0 l) * ((s l : ℂ) - s l'))‖ /
          ‖∏ l, ∏ i, (x0 l - (s i : ℂ))‖ * ((∏ l, ∏ i, q l i) * ‖∏ l, ∏ i, (x l - (s i : ℂ))‖)) := by
        gcongr
        · exact Finset.prod_nonneg fun l _ => Finset.prod_nonneg fun l' _ => hP0 l l'
    _ = _ := by ring

/-! ### Lemma J, abstract form -/

/-- The polydisc: radius `ρ` around `c` in the variables of `J`, the other variables at their centres. -/
def InPoly (J : Finset (Fin k)) (c : Fin k → ℂ) (ρ : ℝ) (x : Fin k → ℂ) : Prop :=
  (∀ l ∈ J, ‖x l - c l‖ ≤ ρ) ∧ (∀ l, l ∉ J → x l = c l)

/-- The distortion exponent of Lemma J: `∑_{pairs not tight} (e_l + e_l′)/d_{ll′} + ∑_{l,i} e_l / m_{li}`,
`e_l = eJ` on `J`, `0` elsewhere, `d_{ll′} = ‖x⁰_{l′} - x⁰_l‖`. -/
noncomputable def jetExponent (J : Finset (Fin k)) (eJ : ℝ) (x0 : Fin k → ℂ) (m : Fin k → Fin k → ℝ)
    (Tt : Fin k → Fin k → Prop) [DecidableRel Tt] : ℝ :=
  (∑ l, ∑ l' ∈ Finset.Ioi l,
      if Tt l l' then 0 else ((if l ∈ J then eJ else 0) + (if l' ∈ J then eJ else 0)) / ‖x0 l' - x0 l‖) +
    ∑ l, ∑ i, (if l ∈ J then eJ else 0) / m l i

/-- **Lemma J (abstract form).**  The jetted determinant at the centres `c` is at most
`∏_{l∈J}(‖κ_l‖ + ‖ε_l‖/ρ) · exp(jetExponent) · ‖cexpr(x⁰, s)‖`, given: the reference `x⁰` is injective and away from
the nodes; the polydisc of `J` stays within `eJ` of the reference (`ρ + ‖c_l - x⁰_l‖ ≤ eJ`, and
`c = x⁰` off `J`); the nodes stay at least `m_{li}` from every polydisc point (and `ρ` from the centres); the
pairs flagged `Tt` do not move farther apart than at the reference. -/
theorem lemmaJ_abstract (κ ε : Fin k → ℂ) (s : Fin k → ℕ) (hs : Function.Injective s)
    (c x0 : Fin k → ℂ) (hx0 : Function.Injective x0) (hx0s : ∀ l i, x0 l ≠ (s i : ℂ))
    {ρ eJ : ℝ} (hρ : 0 < ρ) (heJ : 0 ≤ eJ) (J : Finset (Fin k))
    (hpole : ∀ l ∈ J, ∀ i, ρ < ‖c l - (s i : ℂ)‖)
    (hcJ : ∀ l ∈ J, ρ + ‖c l - x0 l‖ ≤ eJ) (hcn : ∀ l, l ∉ J → c l = x0 l)
    (m : Fin k → Fin k → ℝ) (hm : ∀ l i, 0 < m l i)
    (hnode : ∀ x, InPoly J c ρ x → ∀ l i, m l i ≤ ‖x l - (s i : ℂ)‖)
    (Tt : Fin k → Fin k → Prop) [DecidableRel Tt]
    (htight : ∀ l l', l < l' → Tt l l' → ∀ x, InPoly J c ρ x → ‖x l' - x l‖ ≤ ‖x0 l' - x0 l‖) :
    ‖Dj κ ε s J c‖ ≤ (∏ l ∈ J, (‖κ l‖ + ‖ε l‖ / ρ)) * Real.exp (jetExponent J eJ x0 m Tt) *
      ‖cexpr x0 (fun i => (s i : ℂ))‖ := by
  classical
  set e : Fin k → ℝ := fun l => if l ∈ J then eJ else 0 with he
  have he0 : ∀ l, 0 ≤ e l := fun l => by simp only [he]; split_ifs <;> simp [heJ]
  have hdist : ∀ x, InPoly J c ρ x → ∀ l, ‖x l - x0 l‖ ≤ e l := by
    intro x hx l
    by_cases hl : l ∈ J
    · simp only [he, if_pos hl]
      calc ‖x l - x0 l‖ = ‖(x l - c l) + (c l - x0 l)‖ := by ring_nf
        _ ≤ ‖x l - c l‖ + ‖c l - x0 l‖ := norm_add_le _ _
        _ ≤ ρ + ‖c l - x0 l‖ := by gcongr; exact hx.1 l hl
        _ ≤ eJ := hcJ l hl
    · simp only [he, if_neg hl]
      rw [hx.2 l hl, hcn l hl, sub_self, norm_zero]
  have hd0 : ∀ l l', l < l' → 0 < ‖x0 l' - x0 l‖ := fun l l' h =>
    norm_pos_iff.2 (sub_ne_zero.2 (fun hh => (ne_of_lt h) (hx0 hh).symm))
  have hnn : ∀ l l', 0 ≤ (if Tt l l' then (0 : ℝ) else (e l + e l') / ‖x0 l' - x0 l‖) := by
    intro l l'
    split_ifs
    · exact le_rfl
    · have := he0 l
      have := he0 l'
      positivity
  let P : Fin k → Fin k → ℝ := fun l l' =>
    1 + (if Tt l l' then 0 else (e l + e l') / ‖x0 l' - x0 l‖)
  let q : Fin k → Fin k → ℝ := fun l i => 1 + e l / m l i
  have hM : ∀ x : Fin k → ℂ, InPoly J c ρ x →
      ‖Dj κ ε s ∅ x‖ ≤ Real.exp (jetExponent J eJ x0 m Tt) * ‖cexpr x0 (fun i => (s i : ℂ))‖ := by
    intro x hx
    have hxs : ∀ l i, x l ≠ (s i : ℂ) := by
      intro l i h
      have := hnode x hx l i
      rw [h, sub_self, norm_zero] at this
      exact absurd this (not_le.2 (hm l i))
    rw [Dj_empty_eq_cexpr κ ε s hs x hxs]
    have hmain := norm_cexpr_le x x0 s hs hx0 hx0s hxs P
      (fun l l' => by
        have := hnn l l'
        simp only [P]; linarith)
      (fun l l' hll' => by
        simp only [P]
        by_cases ht : Tt l l'
        · rw [if_pos ht, add_zero, one_mul]
          exact htight l l' hll' ht x hx
        · rw [if_neg ht]
          have hd := hd0 l l' hll'
          have h1 : ‖x l' - x l‖ ≤ ‖x0 l' - x0 l‖ + e l' + e l := by
            calc ‖x l' - x l‖ = ‖(x0 l' - x0 l) + (x l' - x0 l') - (x l - x0 l)‖ := by ring_nf
              _ ≤ ‖(x0 l' - x0 l) + (x l' - x0 l')‖ + ‖x l - x0 l‖ := norm_sub_le _ _
              _ ≤ ‖x0 l' - x0 l‖ + ‖x l' - x0 l'‖ + ‖x l - x0 l‖ := by
                  gcongr
                  exact norm_add_le _ _
              _ ≤ ‖x0 l' - x0 l‖ + e l' + e l := by
                  gcongr
                  · exact hdist x hx l'
                  · exact hdist x hx l
          calc ‖x l' - x l‖ ≤ ‖x0 l' - x0 l‖ + e l' + e l := h1
            _ = (1 + (e l + e l') / ‖x0 l' - x0 l‖) * ‖x0 l' - x0 l‖ := by
                field_simp; ring)
      q (fun l i => by
        simp only [q]
        have hmi := hnode x hx l i
        have hmpos := hm l i
        have h1 : ‖x0 l - (s i : ℂ)‖ ≤ ‖x l - (s i : ℂ)‖ + e l := by
          calc ‖x0 l - (s i : ℂ)‖ = ‖(x l - (s i : ℂ)) - (x l - x0 l)‖ := by ring_nf
            _ ≤ ‖x l - (s i : ℂ)‖ + ‖x l - x0 l‖ := norm_sub_le _ _
            _ ≤ ‖x l - (s i : ℂ)‖ + e l := by gcongr; exact hdist x hx l
        have h2 : e l ≤ e l / m l i * ‖x l - (s i : ℂ)‖ := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hmpos]
          exact mul_le_mul_of_nonneg_left hmi (he0 l)
        nlinarith)
    have hP1 : (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') ≤ Real.exp
        (∑ l, ∑ l' ∈ Finset.Ioi l,
          if Tt l l' then 0 else (e l + e l') / ‖x0 l' - x0 l‖) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun l' _ => ?_) (fun l _ => ?_)
      · have := hnn l l'
        simp only [P]; linarith
      · rw [Real.exp_sum]
        refine Finset.prod_le_prod₀ (fun l' _ => ?_) (fun l' _ => ?_)
        · have := hnn l l'
          simp only [P]; linarith
        · simp only [P]
          rw [add_comm]
          exact Real.add_one_le_exp _
    have hP2 : (∏ l, ∏ i, q l i) ≤ Real.exp (∑ l, ∑ i, e l / m l i) := by
      rw [Real.exp_sum]
      refine Finset.prod_le_prod₀ (fun l _ => Finset.prod_nonneg fun i _ => ?_) (fun l _ => ?_)
      · have := he0 l
        have := hm l i
        simp only [q]; positivity
      · rw [Real.exp_sum]
        refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
        · have := he0 l
          have := hm l i
          simp only [q]; positivity
        · simp only [q]
          rw [add_comm]
          exact Real.add_one_le_exp _
    have hex : Real.exp (jetExponent J eJ x0 m Tt) =
        Real.exp (∑ l, ∑ l' ∈ Finset.Ioi l,
          if Tt l l' then 0 else (e l + e l') / ‖x0 l' - x0 l‖) *
        Real.exp (∑ l, ∑ i, e l / m l i) := by
      rw [← Real.exp_add]; rfl
    rw [hex]
    calc ‖cexpr x (fun i => (s i : ℂ))‖
        ≤ (∏ l, ∏ l' ∈ Finset.Ioi l, P l l') * (∏ l, ∏ i, q l i) *
          ‖cexpr x0 (fun i => (s i : ℂ))‖ := hmain
      _ ≤ (Real.exp (∑ l, ∑ l' ∈ Finset.Ioi l,
          if Tt l l' then 0 else (e l + e l') / ‖x0 l' - x0 l‖) *
          Real.exp (∑ l, ∑ i, e l / m l i)) * ‖cexpr x0 (fun i => (s i : ℂ))‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact mul_le_mul hP1 hP2
          (Finset.prod_nonneg fun l _ => Finset.prod_nonneg fun i _ => by
            have := he0 l
            have := hm l i
            simp only [q]; positivity)
          (Real.exp_nonneg _)
  have := norm_Dj_le κ ε s c hρ J hpole
    (M := Real.exp (jetExponent J eJ x0 m Tt) * ‖cexpr x0 (fun i => (s i : ℂ))‖)
    (fun x h1 h2 => hM x ⟨h1, h2⟩)
  calc ‖Dj κ ε s J c‖ ≤ _ := this
    _ = _ := by ring

/-! ### The two sum estimates of Lemma J (nodes and separated atoms) -/

/-- The harmonic sum of `k ≥ 1` terms: `∑_{m<k} 1/(m + a) ≤ 1/a + log ((k - 1 + a)/a)`. -/
theorem harmonic_shift_le {a : ℝ} (ha : 0 < a) : ∀ k : ℕ, 1 ≤ k →
    ∑ m ∈ Finset.range k, 1 / ((m : ℝ) + a) ≤ 1 / a + Real.log (((k : ℝ) - 1 + a) / a)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp
  | k + 2, _ => by
    have ih := harmonic_shift_le ha (k + 1) (by omega)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have e1 : (((k + 1 : ℕ) : ℝ) - 1 + a) = (k : ℝ) + a := by push_cast; ring
    have e2 : (((k + 2 : ℕ) : ℝ) - 1 + a) = (k : ℝ) + 1 + a := by push_cast; ring
    have e3 : ((k + 1 : ℕ) : ℝ) + a = (k : ℝ) + 1 + a := by push_cast; ring
    rw [e1] at ih
    rw [e2, Finset.sum_range_succ, e3]
    have h1 : 0 < (k : ℝ) + a := by linarith
    have h2 : 0 < (k : ℝ) + 1 + a := by linarith
    have hlog : 1 / ((k : ℝ) + 1 + a) ≤ Real.log (((k : ℝ) + 1 + a) / ((k : ℝ) + a)) := by
      have := Real.one_sub_inv_le_log_of_pos (x := ((k : ℝ) + 1 + a) / ((k : ℝ) + a)) (by positivity)
      have e : 1 - (((k : ℝ) + 1 + a) / ((k : ℝ) + a))⁻¹ = 1 / ((k : ℝ) + 1 + a) := by
        field_simp
        ring
      linarith
    have hsplit : Real.log (((k : ℝ) + 1 + a) / a) =
        Real.log (((k : ℝ) + a) / a) + Real.log (((k : ℝ) + 1 + a) / ((k : ℝ) + a)) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    linarith [hlog, hsplit, ih]

/-- Distinct naturals have a harmonic node sum: `∑_i 1/(s_i + a) ≤ ∑_{m<k} 1/(m + a)`. -/
theorem sum_inv_node_le {a : ℝ} (ha : 0 < a) (s : Fin k → ℕ) (hs : Function.Injective s) :
    ∑ i, 1 / ((s i : ℝ) + a) ≤ ∑ m ∈ Finset.range k, 1 / ((m : ℝ) + a) := by
  classical
  let r : Fin k → ℕ := fun i => (Finset.univ.filter fun j => s j < s i).card
  have hr_lt : ∀ i, r i < k := by
    intro i
    have : (Finset.univ.filter fun j => s j < s i).card < (Finset.univ : Finset (Fin k)).card := by
      apply Finset.card_lt_card
      refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
      have := h (Finset.mem_univ i)
      simp at this
    simpa using this
  have hr_le : ∀ i, r i ≤ s i := by
    intro i
    have h1 : ((Finset.univ.filter fun j => s j < s i).image s) ⊆ Finset.range (s i) := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 ht
      simpa using hj
    have h2 := Finset.card_le_card h1
    rw [Finset.card_image_of_injective _ hs, Finset.card_range] at h2
    exact h2
  have hr_inj : Function.Injective r := by
    intro i j hij
    by_contra hne
    rcases lt_trichotomy (s i) (s j) with h | h | h
    · have : (Finset.univ.filter fun l => s l < s i).card < (Finset.univ.filter fun l => s l < s j).card := by
        apply Finset.card_lt_card
        refine ⟨fun l hl => ?_, fun hh => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
          omega
        · have := hh (by simpa using h : i ∈ Finset.univ.filter fun l => s l < s j)
          simp at this
      exact absurd hij (ne_of_lt this)
    · exact hne (hs h)
    · have : (Finset.univ.filter fun l => s l < s j).card < (Finset.univ.filter fun l => s l < s i).card := by
        apply Finset.card_lt_card
        refine ⟨fun l hl => ?_, fun hh => ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
          omega
        · have := hh (by simpa using h : j ∈ Finset.univ.filter fun l => s l < s i)
          simp at this
      exact absurd hij (ne_of_gt this)
  calc ∑ i, 1 / ((s i : ℝ) + a) ≤ ∑ i, 1 / ((r i : ℝ) + a) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have : (r i : ℝ) ≤ s i := by exact_mod_cast hr_le i
        have h0 : (0 : ℝ) ≤ r i := Nat.cast_nonneg _
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
    _ = ∑ m ∈ Finset.univ.image r, 1 / ((m : ℝ) + a) :=
        (Finset.sum_image (f := fun m : ℕ => 1 / ((m : ℝ) + a)) (fun i _ j _ h => hr_inj h)).symm
    _ ≤ ∑ m ∈ Finset.range k, 1 / ((m : ℝ) + a) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
        intro m hm
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_range.2 (hr_lt i)

/-- **Separated points.**  If the points of `T` are pairwise at least `g` apart and all lie at least `g` to the
right of `a`, then `∑_{t∈T} 1/(t - a) ≤ (1/g) ∑_{j<|T|} 1/(j+1)`. -/
theorem sum_inv_sep_le {g : ℝ} (hg : 0 < g) (a : ℝ) (T : Finset ℝ)
    (hsep : ∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → g ≤ |t - t'|) (hnear : ∀ t ∈ T, a + g ≤ t) :
    ∑ t ∈ T, 1 / (t - a) ≤ (1 / g) * ∑ j ∈ Finset.range T.card, 1 / ((j : ℝ) + 1) := by
  classical
  have key : ∀ T : Finset ℝ, (∀ t ∈ T, ∀ t' ∈ T, t ≠ t' → g ≤ |t - t'|) → (∀ t ∈ T, a + g ≤ t) →
      (∑ t ∈ T, 1 / (t - a) ≤ (1 / g) * ∑ j ∈ Finset.range T.card, 1 / ((j : ℝ) + 1)) ∧
      (∀ m ∈ T, (∀ t ∈ T, t ≤ m) → a + T.card * g ≤ m) := by
    intro T
    induction T using Finset.induction_on_max with
    | empty => intro _ _; simp
    | insert x s hlt ih =>
      intro hsep hnear
      have hxs : x ∉ s := fun h => lt_irrefl _ (hlt x h)
      obtain ⟨ih1, ih2⟩ := ih (fun t ht t' ht' hne => hsep t (Finset.mem_insert_of_mem ht) t'
        (Finset.mem_insert_of_mem ht') hne) (fun t ht => hnear t (Finset.mem_insert_of_mem ht))
      have hx : a + (s.card + 1 : ℕ) * g ≤ x := by
        rcases s.eq_empty_or_nonempty with he | hne
        · subst he
          simpa using hnear x (Finset.mem_insert_self x _)
        · set m := s.max' hne
          have hm : m ∈ s := Finset.max'_mem s hne
          have h1 := ih2 m hm (fun t ht => Finset.le_max' s t ht)
          have h2 := hsep x (Finset.mem_insert_self x s) m (Finset.mem_insert_of_mem hm)
            (ne_of_gt (hlt m hm))
          rw [abs_of_pos (sub_pos.2 (hlt m hm))] at h2
          push_cast
          nlinarith
      refine ⟨?_, ?_⟩
      · rw [Finset.sum_insert hxs, Finset.card_insert_of_notMem hxs, Finset.sum_range_succ]
        have hpos : 0 < x - a := by
          have : (0 : ℝ) < ((s.card + 1 : ℕ) : ℝ) * g := by positivity
          linarith
        have h3 : 1 / (x - a) ≤ (1 / g) * (1 / ((s.card : ℝ) + 1)) := by
          have hc : g * ((s.card : ℝ) + 1) ≤ x - a := by push_cast at hx; nlinarith
          have e : (1 / g) * (1 / ((s.card : ℝ) + 1)) = 1 / (g * ((s.card : ℝ) + 1)) := by
            rw [one_div_mul_one_div]
          rw [e]
          exact one_div_le_one_div_of_le (by positivity) hc
        calc 1 / (x - a) + ∑ t ∈ s, 1 / (t - a)
            ≤ (1 / g) * (1 / ((s.card : ℝ) + 1)) +
              (1 / g) * ∑ j ∈ Finset.range s.card, 1 / ((j : ℝ) + 1) := by linarith
          _ = _ := by ring
      · intro m hm hmax
        rw [Finset.card_insert_of_notMem hxs]
        have hmx : m = x := by
          rcases Finset.mem_insert.1 hm with h | h
          · exact h
          · exact absurd (hmax x (Finset.mem_insert_self x s)) (not_le.2 (hlt m h))
        rw [hmx]
        push_cast at hx ⊢
        linarith
  exact (key T hsep hnear).1

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.Dj_insert
#print axioms CatalanCore.Uniform.Decay.Jet.norm_Dj_le
#print axioms CatalanCore.Uniform.Decay.Jet.norm_cexpr_le
#print axioms CatalanCore.Uniform.Decay.Jet.lemmaJ_abstract
#print axioms CatalanCore.Uniform.Decay.Jet.harmonic_shift_le
#print axioms CatalanCore.Uniform.Decay.Jet.sum_inv_node_le
#print axioms CatalanCore.Uniform.Decay.Jet.sum_inv_sep_le
