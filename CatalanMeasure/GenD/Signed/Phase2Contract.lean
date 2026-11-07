module

public import CatalanMeasure.GenD.Signed.MarkedCap
public import CatalanMeasure.GenD.Signed.Brackets
public import CatalanMeasure.GenD.Analytic.MarkedSecond
public import CatalanMeasure.GenD.Signed.RealPlace

/-!
# Phase 2 contract: the complete `SignedNearBounds` from endpoint data

`Phase2Data I` bundles exactly the data a Phase 2 data module supplies for `I` α-intervals:
the two endpoint trial families `DA i`, `DB i` at `αA i < αB i`, the endpoint suprema of the row,
column and FIXED-ROW fields (`fNegM`, `fPosMS`, `fPosMR`, `fNearMS`), the endpoint constants and
curvature, the dual chord `zb`, the cap constants (`CapEnd`) and the two budget inequalities.
`Phase2Data.toBounds` assembles the contract of `EnergyNear` from

* `SignedNearBounds.ofEnds` (Theorem M) for `e_mem, v_summable, R_geom, t_geom, reference, rowNeg,
  rowPos, column, const_le, budgetFix`;
* `fixedSum_ends` (below), the endpoint form of `fixedSumAt_of_cap` (Theorem S with the top cap):
  the fixed-row fields are exactly affine in the interpolation weight (`fNegM_interp`, ...), so
  endpoint suprema suffice; `ZB := zbCap` of the chord cap data;
* `spikeFix_of_ends` (Theorem SE) for `spikeFix`.

`Phase2Data.signedSecondSheetNear` is the end-to-end corollary: `SignedSecondSheetCore` for the
sheet, given the identification of the data with the sheet's problem data.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Filter OAI.InternalCatalan

noncomputable section

/-! ### 1. Elementary mixing -/

theorem mix_le {l a b A B ε : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ A + ε) (hb : b ≤ B + ε) :
    (1 - l) * a + l * b ≤ ((1 - l) * A + l * B) + ε := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_le_const {l a b M : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : a ≤ M) (hb : b ≤ M) :
    (1 - l) * a + l * b ≤ M := by
  nlinarith [mul_le_mul_of_nonneg_left ha (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hb h0]

theorem mix_nonneg {l a b : ℝ} (h0 : 0 ≤ l) (h1 : l ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ (1 - l) * a + l * b :=
  add_nonneg (mul_nonneg (sub_nonneg.2 h1) ha) (mul_nonneg h0 hb)

theorem abs_le_one_of_Ioo {x a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (hx : x ∈ Ioo a b) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-! ### 2. The cap data at the two endpoints and its chord -/

/-- The σ-cap data of one α-interval at its two endpoint trials `A`, `B`: the node threshold `gs`,
the top-cell start `xc`, the cap density `C1`, the off-top bounds `lam*` and the top-cell constants
`g*` of the fixed-row fields of each endpoint, the log coefficients `rSA, rSB` of the near field
and `rP` of the positive field (the latter is not interpolated: it only has to dominate
`rc α`). -/
structure CapEnd where
  gs : ℝ
  xc : ℝ
  C1 : ℝ
  lamNA : ℝ
  lamNB : ℝ
  lamPA : ℝ → ℝ
  lamPB : ℝ → ℝ
  gPA : ℝ → ℝ
  gPB : ℝ → ℝ
  rP : ℝ → ℝ
  lamSA : ℝ → ℝ → ℝ
  lamSB : ℝ → ℝ → ℝ
  gSA : ℝ → ℝ → ℝ
  gSB : ℝ → ℝ → ℝ
  rSA : ℝ → ℝ → ℝ
  rSB : ℝ → ℝ → ℝ

/-! ### 3. `fixedSum` of one interval from endpoint data -/

/-! ### 4. The complete Phase 2 data and the contract -/

/-! ### Admissibility of the actual marked nodes -/

/-! `MarkedCap` (the cap of the actual marked rows) is defined in `MarkedCap.lean`. -/

theorem count_sub_le {m a : ℕ} (y : Fin m → ℝ) (f : Fin a → Fin m) (hf : Function.Injective f)
    (j : Fin a) :
    (Finset.univ.filter (fun i => y (f j) ≤ y (f i))).card ≤
      (Finset.univ.filter (fun i => y (f j) ≤ y i)).card := by
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    simpa using hi
  · exact hf.injOn

/-! ### 5. The end-to-end corollary -/

section Sheet

open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic

end Sheet


/-! ### Spike witnesses from per-trial certificates (`spikeWitness_of_cert`)

`SpikeTrialCert D m ρ Kn Tn` is the per-trial, per-`m` data: finitely many real (in practice
rational) constants and inequalities that do not depend on the configuration.  `Kn` bounds the
number of negative rows, `Tn` the total number of rows plus one. -/

/-! ### 6. The class link `hlink` for `nearOptCls`: counting, free facts, statistics

Everything here is about the free rows `z` of a configuration in `nearOptCls` (the old-route
violation) and the marked rows `y`.  The factor-free old (532) trial `D0 : SecondTrialBoundsEnd P 0` is the reference:
near-optimality gives the field bracket and the cosine square of the free rows at most
`excess ..` (`free_facts`), hence counts of free rows in any region where the free field is below
its cap (`card_region_le`) and one-sided linear statistics (`stat_poly_ge`).  -/

section HL

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

theorem card_filter_append {a b : ℕ} (u : Fin a → ℝ) (v : Fin b → ℝ) (P : ℝ → Prop)
    [DecidablePred P] :
    (Finset.univ.filter (fun i => P (Fin.append u v i))).card =
      (Finset.univ.filter (fun i => P (u i))).card +
        (Finset.univ.filter (fun i => P (v i))).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

/-- **Top count of the marked rows** (`MarkedCap`, `nodeCap_gap`): the rows above `1 - θ` number at
most `C1 n θ + 1`, from the cap `#{i : y_j ≤ y_i} ≤ C1 n (1 - y_j) + 1` at the lowest such row. -/
theorem top_count_le {m : ℕ} (y : Fin m → ℝ) {xc C1 n θ : ℝ}
    (h : ∀ j, xc ≤ y j →
      ((Finset.univ.filter (fun i => y j ≤ y i)).card : ℝ) ≤ C1 * n * (1 - y j) + 1)
    (hxc : xc ≤ 1 - θ) (hθ : 0 ≤ θ) (hC : 0 ≤ C1) (hn : 0 ≤ n) :
    ((Finset.univ.filter (fun i => 1 - θ < y i)).card : ℝ) ≤ C1 * n * θ + 1 := by
  classical
  set S := Finset.univ.filter (fun i => 1 - θ < y i) with hS
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    nlinarith [mul_nonneg (mul_nonneg hC hn) hθ]
  · obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image S y hne
    have hj0' : 1 - θ < y j0 := (Finset.mem_filter.1 hj0).2
    have hsub : S ⊆ Finset.univ.filter (fun i => y j0 ≤ y i) := fun i hi =>
      Finset.mem_filter.2 ⟨Finset.mem_univ _, hmin i hi⟩
    have h1 := h j0 (by linarith)
    have h2 : (S.card : ℝ) ≤ ((Finset.univ.filter (fun i => y j0 ≤ y i)).card : ℝ) :=
      Nat.cast_le.2 (Finset.card_le_card hsub)
    have h3 : C1 * n * (1 - y j0) ≤ C1 * n * θ :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hn)
    linarith

/-- A sum over the nodes of a sign split, bounded sign by sign. -/
theorem sum_sign_le {p k q : ℕ} (σ : Fin k ⊕ Fin q ≃ Fin p) (x : Fin p → ℝ) (f : ℝ → ℝ)
    {a b : ℝ} (h1 : ∀ i, f (x (σ (Sum.inl i))) ≤ a) (h2 : ∀ i, f (x (σ (Sum.inr i))) ≤ b) :
    ∑ i, f (x i) ≤ k * a + q * b := by
  rw [← Equiv.sum_comp σ (fun i => f (x i)), Fintype.sum_sum_type]
  have e1 : ∑ i : Fin k, f (x (σ (Sum.inl i))) ≤ k * a :=
    calc _ ≤ ∑ _i : Fin k, a := Finset.sum_le_sum fun i _ => h1 i
      _ = k * a := by simp
  have e2 : ∑ i : Fin q, f (x (σ (Sum.inr i))) ≤ q * b :=
    calc _ ≤ ∑ _i : Fin q, b := Finset.sum_le_sum fun i _ => h2 i
      _ = q * b := by simp
  linarith

/-! #### Free facts of a near-optimal class member -/

theorem groupedSquares_ge_free {ν e : ℝ} (hν : 0 < ν) (he : e ∈ Ioo (0 : ℝ) (1 / 8))
    {a b r : ℕ} {x : Fin a → ℝ} {y : Fin b → ℝ} (z s : Fin r → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hy : ∀ i, y i ∈ Ioo (-1 : ℝ) 1)
    (u v w : ℕ → ℝ) (hu : Summable (fun k => |u k|)) :
    sqTail v (pinCosineMoment ν e z) ≤ groupedSquares ν e u v w x y z s := by
  have h1 := (cosineSquares_nonneg hν he hx hy u hu).2
  have h3 := sqTail_nonneg w (fun j => pinPowerMoment ν e z j - 2 * pinColumnMoment ν e s j)
  unfold groupedSquares freeSquares
  linarith only [h1, h3]

/-- The factor-free second-population trial from an old one, at a free output target `target'`
and marked-fraction threshold `α1` (only the budget field mentions either). -/
def _root_.CatalanMeasure.GenD.Analytic.SecondTrialBounds.toEndAt {P : Parameters}
    {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G)
    {α1 target' : ℝ} (cost' : ℝ)
    (hbud : ∀ {a t : ℝ}, α1 ≤ a → 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        D.normCap + (1 - a) * D.fieldCap + (a - t) * residual + t * nearCap ≤
          -target' + Real.log 2 / 2 + cost' * a) :
    SecondTrialBoundsEnd P α1 target' residual nearCap cost' G where
  p := D.p
  v := D.v
  MX := D.MX
  MY := D.MY
  normCap := D.normCap
  fieldCap := D.fieldCap
  p_summable := D.p_summable
  v_summable := D.v_summable
  norm_le := D.norm_le
  field_sum := D.field_sum
  row := D.row
  column := D.column
  marked := D.marked
  near := D.near
  budget := hbud

/-- The factor-free (endpoint column field) old-route trial from an old-route trial and an endpoint
budget without `a (1 - a) log 2` (for K590: `K590.second_budget'_log2`, cost `secondCost'`): the
instance `α1 = 0`, original target, of `toEndAt`. -/
def SecondTrialBounds.toEnd {P : Parameters} {target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBounds P target residual nearCap cost G) (cost' : ℝ)
    (hbud : ∀ {a t : ℝ}, 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        D.normCap + (1 - a) * D.fieldCap + (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost' * a) :
    SecondTrialBoundsEnd P 0 target residual nearCap cost' G :=
  D.toEndAt (α1 := 0) (target' := target) cost' (fun _ ha ht => hbud ha ht)

set_option maxHeartbeats 1600000 in
/-- The physical column field is the endpoint column field plus `α log (1 + s)`
(`Analytic.grouped_value_physical_eq`, restated here). -/
theorem grouped_value_phys_end {P : Parameters} {N r a b : ℕ}
    (z : Fin r → ℝ) (x : Fin a → ℝ) (y : Fin b → ℝ) (s : Fin r → ℝ) :
    groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationPhysicalColumnField P N (a + b)) z x y s =
      groupedValueWithFields (P.n N : ℝ) (groupedConstant P N r a b)
        (populationPhysicalFreeField P N) (groupedMarkedField P N)
        (groupedNearField P N) (populationEndpointColumnField P N 0) z x y s +
      ((((a + b : ℕ) : ℝ) / (P.n N : ℝ)) * ∑ i, Real.log (1 + s i)) / (P.n N : ℝ) :=
  CatalanMeasure.GenD.Analytic.grouped_value_physical_eq z x y s

set_option maxHeartbeats 1600000 in
end HL

section HL2

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- Counting: the free rows in a region where the free field is `d` below its cap number at most
`ν Δ / d` (Chebyshev inequality for the bracket). -/
theorem card_region_le {ν cap d Δ : ℝ} (hν : 0 < ν) {p : ℕ} (X : Fin p → ℝ)
    (S : Finset (Fin p)) (hX : ∀ i, X i ≤ cap) (hS : ∀ i ∈ S, X i ≤ cap - d)
    (hb : bracketSlack ν cap X ≤ Δ) : (S.card : ℝ) * d ≤ ν * Δ :=
  (card_mul_le_bracket hν X S hX hS).trans (mul_le_mul_of_nonneg_left hb hν.le)

/-- The Chebyshev polynomial `c0 + Σ_{k<K} G_k τ^{k+1} T_{k+1}(x)` of a certificate; `τ = 1 - e`
is the damping of the cosine moments `pinCosineMoment`. -/
def evalCert (e : ℝ) (K : ℕ) (G : ℕ → ℝ) (c0 x : ℝ) : ℝ :=
  c0 + ∑ k ∈ Finset.range K,
    G k * (realEnergyTau e ^ (k + 1) * (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x)

/-- `H = Σ_{k<K} G_k² (k+1)`: the dual norm of the certificate. -/
def certH (K : ℕ) (G : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range K, G k ^ 2 * ((k : ℝ) + 1)

/-- `Σ_{k<K} G_k p_{k+1}`: the value of the certificate on the trial. -/
def certMean (K : ℕ) (G : ℕ → ℝ) (pp : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range K, G k * pp (k + 1)

end HL2

section HL3

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- A one-sided Chebyshev-polynomial certificate: the polynomial `evalCert e K G c0`. -/
structure PolyCert where
  K : ℕ
  G : ℕ → ℝ
  c0 : ℝ

theorem certH_nonneg (K : ℕ) (G : ℕ → ℝ) : 0 ≤ certH K G :=
  Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (by positivity)

theorem sqrt_certH_le {K : ℕ} {G : ℕ → ℝ} {Δ Dtop s : ℝ} (hΔ : Δ ≤ Dtop) (hs : 0 ≤ s)
    (h : certH K G * Dtop ≤ s ^ 2) : Real.sqrt (certH K G * Δ) ≤ s :=
  Real.sqrt_le_iff.mpr ⟨hs, (mul_le_mul_of_nonneg_left hΔ (certH_nonneg K G)).trans h⟩

/-- `1 - k_t(x) ≥ 0` for `t > 0`. -/
theorem one_sub_slopeKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 ≤ 1 - slopeKernel t x := by
  unfold slopeKernel
  have hd : 0 < t ^ 2 + x ^ 2 := by positivity
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) = 1 - x ^ 2 / (t ^ 2 + x ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  have h3 : 0 ≤ x ^ 2 / (t ^ 2 + x ^ 2) := by positivity
  linarith

/-- For small `t` and a node away from the origin, `1 - k_t(x) ≥ a²/(ts² + a²)`. -/
theorem one_sub_slopeKernel_ge_small {t x a ts : ℝ} (ht : 0 < t) (hts : t ≤ ts) (ha : 0 < a)
    (hx : a ≤ |x|) : a ^ 2 / (ts ^ 2 + a ^ 2) ≤ 1 - slopeKernel t x := by
  unfold slopeKernel
  have ht2 : t ^ 2 ≤ ts ^ 2 := by nlinarith
  have hx2 : a ^ 2 ≤ x ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg x]) hx
    simpa using this
  have hd : 0 < t ^ 2 + x ^ 2 := by positivity
  have hts0 : 0 < ts := lt_of_lt_of_le ht hts
  have h1 : t ^ 2 / (t ^ 2 + x ^ 2) = 1 - x ^ 2 / (t ^ 2 + x ^ 2) := by
    field_simp; ring
  have h2 : 0 ≤ x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) := by positivity
  have h3 : a ^ 2 / (ts ^ 2 + a ^ 2) ≤ x ^ 2 / (t ^ 2 + x ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) hd]
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.2 ht2), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hx2),
      mul_nonneg (sub_nonneg.2 hx2) (sub_nonneg.2 ht2), sq_nonneg a, sq_nonneg ts]
  linarith

/-- **`k_t(x)` is Lipschitz in `t` on `t ≥ a`**, with constant `1/a`, uniformly in `x`. -/
theorem slopeKernel_lip {x t s a : ℝ} (ha : 0 < a) (ht : a ≤ t) (hs : a ≤ s) :
    |slopeKernel t x - slopeKernel s x| ≤ |t - s| / a := by
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hs0 : 0 < s := lt_of_lt_of_le ha hs
  have hts : 2 * a ≤ t + s := by linarith
  -- the first term
  have hg : |t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)| ≤ |t - s| / (2 * a) := by
    have hd1 : 0 < t ^ 2 + x ^ 2 := by positivity
    have hd2 : 0 < s ^ 2 + x ^ 2 := by positivity
    rw [div_sub_div _ _ hd1.ne' hd2.ne']
    have hnum : t ^ 2 * (s ^ 2 + x ^ 2) - (t ^ 2 + x ^ 2) * s ^ 2 =
        x ^ 2 * (t - s) * (t + s) := by ring
    rw [hnum, abs_div, abs_of_pos (mul_pos hd1 hd2), abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by linarith : 0 < t + s), div_le_div_iff₀ (mul_pos hd1 hd2) (by positivity)]
    have hden : 2 * a * (x ^ 2 * (t + s)) ≤ (t ^ 2 + x ^ 2) * (s ^ 2 + x ^ 2) := by
      nlinarith [sq_nonneg (t * s - x ^ 2), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hts),
        mul_nonneg (sq_nonneg x) (sq_nonneg (t + s)), sq_nonneg x]
    have := mul_le_mul_of_nonneg_left hden (abs_nonneg (t - s))
    nlinarith [this, abs_nonneg (t - s), sq_nonneg x]
  have hh : |x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)| ≤
      |t - s| / (2 * a) := by
    have hd1 : 0 < 1 + x ^ 2 * t ^ 2 := by positivity
    have hd2 : 0 < 1 + x ^ 2 * s ^ 2 := by positivity
    rw [div_sub_div _ _ hd1.ne' hd2.ne']
    have hnum : x ^ 2 * t ^ 2 * (1 + x ^ 2 * s ^ 2) - (1 + x ^ 2 * t ^ 2) * (x ^ 2 * s ^ 2) =
        x ^ 2 * (t - s) * (t + s) := by ring
    rw [hnum, abs_div, abs_of_pos (mul_pos hd1 hd2), abs_mul, abs_mul, abs_of_nonneg (sq_nonneg x),
      abs_of_pos (by linarith : 0 < t + s), div_le_div_iff₀ (mul_pos hd1 hd2) (by positivity)]
    have hden : 2 * a * (x ^ 2 * (t + s)) ≤ (1 + x ^ 2 * t ^ 2) * (1 + x ^ 2 * s ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 * t * s - 1), mul_nonneg (sq_nonneg x) (sub_nonneg.2 hts),
        mul_nonneg (sq_nonneg x) (sq_nonneg (t + s)), sq_nonneg x]
    have := mul_le_mul_of_nonneg_left hden (abs_nonneg (t - s))
    nlinarith [this, abs_nonneg (t - s), sq_nonneg x]
  unfold slopeKernel
  have hsplit : t ^ 2 / (t ^ 2 + x ^ 2) - x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) -
      (s ^ 2 / (s ^ 2 + x ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)) =
      (t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)) -
        (x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)) := by ring
  rw [hsplit]
  calc _ ≤ |t ^ 2 / (t ^ 2 + x ^ 2) - s ^ 2 / (s ^ 2 + x ^ 2)| +
        |x ^ 2 * t ^ 2 / (1 + x ^ 2 * t ^ 2) - x ^ 2 * s ^ 2 / (1 + x ^ 2 * s ^ 2)| := abs_sub _ _
    _ ≤ |t - s| / (2 * a) + |t - s| / (2 * a) := add_le_add hg hh
    _ = |t - s| / a := by field_simp; ring

end HL3

section HL4

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

theorem g_bound {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 2 ≤ N) :
    2 * P.g N + 2 ≤ P.n N := by
  have h := Nat.mul_le_mul_right N (show 2 * P.g0 + 1 ≤ P.n0 from hP.2.2.2.2)
  simp only [Parameters.g, Parameters.n]
  nlinarith [h]

end HL4

section HL5

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

/-- The canonical class predicate `Clsf` (what `hCls_of_cert` needs): ranges, row counts, and the
spike count of the positives `≤ Mmax N` for every endpoint trial's `θ`. -/
def ClsfCanon {I : ℕ} (θ : Fin I → ℕ → ℝ) (sr gc : Fin I → ℕ → ℕ) (nu : Fin I → ℕ → ℝ)
    (Kn Tn : ℕ → ℝ) (Mmax : ℕ → ℕ) (N k q m1 m2 : ℕ)
    (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) : Prop :=
  (∀ b, Fin.append xn yn b ∈ Ioo (-1 : ℝ) 0) ∧ (∀ p, Fin.append gp yp p ∈ Ioo (0 : ℝ) 1) ∧
    (((k + m1 : ℕ)) : ℝ) ≤ Kn N ∧ ((k + m1 + (q + m2) + 1 : ℕ) : ℝ) ≤ Tn N ∧
    (∀ i, (Finset.univ.filter (fun p => 1 - θ i N < Fin.append gp yp p)).card ≤ Mmax N) ∧
    ∀ i, 0 < sr i N ∧ sr i N + gc i N ≤ q + m2 ∧ ((q + m2 : ℕ) : ℝ) ≤ nu i N

theorem card_spike_mono {n : ℕ} (v : Fin n → ℝ) {θ θ0 : ℝ} (h : θ ≤ θ0) :
    (Finset.univ.filter (fun i => 1 - θ < v i)).card ≤
      (Finset.univ.filter (fun i => 1 - θ0 < v i)).card :=
  Finset.card_le_card (fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    linarith)

end HL5

section HL6

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

set_option maxHeartbeats 1600000 in
end HL6

section HL7

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.Parametric
  OAI.InternalCatalan

end HL7

/-! ### Independent negative-gap near-sheet bridge (eventual node cap)

The original symmetric theorems above retain their explicit types. Their shared
Phase2 record and SignedNearBounds assembly are reused. The new node route needs
only an eventual cap, so it never asserts the N>=10 result at smaller N.
-/
open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan
set_option maxHeartbeats 1600000 in
end

end CatalanMeasure.Signed


#print axioms CatalanMeasure.Signed.top_count_le
#print axioms CatalanMeasure.Signed.slopeKernel_lip






