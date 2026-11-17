module

public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import CatalanCore.Uniform.Decay.Polygon.Deform
public import CatalanCore.Decay.ComplexEnergy
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-!
# Weighted curve families and the logarithmic potential (Lai decay, LD09)

Finite families of weighted curves as one measure space (`listMeasure`), pieces of a polygon,
one-dimensional integral bounds, and the potential `potC` of a finite measure: measurability,
a lower bound for square-root-majorised measures, upper semicontinuity.
-/



open MeasureTheory Set Real Filter Topology Finset

namespace CatalanCore.Decay.CurveFamily

/-- The measure space of a finite family of weighted curves: `Fin N × ℝ` with the measure
`∑ᵢ (νᵢ pushed to {i} × ℝ)`. -/
noncomputable def famMeasure {N : ℕ} (ν : Fin N → Measure ℝ) : Measure (Fin N × ℝ) :=
  Measure.sum fun i => (ν i).map (Prod.mk i)

theorem sigmaFinite_finset_sum' {ι α : Type*} [MeasurableSpace α] (μ : ι → Measure α)
    [∀ i, SigmaFinite (μ i)] (s : Finset ι) : SigmaFinite (∑ i ∈ s, μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    haveI := ih
    infer_instance

instance famMeasure_sigmaFinite {N : ℕ} (ν : Fin N → Measure ℝ) [∀ i, SigmaFinite (ν i)] :
    SigmaFinite (famMeasure ν) := by
  unfold famMeasure
  rw [Measure.sum_fintype]
  haveI : ∀ i, SigmaFinite ((ν i).map (Prod.mk i)) := fun i =>
    (measurableEmbedding_prodMk_left i).sigmaFinite_map
  exact sigmaFinite_finset_sum' _ _

theorem integrable_fam_iff {N : ℕ} (ν : Fin N → Measure ℝ) {E : Type*} [NormedAddCommGroup E]
    {F : Fin N × ℝ → E} :
    Integrable F (famMeasure ν) ↔ ∀ i, Integrable (fun t => F (i, t)) (ν i) := by
  unfold famMeasure
  rw [integrable_sum_measure_iff]
  constructor
  · rintro ⟨h, -⟩ i
    exact ((measurableEmbedding_prodMk_left i).integrable_map_iff).mp (h i)
  · intro h
    refine ⟨fun i => ((measurableEmbedding_prodMk_left i).integrable_map_iff).mpr (h i), ?_⟩
    exact Summable.of_finite

theorem integral_fam {N : ℕ} (ν : Fin N → Measure ℝ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Fin N × ℝ → E} (hF : Integrable F (famMeasure ν)) :
    ∫ x, F x ∂famMeasure ν = ∑ i, ∫ t, F (i, t) ∂ν i := by
  unfold famMeasure
  rw [integral_sum_measure (by unfold famMeasure at hF; exact hF), tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (measurableEmbedding_prodMk_left i).integral_map _

/-! ### Pieces of a polygon and curve families -/

/-- A straight piece `t ↦ a + t D`: a finite segment (`t ∈ (0, 1]`) or a ray (`t ∈ (0, ∞)`). -/
structure Piece where
  a : ℂ
  D : ℂ
  ray : Bool

namespace Piece

/-- The parametrisation `t ↦ a + t D`. -/
def zeta (p : Piece) (t : ℝ) : ℂ := p.a + (t : ℂ) * p.D

/-- The parameter measure. -/
noncomputable def nu (p : Piece) : Measure ℝ :=
  if p.ray then volume.restrict (Ioi (0 : ℝ)) else volume.restrict (Ioc (0 : ℝ) 1)

/-- Complex conjugation of a piece. -/
def conj (p : Piece) : Piece := ⟨starRingEnd ℂ p.a, starRingEnd ℂ p.D, p.ray⟩

instance (p : Piece) : SigmaFinite p.nu := by
  unfold nu
  split_ifs <;> infer_instance

theorem zeta_conj (p : Piece) (t : ℝ) : p.conj.zeta t = starRingEnd ℂ (p.zeta t) := by
  simp [conj, zeta]

end Piece

/-- The pieces of the chain `l₀ → l₁ → ⋯`. -/
def chainPieces : List ℂ → List Piece
  | [] => []
  | [_] => []
  | a :: b :: rest => ⟨a, b - a, false⟩ :: chainPieces (b :: rest)

/-- The pieces of a polygon: the chain and the final ray. -/
def polyPieces (vs : List ℂ) (hne : vs ≠ []) (d : ℂ) : List Piece :=
  chainPieces vs ++ [⟨vs.getLast hne, d, true⟩]

theorem segI_eq_Ioc (f : ℂ → ℂ) (a b : ℂ) :
    CatalanCore.Uniform.Decay.Polygon.segI f a b =
      ∫ t, f (a + (t : ℂ) * (b - a)) * (b - a) ∂(volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [CatalanCore.Uniform.Decay.Polygon.segI_eq, intervalIntegral.integral_of_le zero_le_one]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [AffineMap.lineMap_apply, Complex.real_smul]
  left
  ring_nf

theorem chainI_eq_sum (f : ℂ → ℂ) :
    ∀ l : List ℂ, CatalanCore.Uniform.Decay.Polygon.chainI f l =
      ((chainPieces l).map fun p => ∫ t, f (p.zeta t) * p.D ∂p.nu).sum
  | [] => by simp [CatalanCore.Uniform.Decay.Polygon.chainI, chainPieces]
  | [a] => by simp [CatalanCore.Uniform.Decay.Polygon.chainI, chainPieces]
  | a :: b :: rest => by
    rw [CatalanCore.Uniform.Decay.Polygon.chainI_cons_cons, chainI_eq_sum f (b :: rest)]
    simp only [chainPieces, List.map_cons, List.sum_cons]
    congr 1
    rw [segI_eq_Ioc]
    simp [Piece.nu, Piece.zeta]

theorem polyI_eq_sum (f : ℂ → ℂ) (v : ℂ) (pts : List ℂ) (d : ℂ) :
    CatalanCore.Uniform.Decay.Polygon.polyI f v pts d =
      ((polyPieces (v :: pts) (List.cons_ne_nil _ _) d).map
        fun p => ∫ t, f (p.zeta t) * p.D ∂p.nu).sum := by
  unfold CatalanCore.Uniform.Decay.Polygon.polyI polyPieces
  rw [chainI_eq_sum, List.map_append, List.sum_append]
  congr 1
  simp [CatalanCore.Uniform.Decay.Polygon.rayInt, Piece.nu, Piece.zeta]

/-- A weighted curve: a point map `ζ`, a complex weight `w`, a parameter measure `ν`. -/
structure Curve where
  ζ : ℝ → ℂ
  w : ℝ → ℂ
  ν : Measure ℝ

/-- The curve of a piece with weight `κ ρ(ζ) D`. -/
noncomputable def Curve.ofPiece (κ : ℂ) (ρ : ℂ → ℂ) (p : Piece) : Curve :=
  ⟨p.zeta, fun t => κ * ρ (p.zeta t) * p.D, p.nu⟩

/-- An atom of mass `α` at `z`. -/
noncomputable def Curve.atom (z α : ℂ) : Curve := ⟨fun _ => z, fun _ => α, Measure.dirac 0⟩

/-- The measure of a list of curves. -/
noncomputable def listMeasure (cs : List Curve) : Measure (Fin cs.length × ℝ) :=
  famMeasure fun i => (cs.get i).ν

/-- The weight function on the family space. -/
def listW (cs : List Curve) (x : Fin cs.length × ℝ) : ℂ := (cs.get x.1).w x.2

/-- The point map on the family space. -/
def listZ (cs : List Curve) (x : Fin cs.length × ℝ) : ℂ := (cs.get x.1).ζ x.2

theorem listMeasure_sigmaFinite (cs : List Curve) (h : ∀ c ∈ cs, SigmaFinite c.ν) :
    SigmaFinite (listMeasure cs) := by
  haveI : ∀ i, SigmaFinite ((cs.get i).ν) := fun i => h _ (List.get_mem _ _)
  unfold listMeasure
  infer_instance

theorem integrable_list_iff {E : Type*} [NormedAddCommGroup E] (cs : List Curve) (g : ℂ → ℂ → E) :
    Integrable (fun x => g (listW cs x) (listZ cs x)) (listMeasure cs) ↔
      ∀ c ∈ cs, Integrable (fun t => g (c.w t) (c.ζ t)) c.ν := by
  unfold listMeasure
  rw [integrable_fam_iff]
  constructor
  · intro h c hc
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact h i
  · intro h i
    exact h _ (List.get_mem _ _)

theorem integral_list {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (cs : List Curve)
    (g : ℂ → ℂ → E)
    (hg : Integrable (fun x => g (listW cs x) (listZ cs x)) (listMeasure cs)) :
    ∫ x, g (listW cs x) (listZ cs x) ∂listMeasure cs =
      (cs.map fun c => ∫ t, g (c.w t) (c.ζ t) ∂c.ν).sum := by
  unfold listMeasure at hg ⊢
  rw [integral_fam _ hg]
  exact Fin.sum_univ_fun_getElem cs (fun c => ∫ t, g (c.w t) (c.ζ t) ∂c.ν)

/-! ### One-dimensional integral bounds -/

theorem integral_Ioc_le {F : ℝ → ℝ} {M : ℝ} (hF : Integrable F (volume.restrict (Ioc (0 : ℝ) 1)))
    (h : ∀ t ∈ Ioc (0 : ℝ) 1, F t ≤ M) : ∫ t, F t ∂(volume.restrict (Ioc (0 : ℝ) 1)) ≤ M := by
  have h1 : IntegrableOn (fun _ : ℝ => M) (Ioc (0 : ℝ) 1) := integrableOn_const (by simp)
  have := setIntegral_mono_on hF h1 measurableSet_Ioc h
  simpa using this

theorem integral_Ioi_le {F : ℝ → ℝ} {M μ : ℝ} (hμ : 0 < μ)
    (hF : Integrable F (volume.restrict (Ioi (0 : ℝ))))
    (h : ∀ t ∈ Ioi (0 : ℝ), F t ≤ M * Real.exp (-μ * t)) :
    ∫ t, F t ∂(volume.restrict (Ioi (0 : ℝ))) ≤ M / μ := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-μ * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -μ < 0) 0).const_mul M
  have := setIntegral_mono_on hF hint measurableSet_Ioi h
  have h2 : ∫ t in Ioi (0 : ℝ), M * Real.exp (-μ * t) = M / μ := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -μ < 0)]
    simp
    field_simp
  rw [h2] at this
  exact this

theorem integrable_Ioc_of_le {F : ℝ → ℝ} {M : ℝ} (hm : AEStronglyMeasurable F volume)
    (h : ∀ t ∈ Ioc (0 : ℝ) 1, ‖F t‖ ≤ M) : Integrable F (volume.restrict (Ioc (0 : ℝ) 1)) := by
  refine Integrable.mono' (integrable_const M) hm.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using h t ht

theorem integrable_Ioi_of_le {F : ℝ → ℝ} {M μ : ℝ} (hμ : 0 < μ) (hm : AEStronglyMeasurable F volume)
    (h : ∀ t ∈ Ioi (0 : ℝ), ‖F t‖ ≤ M * Real.exp (-μ * t)) :
    Integrable F (volume.restrict (Ioi (0 : ℝ))) := by
  have hint : IntegrableOn (fun t : ℝ => M * Real.exp (-μ * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -μ < 0) 0).const_mul M
  refine Integrable.mono' hint hm.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using h t ht

/-- `(1 + t)^k ≤ C e^{μ t}` for `t ≥ 0`. -/
theorem pow_one_add_le_exp (k : ℕ) {μ : ℝ} (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ k ≤ C * Real.exp (μ * t) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, by norm_num, fun t ht => by
      simp only [pow_zero, one_mul]
      exact Real.one_le_exp (by positivity)⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set δ : ℝ := μ / k with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨(1 + 1 / δ) ^ k, by positivity, fun t ht => ?_⟩
  have h1 : 1 + t ≤ (1 + 1 / δ) * Real.exp (δ * t) := by
    have e1 : δ * t + 1 ≤ Real.exp (δ * t) := Real.add_one_le_exp _
    have e2 : 1 ≤ Real.exp (δ * t) := Real.one_le_exp (by positivity)
    have : t ≤ (1 / δ) * Real.exp (δ * t) := by
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hδ0]; nlinarith
    nlinarith
  calc (1 + t) ^ k ≤ ((1 + 1 / δ) * Real.exp (δ * t)) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = (1 + 1 / δ) ^ k * Real.exp (μ * t) := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        rw [hδ]; field_simp


/-! ### The logarithmic potential: measurability, lower bound, upper semicontinuity -/

open CatalanCore.Decay.ComplexEnergy in
theorem measurable_potC (σ : Measure ℂ) [SFinite σ] : Measurable (potC σ) := by
  unfold potC
  have h : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖ := by fun_prop
  exact (h.stronglyMeasurable.integral_prod_right').measurable

open CatalanCore.Decay.ComplexEnergy in
/-- `-2 A ≤ potC σ t` for a square-root-majorised measure. -/
theorem neg_le_potC_half {σ : Measure ℂ} {b A : ℝ} (hσ : BallMajA σ b A (1 / 2)) [IsFiniteMeasure σ] (t : ℂ) :
    -(A * (1 : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) ≤ potC σ t := by
  unfold potC
  have h1 : ∫ u, Real.log ‖t - u‖ ∂σ = ∫ u, posC t u ∂σ - ∫ u, regC t 1 u ∂σ := by
    rw [← integral_sub (integrable_posC hσ t) (integrable_regC hσ one_pos t)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => log_norm_eq t u)
  have h2 : 0 ≤ ∫ u, posC t u ∂σ := integral_nonneg fun u => Real.posLog_nonneg
  have h3 := integral_regC_le hσ one_pos t
  linarith

lemma abs_log_add_le {a h c : ℝ} (ha : 0 < a) (hh : 0 < h) (hh1 : h < 1) (hc : a + 1 ≤ c) :
    |Real.log (a + h)| ≤ |Real.log a| + Real.log c := by
  have hc1 : 1 ≤ c := by linarith
  have hL : 0 ≤ Real.log c := Real.log_nonneg hc1
  rcases le_or_gt 1 (a + h) with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have : Real.log (a + h) ≤ Real.log c := Real.log_le_log (by linarith) (by linarith)
    linarith [abs_nonneg (Real.log a)]
  · have h2 : Real.log (a + h) < 0 := Real.log_neg (by linarith) h1
    have h3 : Real.log a ≤ Real.log (a + h) := Real.log_le_log ha (by linarith)
    rw [abs_of_neg h2, abs_of_neg (by linarith : Real.log a < 0)]
    linarith

open CatalanCore.Decay.ComplexEnergy in
/-- **Upper semicontinuity of the logarithmic potential** of a finite measure with bounded support,
no atoms and locally integrable logarithm. -/
theorem potC_usc_of {ν : Measure ℂ} [IsFiniteMeasure ν] {b : ℝ} (hb0 : 0 < b)
    (hb : ∀ᵐ u ∂ν, ‖u‖ ≤ b) (hne0 : ∀ x : ℂ, ν {x} = 0)
    (hint : ∀ t : ℂ, Integrable (fun u => Real.log ‖t - u‖) ν) (s₀ : ℂ)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, ‖s - s₀‖ < δ → potC ν s ≤ potC ν s₀ + ε := by
  set Φ : ℝ → ℝ := fun h => ∫ u, Real.log (‖s₀ - u‖ + h) ∂ν with hΦ
  have hne : ∀ᵐ u ∂ν, u ≠ s₀ := by
    have : ν {s₀} = 0 := hne0 s₀
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with u hu
    simpa using hu
  have hlim : Tendsto Φ (𝓝[>] 0) (𝓝 (potC ν s₀)) := by
    unfold potC
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => |Real.log ‖s₀ - u‖| + Real.log (1 + ‖s₀‖ + b + 1)) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        (Measurable.log (by fun_prop)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with h hh
      filter_upwards [hb, hne] with u hu hu0
      have hpos : 0 < ‖s₀ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu0))
      rw [Real.norm_eq_abs]
      refine abs_log_add_le hpos hh.1 hh.2 ?_
      have h1 : ‖s₀ - u‖ ≤ ‖s₀‖ + b := (norm_sub_le _ _).trans (by linarith)
      have := norm_nonneg s₀
      linarith
    · exact (hint s₀).abs.add (integrable_const _)
    · filter_upwards [hne] with u hu0
      have hpos : 0 < ‖s₀ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu0))
      have hc : ContinuousAt (fun h : ℝ => Real.log (‖s₀ - u‖ + h)) 0 := by
        refine ContinuousAt.log (by fun_prop) ?_
        simpa using hpos.ne'
      have := hc.tendsto
      simp only [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
  have hev := hlim.eventually (gt_mem_nhds (show potC ν s₀ < potC ν s₀ + ε by linarith))
  obtain ⟨h, hΦh, hh0, hh1⟩ := (hev.and (Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1))).exists
  refine ⟨h, hh0, fun s hs => ?_⟩
  have hneS : ∀ᵐ u ∂ν, u ≠ s := by
    have : ν {s} = 0 := hne0 s
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp this] with u hu
    simpa using hu
  have hint2 : Integrable (fun u => Real.log (‖s₀ - u‖ + h)) ν := by
    refine Integrable.mono' ((hint s₀).abs.add
      (integrable_const (Real.log (1 + ‖s₀‖ + b + 1)))) (Measurable.log (by fun_prop)).aestronglyMeasurable ?_
    filter_upwards [hb, hne] with u hu hu0
    have hpos : 0 < ‖s₀ - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu0))
    rw [Real.norm_eq_abs]
    refine abs_log_add_le hpos hh0 hh1 ?_
    have h1 : ‖s₀ - u‖ ≤ ‖s₀‖ + b := (norm_sub_le _ _).trans (by linarith)
    have := norm_nonneg s₀
    linarith
  have hmono : ∫ u, Real.log ‖s - u‖ ∂ν ≤ ∫ u, Real.log (‖s₀ - u‖ + h) ∂ν := by
    refine integral_mono_ae (hint s) hint2 ?_
    filter_upwards [hneS] with u hu
    have hpos : 0 < ‖s - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hu))
    refine Real.log_le_log hpos ?_
    calc ‖s - u‖ = ‖(s - s₀) + (s₀ - u)‖ := by ring_nf
      _ ≤ ‖s - s₀‖ + ‖s₀ - u‖ := norm_add_le _ _
      _ ≤ ‖s₀ - u‖ + h := by linarith
  unfold potC at hΦh ⊢
  have : Φ h = ∫ u, Real.log (‖s₀ - u‖ + h) ∂ν := rfl
  linarith

end CatalanCore.Decay.CurveFamily
