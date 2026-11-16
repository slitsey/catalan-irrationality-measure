module

public import CatalanCore.Zeta5.Energy.Circle

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, Apery/EnergyBlocks.lean, Apery/EnergyRaw.lean (`block_A`, `block_B`, `block_AB_sum`, `energy_raw`) (Moritz Firsching); changes: module conversion, namespace CatalanCore.Zeta5.Energy; the sixteen arcsine atoms are replaced by one measure `ν` with the arcsine majorant `ArcMaj` (atoms `Idx h = Fin h ⊕ Fin 16` become `Option (Fin h)`), circles are probability measures, blocks (C) and (D) are new (ZD05 error term, `∫ U dν`), the weights are `-1` on `ν` and `1/K` on each circle. -/

/-!
# The raw configuration inequality (ZD06, ZD07 first half)

For a measure `ν` on `ℝ` with `ArcMaj ν b F`, a real `K > 0` with `h = K ν(ℝ)` and pairwise
distinct reals `t_1, …, t_h`, apply Lemma 6.2 (`energy_log_nonpos`) to the family
`ν̃` (weight `-1`) and the circles `circ t_i ε` (weight `1/K`).  The four blocks are

* (A) `∬ log ‖z - w‖ d(circ t ε)² = log ε` (`pair_circ_self`);
* (B) `∬ log ‖z - w‖ d(circ t_i ε) d(circ t_j ε) ≥ log |t_i - t_j|` (`pair_circ_circ_ge`);
* (C) `∬ log ‖z - w‖ d(circ t_i ε) dν̃ ≤ U(t_i) + C_circ √ε`, `C_circ = 2√2 F/√b` (ZD05);
* (D) `∬ log ‖z - w‖ dν̃ dν̃ = ∫ U dν =: I(ν)` (Fubini).

Result (`energy_raw`): `h log ε + ∑ᵢ ∑ᵢ' log|tᵢ - tᵢ'| ≤ 2K ∑ᵢ (U(tᵢ) + C_circ √ε) - K² I(ν)`,
where the diagonal terms are `log 0 = 0`.
-/

open MeasureTheory Set Real Filter Topology

namespace CatalanCore.Zeta5.Energy

variable {ν : Measure ℝ} {b F : ℝ}

/-- The logarithmic potential `U(t) = ∫ log |t - u| dν(u)`. -/
noncomputable def potU (ν : Measure ℝ) (t : ℝ) : ℝ := ∫ u, Real.log |t - u| ∂ν

/-- The logarithmic energy `I(ν) = ∫ U dν = ∬ log |u - v| dν dν`. -/
noncomputable def energyI (ν : Measure ℝ) : ℝ := ∫ u, potU ν u ∂ν

/-- The atoms of the configuration: `ν̃` and the circles about `t i`. -/
noncomputable def cfg (ν : Measure ℝ) {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) : Option (Fin h) → Measure ℂ
  | none => nuC ν
  | some i => circ (t i) ε

instance cfg_finite (ν : Measure ℝ) [IsFiniteMeasure ν] {h : ℕ} (t : Fin h → ℝ) (ε : ℝ)
    (k : Option (Fin h)) : IsFiniteMeasure (cfg ν t ε k) := by
  cases k <;> simp only [cfg] <;> infer_instance

/-! ### Circle facts -/

lemma ae_dist_circ (c : ℝ) {ε : ℝ} (hε : 0 < ε) : ∀ᵐ w ∂(circ c ε), ‖(c : ℂ) - w‖ = ε := by
  unfold circ
  refine ae_smul_measure' ?_ _
  rw [ae_map_iff (measurable_circleMap' _ _).aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine ae_of_all _ fun θ => ?_
  rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]

/-- Block (A): the self-energy of a circle. -/
lemma pair_circ_self (c : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circ c ε).prod (circ c ε))) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circ c ε).prod (circ c ε)) = Real.log ε := by
  rw [integral_prod_symm _ hint]
  have : ∀ᵐ w ∂(circ c ε), ∫ z, Real.log ‖z - w‖ ∂(circ c ε) = Real.log ε := by
    filter_upwards [ae_dist_circ c hε] with w hw
    rw [integral_log_circ_max c hε w, hw, max_self]
  rw [integral_congr_ae this]
  simp

/-- Block (B): the mutual energy of two distinct circles dominates `log |c - c'|`. -/
lemma pair_circ_circ_ge (c c' : ℝ) {ε : ℝ} (hε : 0 < ε) (hne : c ≠ c')
    (hint : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circ c ε).prod (circ c' ε))) :
    Real.log |c - c'| ≤
      ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circ c ε).prod (circ c' ε)) := by
  rw [integral_prod_symm _ hint]
  have h1 : Integrable (fun w : ℂ => ∫ z, Real.log ‖z - w‖ ∂(circ c ε)) (circ c' ε) :=
    hint.integral_prod_right
  have h2 : Integrable (fun w : ℂ => Real.log ‖(c : ℂ) - w‖) (circ c' ε) := by
    refine (integrable_log_circ c' hε (c : ℂ)).congr (ae_of_all _ fun w => ?_)
    simp only [norm_sub_rev]
  have h3 : ∀ᵐ w ∂(circ c' ε), (c : ℂ) ≠ w := by
    have := (measure_eq_zero_iff_ae_notMem.mp (circ_singleton c' hε.ne' (c : ℂ)))
    filter_upwards [this] with w hw hcw
    exact hw (by simp [hcw])
  have h4 : ∫ w, Real.log ‖(c : ℂ) - w‖ ∂(circ c' ε) = Real.log (max ε |c' - c|) := by
    have e : ∀ w : ℂ, Real.log ‖(c : ℂ) - w‖ = Real.log ‖w - (c : ℂ)‖ := fun w => by
      rw [norm_sub_rev]
    simp_rw [e]
    rw [integral_log_circ_max c' hε (c : ℂ)]
    congr 2
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h5 : Real.log |c - c'| ≤ Real.log (max ε |c' - c|) := by
    have hpos : 0 < |c - c'| := abs_pos.mpr (sub_ne_zero.mpr hne)
    refine Real.log_le_log hpos ?_
    rw [abs_sub_comm]
    exact le_max_right _ _
  calc Real.log |c - c'| ≤ Real.log (max ε |c' - c|) := h5
    _ = ∫ w, Real.log ‖(c : ℂ) - w‖ ∂(circ c' ε) := h4.symm
    _ ≤ ∫ w, ∫ z, Real.log ‖z - w‖ ∂(circ c ε) ∂(circ c' ε) := by
        refine integral_mono_ae h2 h1 ?_
        filter_upwards [h3] with w hw
        rw [integral_log_circ_max c hε w]
        refine Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hw)) (le_max_right _ _)

/-! ### Integrability and distinctness -/

section Hyp

variable [IsFiniteMeasure ν]

lemma integrable_circ_circ (c c' : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circ c ε).prod (circ c' ε)) := by
  refine integrable_log_prod (C := 2 * Real.log (1 + |c| + ε + (|c'| + |ε|)) + |Real.log ε|) ?_ ?_
  · exact ae_of_all _ fun w => integrable_log_circ c hε w
  · filter_upwards [ae_norm_circ c' ε] with w hw
    exact integral_abs_log_circ_le c hε w hw

lemma integrable_circ_nuC (hν : ArcMaj ν b F) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((circ c ε).prod (nuC ν)) := by
  refine integrable_log_prod (C := 2 * Real.log (1 + |c| + ε + b) + |Real.log ε|) ?_ ?_
  · exact ae_of_all _ fun w => integrable_log_circ c hε w
  · filter_upwards [ae_norm_nuC hν] with w hw
    exact integral_abs_log_circ_le c hε w hw

lemma integrable_nuC_circ (hν : ArcMaj ν b F) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((nuC ν).prod (circ c ε)) :=
  integrable_log_swap (integrable_circ_nuC hν c hε)

lemma integrable_nuC_nuC (hν : ArcMaj ν b F) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((nuC ν).prod (nuC ν)) := by
  refine integrable_log_prod
    (C := ν.real univ * Real.log (1 + b + b) + 2 * Real.sqrt 2 * F / Real.sqrt b * Real.sqrt 1)
    ?_ ?_
  · rw [ae_nuC]
    filter_upwards with t
    have h := integrable_log_abs_sub hν t
    have : Integrable (fun u : ℝ => Real.log ‖(u : ℂ) - (t : ℂ)‖) ν := by
      refine h.congr (ae_of_all _ fun u => ?_)
      simp only
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact measurableEmbedding_ofReal.integrable_map_iff.mpr this
  · rw [ae_nuC]
    filter_upwards [hν.ae_mem] with t ht
    rw [integral_nuC]
    have e : ∀ u : ℝ, abs (Real.log ‖(u : ℂ) - (t : ℂ)‖) = abs (Real.log |t - u|) := by
      intro u
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    simp_rw [e]
    refine (integral_abs_log_le hν t).trans ?_
    have hmono : Real.log (1 + |t| + b) ≤ Real.log (1 + b + b) := by
      refine Real.log_le_log (by have := hν.b_pos; positivity) ?_
      rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ ν.real univ)
    linarith

end Hyp

/-! ### The blocks (C), (D) and the pair integrals of `cfg` -/

lemma log_max_eq_add {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log (max ε x) = Real.log x + Real.posLog (ε / x) := by
  rcases le_total ε x with h | h
  · rw [max_eq_right h, (Real.posLog_eq_zero_iff _).mpr (by
      rw [abs_of_nonneg (by positivity), div_le_one hx]; exact h), add_zero]
  · rw [max_eq_left h, Real.posLog_eq_log (by
      rw [abs_of_nonneg (by positivity), one_le_div hx]; exact h), Real.log_div hε.ne' hx.ne']
    ring

section Hyp2

variable [IsFiniteMeasure ν]

/-- Block (C), exact form (ZD05 in context): the circle-to-`ν` energy is
`U(c) + ∫ log⁺(ε/|c - u|) dν(u)`, i.e. `∫ U dω_{c,ε} - U(c) = ∫ log⁺(ε/|c - u|) dν`. -/
lemma pair_circ_nuC_eq (hν : ArcMaj ν b F) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circ c ε).prod (nuC ν)) =
      potU ν c + ∫ u, regTerm c ε u ∂ν := by
  rw [integral_prod_symm _ (integrable_circ_nuC hν c hε), integral_nuC]
  have e : ∀ u : ℝ, ∫ z, Real.log ‖z - (u : ℂ)‖ ∂(circ c ε) = Real.log (max ε |c - u|) := by
    intro u
    rw [integral_log_circ_max c hε, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [e]
  have hae : ∀ᵐ u ∂ν, Real.log (max ε |c - u|) = Real.log |c - u| + regTerm c ε u := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hν.singleton_zero c)] with u hu
    have : 0 < |c - u| := abs_pos.mpr (sub_ne_zero.mpr (fun h => hu (by simp [h])))
    exact log_max_eq_add hε this
  rw [integral_congr_ae hae, integral_add (integrable_log_abs_sub hν c) (integrable_regTerm hν hε c)]
  rfl

/-- Block (C): circle-to-`ν` energy is at most `U(c) + C_circ √ε` (ZD05). -/
lemma pair_circ_nuC_le (hν : ArcMaj ν b F) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((circ c ε).prod (nuC ν)) ≤
      potU ν c + 2 * Real.sqrt 2 * F / Real.sqrt b * Real.sqrt ε := by
  rw [pair_circ_nuC_eq hν c hε]
  exact add_le_add le_rfl (integral_regTerm_le hν hε c)

/-- Block (D): the energy of `ν`. -/
lemma pair_nuC_nuC (hν : ArcMaj ν b F) :
    ∫ p : ℂ × ℂ, Real.log ‖p.1 - p.2‖ ∂((nuC ν).prod (nuC ν)) = energyI ν := by
  rw [integral_prod _ (integrable_nuC_nuC hν), integral_nuC]
  unfold energyI potU
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [integral_nuC]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

end Hyp2

section Assembly

variable [IsFiniteMeasure ν] {h : ℕ}

lemma pairInt_swap (m : Option (Fin h) → Measure ℂ) [∀ k, IsFiniteMeasure (m k)] (k l : Option (Fin h)) :
    pairInt m (fun z w => Real.log ‖z - w‖) l k = pairInt m (fun z w => Real.log ‖z - w‖) k l := by
  unfold pairInt
  rw [← integral_prod_swap]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]

/-- **The raw configuration inequality** (ZD06/ZD07, first half): for every `ε > 0` and
pairwise distinct reals `t_i` (`i < h`), with `h = K ν(ℝ)`,
`h log ε + ∑ᵢ ∑ᵢ' log |tᵢ - tᵢ'| ≤ 2K ∑ᵢ (U(tᵢ) + C_circ √ε) - K² I(ν)`, `C_circ = 2√2F/√b`. -/
theorem energy_raw (hν : ArcMaj ν b F) {K : ℝ} (hK : 0 < K) (hh : (h : ℝ) = K * ν.real univ)
    (t : Fin h → ℝ) (ht : Function.Injective t) {ε : ℝ} (hε : 0 < ε) :
    (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'| ≤
      2 * K * ∑ i, (potU ν (t i) + 2 * Real.sqrt 2 * F / Real.sqrt b * Real.sqrt ε) -
        K ^ 2 * energyI ν := by
  set C : ℝ := 2 * Real.sqrt 2 * F / Real.sqrt b with hC
  set m : Option (Fin h) → Measure ℂ := cfg ν t ε with hm
  set s : Option (Fin h) → ℝ := fun o => o.elim (-1) (fun _ => 1 / K) with hs
  have hR : ∀ k, ∀ᵐ z ∂(m k), ‖z‖ ≤ b + ε + ∑ i, |t i| := by
    intro k
    cases k with
    | none =>
      filter_upwards [ae_norm_nuC hν] with z hz
      have : 0 ≤ ∑ i, |t i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      linarith
    | some i =>
      filter_upwards [ae_norm_circ (t i) ε] with z hz
      have h1 : |t i| ≤ ∑ j, |t j| := Finset.single_le_sum (f := fun j => |t j|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      rw [abs_of_pos hε] at hz
      have := hν.b_pos
      linarith
  have hmass : ∑ k, s k * (m k).real univ = 0 := by
    rw [Fintype.sum_option]
    simp only [hs, hm, cfg, Option.elim, nuC_real_univ]
    simp only [probReal_univ, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [hh]; field_simp; ring
  have hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) ((m k).prod (m l)) := by
    intro k l
    cases k <;> cases l <;> simp only [hm, cfg]
    · exact integrable_nuC_nuC hν
    · exact integrable_nuC_circ hν _ hε
    · exact integrable_circ_nuC hν _ hε
    · exact integrable_circ_circ _ _ hε
  have hae : ∀ k l, ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2 := by
    intro k l
    cases l with
    | none => exact ae_ne_of_noAtoms_right (nuC_singleton hν.singleton_zero)
    | some j => exact ae_ne_of_noAtoms_right (circ_singleton _ hε.ne')
  have hE := energy_log_nonpos hR hmass hint hae
  -- the pair integrals
  obtain ⟨L, hL⟩ : ∃ L : Fin h → Fin h → ℝ, ∀ i i',
      L i i' = pairInt m (fun z w => Real.log ‖z - w‖) (some i) (some i') :=
    ⟨fun i i' => pairInt m (fun z w => Real.log ‖z - w‖) (some i) (some i'), fun _ _ => rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Fin h → ℝ, ∀ i,
      Q i = pairInt m (fun z w => Real.log ‖z - w‖) (some i) none :=
    ⟨fun i => pairInt m (fun z w => Real.log ‖z - w‖) (some i) none, fun _ => rfl⟩
  have hQle : ∀ i, Q i ≤ potU ν (t i) + C * Real.sqrt ε := fun i => by
    rw [hQ]; exact pair_circ_nuC_le hν (t i) hε
  have hnn : pairInt m (fun z w => Real.log ‖z - w‖) none none = energyI ν :=
    pair_nuC_nuC hν
  have hLii : ∀ i, L i i = Real.log ε := fun i => by
    rw [hL]; exact pair_circ_self (t i) hε (integrable_circ_circ _ _ hε)
  have hLge : ∀ i i', i ≠ i' → Real.log |t i - t i'| ≤ L i i' := fun i i' hne => by
    rw [hL]; exact pair_circ_circ_ge (t i) (t i') hε (fun e => hne (ht e)) (integrable_circ_circ _ _ hε)
  have hnS : ∀ i, pairInt m (fun z w => Real.log ‖z - w‖) none (some i) = Q i := fun i => by
    rw [hQ]; exact pairInt_swap m (some i) none
  -- expand the energy
  unfold energy at hE
  rw [Fintype.sum_option] at hE
  simp only [Fintype.sum_option, hnn, hnS, ← hL, ← hQ] at hE
  simp only [hs, Option.elim] at hE
  rw [Finset.sum_add_distrib] at hE
  have e1 : ∑ i, (-1 : ℝ) * (1 / K) * Q i = -(1 / K) * ∑ i, Q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, (1 / K) * (-1 : ℝ) * Q i = -(1 / K) * ∑ i, Q i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ i', (1 / K) * (1 / K) * L i i' = (1 / K) ^ 2 * ∑ i, ∑ i', L i i' := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  have hE' : energyI ν - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i' ≤ 0 := by
    linarith [hE, e1, e2, e3]
  -- block AB
  have hAB : (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'| ≤ ∑ i, ∑ i', L i i' := by
    have hi : ∀ i, Real.log ε + ∑ i', Real.log |t i - t i'| ≤ ∑ i', L i i' := by
      intro i
      rw [← Finset.add_sum_erase Finset.univ (fun i' => L i i') (Finset.mem_univ i), hLii i,
        ← Finset.sum_erase (s := Finset.univ) (a := i) (f := fun i' => Real.log |t i - t i'|)
          (by simp)]
      refine add_le_add le_rfl (Finset.sum_le_sum fun i' hi' => ?_)
      exact hLge i i' (fun e => Finset.ne_of_mem_erase hi' e.symm)
    calc (h : ℝ) * Real.log ε + ∑ i, ∑ i', Real.log |t i - t i'|
        = ∑ i : Fin h, (Real.log ε + ∑ i', Real.log |t i - t i'|) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hi i
  have hQsum : ∑ i, Q i ≤ ∑ i, (potU ν (t i) + C * Real.sqrt ε) :=
    Finset.sum_le_sum fun i _ => hQle i
  -- combine: multiply hE' by K²
  have hK2 : 0 < K ^ 2 := by positivity
  have h1 : K ^ 2 * (energyI ν - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i') ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hK2.le hE'
  have h2 : K ^ 2 * (energyI ν - 2 * (1 / K) * ∑ i, Q i + (1 / K) ^ 2 * ∑ i, ∑ i', L i i') =
      K ^ 2 * energyI ν - 2 * K * ∑ i, Q i + ∑ i, ∑ i', L i i' := by
    field_simp
  have h3 : 2 * K * ∑ i, Q i ≤ 2 * K * ∑ i, (potU ν (t i) + C * Real.sqrt ε) :=
    mul_le_mul_of_nonneg_left hQsum (by positivity)
  linarith [h1, h2, h3, hAB]

end Assembly

end CatalanCore.Zeta5.Energy
