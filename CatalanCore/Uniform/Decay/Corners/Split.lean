module

public import CatalanCore.Uniform.Decay.Corners.Reflect

@[expose] public section

/-!
# Integrability of `s^i t^j L` on every rectangle, and gluing of rectangles

For a positive definite form the integrand `ff = s^i t^j L` is integrable on every bounded
rectangle (`ff_integrableOn`: `|ff| ≤ S^i T^j (c + |log t|)` off the null set `t = 0`).  Hence
the iterated integral `BEL` is the set integral over the rectangle (Fubini) and is additive under
splitting of the rectangle in either direction; the boundary terms `BER` are additive as well
(the cut edge cancels), so `BE` glues (`BE_glue_s`, `BE_glue_t`).
-/

namespace CatalanCore.Uniform.Decay.Corners

open Set intervalIntegral MeasureTheory
open CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Assembly

variable {A B C m K : ℝ}

theorem ff_integrableOn (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    IntegrableOn (fun p : ℝ × ℝ => ff A B C i j p.1 p.2) (Ioc a b ×ˢ Ioc c d) := by
  set S : ℝ := max |a| |b| with hS
  set T : ℝ := max |c| |d| with hT
  set R : ℝ := S ^ 2 + T ^ 2 + 1 with hR
  set c1 : ℝ := (|Real.log m| + |Real.log K| + |Real.log R|) / 2 with hc1
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  set K1 : ℝ := S ^ i * T ^ j with hK1
  have hK10 : 0 ≤ K1 := by rw [hK1]; positivity
  set g : ℝ → ℝ := fun t => K1 * c1 + K1 * |Real.log t| with hg
  have hgi : IntegrableOn g (Ioc c d) := by
    have h1 : IntervalIntegrable g volume c d :=
      intervalIntegrable_const.add ((intervalIntegral.intervalIntegrable_log').abs.const_mul K1)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).1 h1
  have hprod : Integrable (fun z : ℝ × ℝ => (fun _ : ℝ => (1 : ℝ)) z.1 * g z.2)
      ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) :=
    Integrable.mul_prod (integrable_const 1) hgi
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hprod
  rw [IntegrableOn]
  refine Integrable.mono' hprod (measurable_ff A B C i j).aestronglyMeasurable ?_
  rw [ae_restrict_iff' (measurableSet_Ioc.prod measurableSet_Ioc)]
  have hnull : ∀ᵐ p : ℝ × ℝ ∂(volume : Measure (ℝ × ℝ)), p.2 ≠ 0 := by
    have hm : MeasurableSet {p : ℝ × ℝ | p.2 ≠ 0} :=
      (measurableSet_singleton (0 : ℝ)).compl.preimage measurable_snd
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hm]
    refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [(Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)] with y hy
    exact hy
  filter_upwards [hnull] with p hp0 hp
  obtain ⟨⟨hp1a, hp1b⟩, ⟨hp2c, hp2d⟩⟩ := hp
  have hs : |p.1| ≤ S := abs_le.2 ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, le_abs_self (-a)],
    by linarith [le_abs_self b, le_max_right |a| |b|]⟩
  have ht : |p.2| ≤ T := abs_le.2 ⟨by linarith [neg_abs_le c, le_max_left |c| |d|, le_abs_self (-c)],
    by linarith [le_abs_self d, le_max_right |c| |d|]⟩
  have hs2 : p.1 ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs p.1, abs_nonneg p.1]
  have ht2 : p.2 ^ 2 ≤ T ^ 2 := by nlinarith [sq_abs p.2, abs_nonneg p.2]
  have htpos : 0 < p.2 ^ 2 := by positivity
  have hL := h.Lq_bound (s := p.1) (t := p.2) (ρ := p.2 ^ 2) (R := R) htpos
    (by nlinarith [sq_nonneg p.1]) (by rw [hR]; nlinarith)
  have hlog : |Real.log (p.2 ^ 2)| = 2 * |Real.log p.2| := by
    rw [Real.log_pow]; push_cast; rw [abs_mul]; norm_num
  rw [hlog] at hL
  have hLL : |Lq A B C p.1 p.2| ≤ c1 + |Real.log p.2| := by
    refine hL.trans (le_of_eq ?_); rw [hc1]; ring
  have hSi : |p.1| ^ i ≤ S ^ i := pow_le_pow_left₀ (abs_nonneg _) hs i
  have hTj : |p.2| ^ j ≤ T ^ j := pow_le_pow_left₀ (abs_nonneg _) ht j
  show ‖ff A B C i j p.1 p.2‖ ≤ 1 * g p.2
  rw [Real.norm_eq_abs]
  unfold ff
  rw [abs_mul, abs_mul, abs_pow, abs_pow]
  calc |p.1| ^ i * |p.2| ^ j * |Lq A B C p.1 p.2|
      ≤ S ^ i * T ^ j * (c1 + |Real.log p.2|) :=
        mul_le_mul (mul_le_mul hSi hTj (by positivity) (by positivity)) hLL (abs_nonneg _)
          (by positivity)
    _ = 1 * g p.2 := by rw [hg, hK1]; ring

theorem BEL_eq_set (h : PD A B C m K) (i j : ℕ) {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    BEL A B C i j a b c d = ∫ p in Ioc a b ×ˢ Ioc c d, ff A B C i j p.1 p.2 := by
  have hI := ff_integrableOn h i j hab hcd
  rw [Measure.volume_eq_prod] at hI ⊢
  rw [setIntegral_prod _ hI]
  unfold BEL
  rw [intervalIntegral.integral_of_le hab]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  simp only [ff]
  rw [intervalIntegral.integral_of_le hcd]

theorem BEL_glue_s (h : PD A B C m K) (i j : ℕ) {a m' b c d : ℝ} (ham : a ≤ m') (hmb : m' ≤ b)
    (hcd : c ≤ d) :
    BEL A B C i j a b c d = BEL A B C i j a m' c d + BEL A B C i j m' b c d := by
  rw [BEL_eq_set h i j (ham.trans hmb) hcd, BEL_eq_set h i j ham hcd, BEL_eq_set h i j hmb hcd]
  rw [Measure.volume_eq_prod]
  rw [← setIntegral_union]
  · congr 1
    rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc ham hmb]
  · exact (Set.disjoint_prod.2 (Or.inl (Set.Ioc_disjoint_Ioc_of_le le_rfl)))
  · exact measurableSet_Ioc.prod measurableSet_Ioc
  · exact ff_integrableOn h i j ham hcd
  · exact ff_integrableOn h i j hmb hcd

theorem BEL_glue_t (h : PD A B C m K) (i j : ℕ) {a b c n d : ℝ} (hab : a ≤ b) (hcn : c ≤ n)
    (hnd : n ≤ d) :
    BEL A B C i j a b c d = BEL A B C i j a b c n + BEL A B C i j a b n d := by
  rw [BEL_eq_set h i j hab (hcn.trans hnd), BEL_eq_set h i j hab hcn, BEL_eq_set h i j hab hnd]
  rw [Measure.volume_eq_prod]
  rw [← setIntegral_union]
  · congr 1
    rw [← Set.prod_union, Set.Ioc_union_Ioc_eq_Ioc hcn hnd]
  · exact (Set.disjoint_prod.2 (Or.inr (Set.Ioc_disjoint_Ioc_of_le le_rfl)))
  · exact measurableSet_Ioc.prod measurableSet_Ioc
  · exact ff_integrableOn h i j hab hcn
  · exact ff_integrableOn h i j hab hnd

/-- Edge integrands at `s = e`: `e^(i+1) t^j L(e,t)` (identically `0` for `e = 0`). -/
theorem edge_t_integrable (h : PD A B C m K) (i j : ℕ) (e c d : ℝ) :
    IntervalIntegrable (fun t => e ^ (i + 1) * t ^ j * Lq A B C e t) volume c d := by
  by_cases he : e = 0
  · subst he; simpa using intervalIntegrable_const (c := (0 : ℝ))
  · exact (((continuous_const.mul (continuous_id.pow j)).mul
      (h.continuous_Lq_t he))).intervalIntegrable _ _

theorem edge_s_integrable (h : PD A B C m K) (i j : ℕ) (e a b : ℝ) :
    IntervalIntegrable (fun s => s ^ i * e ^ (j + 1) * Lq A B C s e) volume a b := by
  by_cases he : e = 0
  · subst he; simpa using intervalIntegrable_const (c := (0 : ℝ))
  · exact ((((continuous_id.pow i).mul continuous_const).mul
      (h.continuous_Lq_s he))).intervalIntegrable _ _

theorem BER_glue_s (h : PD A B C m K) (i j : ℕ) (a m' b c d : ℝ) :
    BER A B C i j a b c d = BER A B C i j a m' c d + BER A B C i j m' b c d := by
  unfold BER
  have t1 : ∀ e e' : ℝ, (∫ t in c..d, (e ^ (i + 1) * t ^ j * Lq A B C e t
      - e' ^ (i + 1) * t ^ j * Lq A B C e' t))
      = (∫ t in c..d, e ^ (i + 1) * t ^ j * Lq A B C e t)
        - ∫ t in c..d, e' ^ (i + 1) * t ^ j * Lq A B C e' t := fun e e' =>
    intervalIntegral.integral_sub (edge_t_integrable h i j e c d) (edge_t_integrable h i j e' c d)
  have q1 : IntervalIntegrable (fun s => s ^ i * d ^ (j + 1) * Lq A B C s d
      - s ^ i * c ^ (j + 1) * Lq A B C s c) volume a m' :=
    (edge_s_integrable h i j d a m').sub (edge_s_integrable h i j c a m')
  have q2 : IntervalIntegrable (fun s => s ^ i * d ^ (j + 1) * Lq A B C s d
      - s ^ i * c ^ (j + 1) * Lq A B C s c) volume m' b :=
    (edge_s_integrable h i j d m' b).sub (edge_s_integrable h i j c m' b)
  have hq := (intervalIntegral.integral_add_adjacent_intervals q1 q2).symm
  rw [t1 b a, t1 m' a, t1 b m', hq]
  ring

theorem BER_glue_t (h : PD A B C m K) (i j : ℕ) (a b c n d : ℝ) :
    BER A B C i j a b c d = BER A B C i j a b c n + BER A B C i j a b n d := by
  unfold BER
  have q1 : IntervalIntegrable (fun t => b ^ (i + 1) * t ^ j * Lq A B C b t
      - a ^ (i + 1) * t ^ j * Lq A B C a t) volume c n :=
    (edge_t_integrable h i j b c n).sub (edge_t_integrable h i j a c n)
  have q2 : IntervalIntegrable (fun t => b ^ (i + 1) * t ^ j * Lq A B C b t
      - a ^ (i + 1) * t ^ j * Lq A B C a t) volume n d :=
    (edge_t_integrable h i j b n d).sub (edge_t_integrable h i j a n d)
  have hq := (intervalIntegral.integral_add_adjacent_intervals q1 q2).symm
  have t2 : ∀ e e' : ℝ, (∫ s in a..b, (s ^ i * e ^ (j + 1) * Lq A B C s e
      - s ^ i * e' ^ (j + 1) * Lq A B C s e'))
      = (∫ s in a..b, s ^ i * e ^ (j + 1) * Lq A B C s e)
        - ∫ s in a..b, s ^ i * e' ^ (j + 1) * Lq A B C s e' := fun e e' =>
    intervalIntegral.integral_sub (edge_s_integrable h i j e a b) (edge_s_integrable h i j e' a b)
  rw [hq, t2 d c, t2 n c, t2 d n]
  ring

theorem BE_glue_s (h : PD A B C m K) (i j : ℕ) {a m' b c d : ℝ} (ham : a ≤ m') (hmb : m' ≤ b)
    (hcd : c ≤ d) (h1 : BE A B C i j a m' c d) (h2 : BE A B C i j m' b c d) :
    BE A B C i j a b c d := by
  unfold BE at *
  rw [BEL_glue_s h i j ham hmb hcd, BER_glue_s h i j a m' b c d]
  linear_combination h1 + h2

theorem BE_glue_t (h : PD A B C m K) (i j : ℕ) {a b c n d : ℝ} (hab : a ≤ b) (hcn : c ≤ n)
    (hnd : n ≤ d) (h1 : BE A B C i j a b c n) (h2 : BE A B C i j a b n d) :
    BE A B C i j a b c d := by
  unfold BE at *
  rw [BEL_glue_t h i j hab hcn hnd, BER_glue_t h i j a b c n d]
  linear_combination h1 + h2

end CatalanCore.Uniform.Decay.Corners
