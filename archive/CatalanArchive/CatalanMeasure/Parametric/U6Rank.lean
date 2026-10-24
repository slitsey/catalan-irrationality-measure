module
public import CatalanArchive.CatalanMeasure.Parametric.U6Digits
public import CatalanMeasure.Parametric.SecondaryTentFilteredResponse
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
@[expose] public section

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

section
variable {p N : ℕ} [hp : Fact p.Prime]

theorem u6_class_term {e : ℕ} (he : e + (p - 1) / 2 + 2 * N = p) (c : Fin (20 * N) → ZMod p)
    {i : ℕ} (hi : p ≤ i) :
    ((X - 1) ^ e * u6Q p N c).coeff i =
      (-1) ^ e * ((u6Y p N c).coeff i - (u6Y p N c).coeff (i - p)) := by
  have h1 : (X - 1 : (ZMod p)[X]) ^ e = C ((-1) ^ e) * (1 - X) ^ e := by
    rw [← neg_sub, neg_pow]; simp
  rw [h1, mul_assoc, u6_frobenius he, sub_mul, one_mul, coeff_C_mul, coeff_sub,
    coeff_X_pow_mul', ite_eq_left_iff.mpr (fun h => absurd hi h)]

/-- The five class-sum terms telescope. -/
theorem u6_class_sum {e : ℕ} (he : e + (p - 1) / 2 + 2 * N = p) (hp2 : p ≠ 2) (hN : 0 < N)
    (c : Fin (20 * N) → ZMod p) {μ : ℕ} (hμ1 : p + μ ≤ 8 * N) (hμ2 : 26 * N + (p - 1) / 2 < 6 * p + μ) :
    ((X - 1) ^ e * u6Q p N c).coeff (2 * p + μ) + ((X - 1) ^ e * u6Q p N c).coeff (3 * p + μ) +
      ((X - 1) ^ e * u6Q p N c).coeff (4 * p + μ) + ((X - 1) ^ e * u6Q p N c).coeff (5 * p + μ) +
      ((X - 1) ^ e * u6Q p N c).coeff (6 * p + μ) = 0 := by
  rw [u6_class_term he c (by omega), u6_class_term he c (by omega), u6_class_term he c (by omega),
    u6_class_term he c (by omega), u6_class_term he c (by omega)]
  rw [show 2 * p + μ - p = p + μ by omega, show 3 * p + μ - p = 2 * p + μ by omega,
    show 4 * p + μ - p = 3 * p + μ by omega, show 5 * p + μ - p = 4 * p + μ by omega,
    show 6 * p + μ - p = 5 * p + μ by omega]
  have h0 : (u6Y p N c).coeff (p + μ) = 0 := u6Y_coeff_zero hp2 hN c (by omega)
  have h6 : (u6Y p N c).coeff (6 * p + μ) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    have := u6Y_natDegree hp2 hN c
    omega
  rw [h0, h6]
  ring


theorem u6Col_eq_mulVec (hp2 : p ≠ 2) (hH : 27 * N < p ^ 2) (c : Fin (20 * N) → ZMod p)
    (k : Fin (20 * N)) :
    (scaledResidueMatrix (p := p) (Matrix.of fun r k : Fin (twenty.n N) =>
      filteredEntryRat twenty 0 N r.val k.val)).transpose.mulVecLin c k = u6Col p N k.val c := by
  have hH' : twenty.H N < p ^ 2 := by rw [twenty_H]; exact hH
  have hzp : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  change (∑ r : Fin (twenty.n N),
    palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat twenty 0 N r.val k.val) * c r) = _
  have hk : k.val < twenty.n N := k.isLt
  simp_rw [(filteredEntry_scaled_residue_sum_general hp2 hH' hk 0 hzp).2, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hq : twenty.q N = N := by simp [twenty, Parameters.q]
  have hb : twenty.b N = 3 * N := by simp [twenty, Parameters.b]
  unfold u6Col
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [hq]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [filterCoeff_residue, hq, hb, u3Resp]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring


theorem binom_filter_top {R : Type*} [CommRing R] (A : R[X]) {i e : ℕ} (hei : e ≤ i)
    (hz : ∀ v < e, A.coeff (i - e + v) = 0) :
    ((X - 1) ^ e * A).coeff i = (-1) ^ e * A.coeff i := by
  have h := binom_filter A (i - e) e
  rw [Nat.sub_add_cancel hei, Finset.sum_range_succ] at h
  rw [← h, Finset.sum_eq_zero (fun v hv => by rw [hz v (Finset.mem_range.mp hv), mul_zero])]
  simp [Nat.sub_add_cancel hei]

theorem u6_digits_zero {d : ℕ} (hN : 0 < N) (hp2 : p ≠ 2) (hd : p = 4 * N + d)
    (hdodd : d % 2 = 1) (hdN : 2 * d < N) (c : Fin (20 * N) → ZMod p)
    (h2a : ∀ u t, 2 ≤ u → u ≤ 5 → t < d → (u6Q p N c).coeff (u * p + (p - 7 * d + t)) = 0)
    (h2b : ∀ t, t < (d + 1) / 2 → (u6Q p N c).coeff (6 * p + (p - 7 * d + t)) = 0) :
    ∀ t, t < d → ∀ u, 2 ≤ u → u ≤ 6 → (u6Q p N c).coeff (u * p + (p - 7 * d + t)) = 0 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro htd u hu1 hu6
    by_cases hu5 : u ≤ 5
    · exact h2a u t hu1 hu5 htd
    have hu : u = 6 := by omega
    subst hu
    by_cases hte : t < (d + 1) / 2
    · exact h2b t hte
    have he : (d + 1) / 2 + (p - 1) / 2 + 2 * N = p := by omega
    have hcs := u6_class_sum he hp2 hN c (μ := p - 7 * d + t) (by omega) (by omega)
    have htop : ∀ u', 2 ≤ u' → u' ≤ 6 →
        ((X - 1) ^ ((d + 1) / 2) * u6Q p N c).coeff (u' * p + (p - 7 * d + t)) =
          (-1) ^ ((d + 1) / 2) * (u6Q p N c).coeff (u' * p + (p - 7 * d + t)) := by
      intro u' hu'1 hu'6
      apply binom_filter_top _ (by omega)
      intro v hv
      rw [show u' * p + (p - 7 * d + t) - (d + 1) / 2 + v =
        u' * p + (p - 7 * d + (t - (d + 1) / 2 + v)) by omega]
      exact ih (t - (d + 1) / 2 + v) (by omega) (by omega) u' hu'1 hu'6
    rw [htop 2 le_rfl (by norm_num), htop 3 (by norm_num) (by norm_num),
      htop 4 (by norm_num) (by norm_num), htop 5 (by norm_num) (by norm_num),
      htop 6 (by norm_num) le_rfl, h2a 2 t le_rfl (by norm_num) htd,
      h2a 3 t (by norm_num) (by norm_num) htd, h2a 4 t (by norm_num) (by norm_num) htd,
      h2a 5 t (by norm_num) (by norm_num) htd] at hcs
    have hu : ((-1 : ZMod p) ^ ((d + 1) / 2)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    simpa [hu] using hcs


/-- The linear map `c ↦ Q_c`. -/
def u6QLin (p N : ℕ) [Fact p.Prime] :
    (Fin (20 * N) → ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  (LinearMap.mulLeft (ZMod p) ((X - 1 : (ZMod p)[X]) ^ N)).comp
    ((LinearMap.mulLeft (ZMod p) (X * oddPrimeWeight p)).comp
      ((LinearMap.mulLeft (ZMod p) ((1 - X : (ZMod p)[X]) ^ N)).comp (u3S p N)))

theorem u6QLin_apply (c : Fin (20 * N) → ZMod p) : u6QLin p N c = u6Q p N c := rfl

/-- The columns of the filtered matrix occupied by the block. -/
def u6BlockCols (p N : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin 5 × Fin (p - 4 * N))).image fun x =>
    (x.1.val + 1) * p + (p - 7 * (p - 4 * N) + x.2.val) - 4 * N

/-- The remaining columns, each of which costs one constraint. -/
def u6FreeCols (p N : ℕ) : Finset ℕ := Finset.range (20 * N) \ u6BlockCols p N

omit hp in
theorem u6BlockCols_card (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) :
    (u6BlockCols p N).card = 5 * (p - 4 * N) := by
  unfold u6BlockCols
  rw [Finset.card_image_of_injective]
  · simp [Finset.card_univ]
  · rintro ⟨a, t⟩ ⟨a', t'⟩ h
    have ht := t.isLt
    have ht' := t'.isLt
    simp only at h
    have key : a = a' ∧ t = t' := by
      fin_cases a <;> fin_cases a' <;> simp at h ⊢ <;> omega
    rw [key.1, key.2]

omit hp in
theorem u6BlockCols_subset (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) :
    u6BlockCols p N ⊆ Finset.range (20 * N) := by
  intro k hk
  unfold u6BlockCols at hk
  obtain ⟨⟨a, t⟩, -, rfl⟩ := Finset.mem_image.mp hk
  have ht := t.isLt
  simp only [Finset.mem_range]
  fin_cases a <;> simp <;> omega

omit hp in
theorem u6FreeCols_card (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) :
    (u6FreeCols p N).card = 20 * N - 5 * (p - 4 * N) := by
  unfold u6FreeCols
  rw [Finset.card_sdiff_of_subset (u6BlockCols_subset h4 h9), Finset.card_range,
    u6BlockCols_card h4 h9]

/-- Costs of the three groups of constraints. -/
def u6Cost (p N : ℕ) : Fin 3 → ℕ
  | 0 => (u6FreeCols p N).card
  | 1 => 4 * (p - 4 * N)
  | 2 => (p - 4 * N + 1) / 2

def u6Constraint (p N : ℕ) [Fact p.Prime] :
    ∀ i : Fin 3, (Fin (20 * N) → ZMod p) →ₗ[ZMod p] (Fin (u6Cost p N i) → ZMod p)
  | 0 => LinearMap.pi fun a : Fin (u6FreeCols p N).card =>
      u6Col p N (((u6FreeCols p N).equivFin.symm a).val)
  | 1 => LinearMap.pi fun a : Fin (4 * (p - 4 * N)) =>
      (lcoeff (ZMod p) ((2 + a.val / (p - 4 * N)) * p +
        (p - 7 * (p - 4 * N) + a.val % (p - 4 * N)))).comp (u6QLin p N)
  | 2 => LinearMap.pi fun a : Fin ((p - 4 * N + 1) / 2) =>
      (lcoeff (ZMod p) (6 * p + (p - 7 * (p - 4 * N) + a.val))).comp (u6QLin p N)

theorem u6Cost_sum (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) (hodd : p % 2 = 1) :
    ∑ i, u6Cost p N i = 20 * N - (p - 4 * N - 1) / 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, u6Cost, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  rw [u6FreeCols_card h4 h9]
  omega


theorem u6_kernel_col (hN : 0 < N) (hp2 : p ≠ 2) (h4 : 4 * N < p) (h9 : 2 * p < 9 * N)
    (c : Fin (20 * N) → ZMod p) (hc : ∀ i, u6Constraint p N i c = 0) {k : ℕ} (hk : k < 20 * N) :
    u6Col p N k c = 0 := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  by_cases hkB : k ∈ u6BlockCols p N
  · obtain ⟨⟨a, t⟩, -, hk'⟩ := Finset.mem_image.mp hkB
    have ht0 := t.isLt
    have ha0 := a.isLt
    have hk2 : k = (a.val + 1) * p + (p - 7 * (p - 4 * N) + t.val) - 4 * N := hk'.symm
    rw [hk2]
    generalize t.val = t0 at ht0 ⊢
    generalize a.val = a0 at ha0 ⊢
    obtain ⟨d, hd⟩ : ∃ d, d = p - 4 * N := ⟨_, rfl⟩
    have hpd : p = 4 * N + d := by omega
    have hd0 : 0 < d := by omega
    have hdodd : d % 2 = 1 := by omega
    have hdN : 2 * d < N := by omega
    have ht : t0 < d := by omega
    have hall := u6_digits_zero hN hp2 hpd hdodd hdN c
      (by
        intro u t' hu1 hu5 ht'
        have hlt : t' + d * (u - 2) < 4 * d := by
          have := Nat.mul_le_mul_left d (show u - 2 ≤ 3 by omega)
          omega
        have key : (lcoeff (ZMod p) ((2 + (t' + d * (u - 2)) / (p - 4 * N)) * p +
            (p - 7 * (p - 4 * N) + (t' + d * (u - 2)) % (p - 4 * N)))).comp (u6QLin p N) c = 0 :=
          congrFun (hc 1) ⟨t' + d * (u - 2), by simp only [u6Cost]; omega⟩
        rw [← hd, Nat.add_mul_div_left _ _ hd0, Nat.div_eq_of_lt ht',
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht', zero_add,
          show 2 + (u - 2) = u by omega] at key
        exact key)
      (by
        intro t' ht'
        have key : (lcoeff (ZMod p) (6 * p + (p - 7 * (p - 4 * N) + t'))).comp (u6QLin p N) c = 0 :=
          congrFun (hc 2) ⟨t', by simp only [u6Cost]; omega⟩
        rw [← hd] at key
        exact key)
    rw [← hd]
    refine u6Col_block_zero hN hp2 h4 h9 (J := a0 + 1) (μ := p - 7 * d + t0) (by omega)
      (by omega) (by omega) (by omega) c ?_
    intro u hu1 hu6
    exact hall t0 ht u hu1 hu6
  · have hkF : k ∈ u6FreeCols p N := by
      unfold u6FreeCols
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hk, hkB⟩
    have key : u6Col p N (((u6FreeCols p N).equivFin.symm
        ((u6FreeCols p N).equivFin ⟨k, hkF⟩)).val) c = 0 :=
      congrFun (hc 0) ((u6FreeCols p N).equivFin ⟨k, hkF⟩)
    simpa using key

/-- The canonical rank bound of Lemma U6. -/
theorem u6_canonical_rank (hN : 0 < N) (h4 : 4 * N < p) (h9 : 2 * p < 9 * N) :
    (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank + (p - 4 * N - 1) / 2 ≤
      20 * N := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hH : 27 * N < p ^ 2 := u6_27N_lt_sq h4 h9
  let J : LinearMap.ker (secondaryTentConstraintMap (u6Cost p N) (u6Constraint p N)) →ₗ[ZMod p]
      (Fin (twenty.n N) → ZMod p) := Submodule.subtype _
  have hr := secondaryTent_rank_of_constraints
    (scaledResidueMatrix (p := p) (Matrix.of fun r k : Fin (twenty.n N) =>
      filteredEntryRat twenty 0 N r.val k.val))
    (u6Cost p N) (u6Constraint p N) J Subtype.val_injective (by
      intro v
      funext k
      have hv := (secondaryTentConstraintMap_eq_zero_iff _ _ v.1).mp v.2

      exact (u6Col_eq_mulVec hp2 hH (J v) k).trans (u6_kernel_col hN hp2 h4 h9 v.1 hv k.isLt))
  rw [u6Cost_sum h4 h9 hodd, Module.finrank_fin_fun] at hr
  have e : 20 * N - (20 * N - (p - 4 * N - 1) / 2) = (p - 4 * N - 1) / 2 := by omega
  change _ + (20 * N - (20 * N - (p - 4 * N - 1) / 2)) ≤ 20 * N at hr
  rw [e] at hr
  exact hr

end

end
end CatalanMeasure.Parametric
