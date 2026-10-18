import CatalanLambda.Decay.ThmNEnergy

/-!
# Theorem N_ρ, stage 3d: completing the node set (identities (a), (b) of BN §1.2)
-/

open Finset

namespace CatalanLambda.Decay

/-- The indicator (as a real number) of the removed nodes. -/
noncomputable def rmask {h k : ℕ} (s : Fin k → Fin h) (b : Fin h) : ℝ :=
  if b ∈ (univ : Finset (Fin k)).image s then 0 else 1

lemma rmask_cases {h k : ℕ} (s : Fin k → Fin h) (b : Fin h) : rmask s b = 0 ∨ rmask s b = 1 := by
  unfold rmask; split_ifs <;> simp

lemma sum_mask {h k : ℕ} (s : Fin k → Fin h) (hs : Function.Injective s) (f : Fin h → ℝ) :
    ∑ i, f (s i) = ∑ b, (1 - rmask s b) * f b := by
  have h1 : ∑ i, f (s i) = ∑ b ∈ (univ : Finset (Fin k)).image s, f b :=
    (Finset.sum_image (fun i _ j _ hij => hs hij)).symm
  have h2 : ∀ b, (1 - rmask s b) * f b = if b ∈ (univ : Finset (Fin k)).image s then f b else 0 := by
    intro b; unfold rmask; split_ifs <;> simp
  rw [h1, Finset.sum_congr rfl (fun b _ => h2 b), ← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

theorem Hsc_decomp {h k : ℕ} (σ : Fin k → ℂ) (τ : Fin h → ℂ) (s : Fin k → Fin h)
    (hs : Function.Injective s) :
    ∑ l, ∑ l', elog (σ l) (σ l') + ∑ i, ∑ i', elog (τ (s i)) (τ (s i'))
        - 2 * ∑ l, ∑ i, elog (σ l) (τ (s i))
      = (∑ l, ∑ l', elog (σ l) (σ l') + 2 * ∑ l, ∑ b, rmask s b * elog (σ l) (τ b)
          + ∑ b, ∑ b', rmask s b * rmask s b' * elog (τ b) (τ b'))
        + ∑ b, ∑ b', elog (τ b) (τ b')
        - 2 * ∑ l, ∑ b, elog (σ l) (τ b)
        - 2 * ∑ b, ∑ b', rmask s b * elog (τ b) (τ b') := by
  set r := rmask s with hr
  have hA : ∑ i, ∑ i', elog (τ (s i)) (τ (s i'))
      = ∑ b, ∑ b', (1 - r b) * (1 - r b') * elog (τ b) (τ b') := by
    have h1 : ∀ i, ∑ i', elog (τ (s i)) (τ (s i'))
        = ∑ b', (1 - r b') * elog (τ (s i)) (τ b') := fun i =>
      sum_mask s hs (fun b' => elog (τ (s i)) (τ b'))
    simp_rw [h1]
    rw [sum_mask s hs (fun b => ∑ b', (1 - r b') * elog (τ b) (τ b'))]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    ring
  have hB : ∑ l, ∑ i, elog (σ l) (τ (s i)) = ∑ l, ∑ b, (1 - r b) * elog (σ l) (τ b) :=
    Finset.sum_congr rfl (fun l _ => sum_mask s hs (fun b => elog (σ l) (τ b)))
  have hsw : ∑ b, ∑ b', r b' * elog (τ b) (τ b') = ∑ b, ∑ b', r b * elog (τ b) (τ b') := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [elog_comm]
  have hexp : ∑ b, ∑ b', (1 - r b) * (1 - r b') * elog (τ b) (τ b')
      = ∑ b, ∑ b', elog (τ b) (τ b') - ∑ b, ∑ b', r b' * elog (τ b) (τ b')
        - ∑ b, ∑ b', r b * elog (τ b) (τ b') + ∑ b, ∑ b', r b * r b' * elog (τ b) (τ b') := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun b' _ => ?_))
    ring
  have hexp2 : ∑ l, ∑ b, (1 - r b) * elog (σ l) (τ b)
      = ∑ l, ∑ b, elog (σ l) (τ b) - ∑ l, ∑ b, r b * elog (σ l) (τ b) := by
    simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [hA, hB, hexp, hexp2, hsw]
  ring

end CatalanLambda.Decay
