module

public import OAI.NumberTheory.ZetaFive.Identities.RiemannSqueeze

@[expose] public section

namespace OAI

open Filter Finset
open scoped Topology

namespace Zeta5.Workers.W14

noncomputable def affineGrid (a b : ℝ) (n i : ℕ) : ℝ :=
  a + (b - a) / n * i

noncomputable def affineLower (a b m c D : ℝ) (n i : ℕ) : ℝ :=
  m * affineGrid a b n i + c - if i = n - 1 then D else 0

noncomputable def affineUpper (a b m c D : ℝ) (n i : ℕ) : ℝ :=
  m * affineGrid a b n (i + 1) + c + if i = n - 1 then D else 0

theorem grid_zero (a b : ℝ) (n : ℕ) : affineGrid a b n 0 = a := by
  simp [affineGrid]

theorem grid_end (a b : ℝ) {n : ℕ} (hn : 0 < n) : affineGrid a b n n = b := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold affineGrid
  rw [div_mul_cancel₀ _ hn']
  ring

theorem grid_width (a b : ℝ) (n i : ℕ) :
    affineGrid a b n (i + 1) - affineGrid a b n i = (b - a) / n := by
  simp only [affineGrid, Nat.cast_add, Nat.cast_one]
  ring

theorem grid_strict {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) :
    StrictMono (affineGrid a b n) := by
  intro i j hij
  unfold affineGrid
  exact add_lt_add_of_le_of_lt le_rfl
    (mul_lt_mul_of_pos_left (by exact_mod_cast hij)
      (div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)))

theorem affine_cell_envelopes {F : ℝ → ℝ} {a b m c D : ℝ}
    (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    {n : ℕ} (hn : 0 < n) :
    ∀ i < n, ∀ x ∈ Set.Ioc (affineGrid a b n i) (affineGrid a b n (i + 1)),
      affineLower a b m c D n i ≤ F x ∧ F x ≤ affineUpper a b m c D n i := by
  intro i hi x hx
  have hg := grid_strict hab hn
  have hxlo : a < x := by
    have h := hg.monotone (Nat.zero_le i)
    rw [grid_zero] at h
    exact h.trans_lt hx.1
  have hxhi : x ≤ b := by
    have h := hg.monotone (show i + 1 ≤ n by omega)
    rw [grid_end a b hn] at h
    exact hx.2.trans h
  have hcorr : 0 ≤ (if i = n - 1 then D else 0) := by split_ifs <;> positivity
  by_cases hxb : x < b
  · rw [hpiece x hxlo hxb]
    unfold affineLower affineUpper
    constructor
    · have h := mul_le_mul_of_nonneg_left hx.1.le hm
      linarith
    · have h := mul_le_mul_of_nonneg_left hx.2 hm
      linarith
  · have heq : x = b := le_antisymm hxhi (le_of_not_gt hxb)
    have hiend : i = n - 1 := by
      by_contra hne
      have hin : i + 1 < n := by omega
      have hglt := hg hin
      rw [grid_end a b hn] at hglt
      exact (not_lt_of_ge (heq ▸ hx.2)) hglt
    have hright : affineGrid a b n (i + 1) = b := by
      have hin : i + 1 = n := by omega
      rw [hin, grid_end a b hn]
    have hmlo := mul_le_mul_of_nonneg_left hx.1.le hm
    have he := abs_le.mp hend
    subst x
    simp only [affineLower, affineUpper, ite_eq_left hiend, hright]
    constructor <;> linarith

theorem affine_envelope_gap (a b m c D : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
      ((affineUpper a b m c D n i - affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i))) =
      (m * (b - a) ^ 2 + 2 * D * (b - a)) / n := by
  classical
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlast : n - 1 ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  simp only [grid_width]
  have heq : ∀ i : ℕ,
      (affineUpper a b m c D n i - affineLower a b m c D n i) * ((b - a) / n) =
        m * ((b - a) / n) ^ 2 + (if i = n - 1 then 2 * D * ((b - a) / n) else 0) := by
    intro i
    unfold affineUpper affineLower affineGrid
    simp only [Nat.cast_add, Nat.cast_one]
    split_ifs <;> ring
  simp_rw [heq, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_ite_eq', ite_eq_left hlast]
  field_simp [hn']

theorem affine_envelope_balance (a b m c D : ℝ) {n : ℕ} (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
      ((affineUpper a b m c D n i + affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i))) =
      2 * (m * (b ^ 2 - a ^ 2) / 2 + c * (b - a)) := by
  let P : ℝ → ℝ := fun x => m * x ^ 2 / 2 + c * x
  have heq : ∀ i : ℕ,
      (affineUpper a b m c D n i + affineLower a b m c D n i) *
        (affineGrid a b n (i + 1) - affineGrid a b n i) =
      2 * (P (affineGrid a b n (i + 1)) - P (affineGrid a b n i)) := by
    intro i
    dsimp [affineUpper, affineLower, P]
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum,
    Finset.sum_range_sub (fun i => P (affineGrid a b n i)) n,
    grid_end a b hn, grid_zero]
  dsimp [P]
  ring

theorem affine_piece_darboux {F : ℝ → ℝ} {a b m c D : ℝ}
    (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    (hIntegral : (∫ x in a..b, F x) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a)) :
    ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (p l u : ℕ → ℝ),
      Monotone p ∧ p 0 = a ∧ p n = b ∧
      (∀ i < n, p i < p (i + 1)) ∧
      (∀ i < n, ∀ x ∈ Set.Ioc (p i) (p (i + 1)), l i ≤ F x ∧ F x ≤ u i) ∧
      (∫ x in a..b, F x) - ε < ∑ i ∈ Finset.range n, l i * (p (i + 1) - p i) ∧
      (∑ i ∈ Finset.range n, u i * (p (i + 1) - p i)) < (∫ x in a..b, F x) + ε := by
  intro ε hε
  let K := m * (b - a) ^ 2 + 2 * D * (b - a)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (K / ε))
  have hn0 : 0 < n := by
    have h : (0 : ℝ) < n := lt_trans (by norm_num) ((le_max_left _ _).trans_lt hn)
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hgap : K / n < ε := by
    apply (div_lt_iff₀ hnR).mpr
    have h := (le_max_right (1 : ℝ) (K / ε)).trans_lt hn
    have h' := (div_lt_iff₀ hε).mp h
    nlinarith
  refine ⟨n, affineGrid a b n, affineLower a b m c D n,
    affineUpper a b m c D n, (grid_strict hab hn0).monotone,
    grid_zero a b n, grid_end a b hn0, ?_,
    affine_cell_envelopes hab hm hD hpiece hend hn0, ?_, ?_⟩
  · intro i _
    exact grid_strict hab hn0 (Nat.lt_succ_self i)
  · have hg := affine_envelope_gap a b m c D hn0
    have hb := affine_envelope_balance a b m c D hn0
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hg hb
    rw [hIntegral]
    dsimp [K] at hgap
    linarith
  · have hg := affine_envelope_gap a b m c D hn0
    have hb := affine_envelope_balance a b m c D hn0
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hg hb
    rw [hIntegral]
    dsimp [K] at hgap
    linarith

theorem weighted_affine_piece_tendsto {F : ℝ → ℝ} {a b m c D : ℝ}
    (ha : 0 < a) (hab : a < b) (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hpiece : ∀ x, a < x → x < b → F x = m * x + c)
    (hend : |F b - (m * b + c)| ≤ D)
    (hIntegral : (∫ x in a..b, F x) = m * (b ^ 2 - a ^ 2) / 2 + c * (b - a))
    (hPNT : Tendsto (fun R : ℝ => Chebyshev.theta R / R) atTop (𝓝 1)) :
    Tendsto (weightedPrimeIntervalSum F a b) atTop (𝓝 (∫ x in a..b, F x)) := by
  exact weightedPrimeIntervalSum_tendsto_of_darboux ha hab hPNT
    (affine_piece_darboux hab hm hD hpiece hend hIntegral)

end Zeta5.Workers.W14

end OAI
