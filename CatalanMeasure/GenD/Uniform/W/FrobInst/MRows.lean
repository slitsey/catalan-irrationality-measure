module
public import CatalanMeasure.GenD.Uniform.W.FrobInst.HRows
@[expose] public section
set_option Elab.async false

/-!
# Row evaluations of the `C` and `H+` pair families

For a row `r` at Laurent exponent `(k0 + k) p ± s` (`1 ≤ s`, `2 s < p`):

* `C` rows (`tRows`): `tRows x r = ± x (s-1) k` (`pair_eval`, `pair_eval_minus`);
* `H+` rows (`hRows`): `hRows ρ r = ρ s k` on the `+` row and `ρ s (k-1)` on the `-` row
  (zero when the block does not exist).

These give the row-level independence of the `C` atoms from the `H+` atoms used for injectivity.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem pair_eval_minus {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (d : Fin D) (k : Fin K) (r : Fin (P.n N))
    (hr : (r : ℤ) - P.g N = cen p K k0 k - ((d : ℕ) + 1)) :
    tRows P N p K D k0 x r = - x d k := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le; omega
  have hdl := d.isLt
  have hp1 : (0 : ℤ) < p := by omega
  rw [tRows_apply, Finset.sum_eq_single d]
  · rw [Finset.sum_eq_single k]
    · unfold pairRow
      rw [if_neg, if_pos hr]
      · simp
      · intro h
        rw [hr] at h
        omega
    · intro k2 _ hk2
      unfold pairRow
      have hn1 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 + ((d : ℕ) + 1)) := by
        intro h
        unfold cen at h hr
        have h5 : (((k2 : ℕ) : ℤ) - (k : ℕ)) * p = -2 * ((d : ℕ) + 1) := by nlinarith
        have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
        omega
      have hn2 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 - ((d : ℕ) + 1)) := by
        intro h
        unfold cen at h hr
        have h4 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = 0 := by nlinarith
        have h5 := (no_mult _ 0 hp1 (by omega) (by omega) h4).1
        exact hk2 (Fin.ext (by omega))
      rw [if_neg hn1, if_neg hn2]; simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro d2 _ hd2
    refine Finset.sum_eq_zero fun k2 _ => ?_
    unfold pairRow
    have hd2l := d2.isLt
    have hn1 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 + ((d2 : ℕ) + 1)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k2 : ℕ) : ℤ) - (k : ℕ)) * p = -(((d : ℕ) : ℤ) + 1) - ((d2 : ℕ) + 1) := by
        nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      omega
    have hn2 : ¬ ((r : ℤ) - P.g N = cen p K k0 k2 - ((d2 : ℕ) + 1)) := by
      intro h
      unfold cen at h hr
      have h5 : (((k : ℕ) : ℤ) - (k2 : ℕ)) * p = ((d : ℕ) : ℤ) - (d2 : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      apply hd2
      apply Fin.ext
      omega
    rw [if_neg hn1, if_neg hn2]; simp
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `H+` rows on the `+` row of block `k0 + kk` at distance `s`. -/
theorem hRows_eval_plus {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (s : ℕ) (hs : s < D) (hs1 : 1 ≤ s) (kk : ℕ)
    (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = (k0 + kk) * p + s) :
    hRows P N p K D k0 x r = if h : kk < K then x ⟨s, hs⟩ ⟨kk, h⟩ else 0 := by
  have hodd := native_half_identity hp2
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  rw [hRows_apply]
  have key : ∀ (j : Fin D) (k : Fin K), pairRowH P N p k0 (j : ℕ) k r =
      if (j : ℕ) = s ∧ (k : ℕ) = kk then 1 else 0 := by
    intro j k
    have hj := j.isLt
    unfold pairRowH
    have c1 : ((r : ℤ) - P.g N = (k0 + (k : ℕ)) * p + (j : ℕ)) ↔ ((j : ℕ) = s ∧ (k : ℕ) = kk) := by
      constructor
      · intro h
        rw [hr] at h
        have h5 : (((kk : ℕ) : ℤ) - (k : ℕ)) * p = ((j : ℕ) : ℤ) - s := by nlinarith
        have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
        omega
      · rintro ⟨h1, h2⟩
        rw [hr, h1, h2]
    have c2 : ¬ ((r : ℤ) - P.g N = (k0 + (k : ℕ) + 1) * p - (j : ℕ)) := by
      intro h
      rw [hr] at h
      have h5 : (((k : ℕ) : ℤ) + 1 - kk) * p = (s : ℤ) + (j : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      omega
    by_cases hc : (j : ℕ) = s ∧ (k : ℕ) = kk
    · rw [if_pos (c1.mpr hc), if_neg c2, if_pos hc]; simp
    · rw [if_neg (fun h => hc (c1.mp h)), if_neg c2, if_neg hc]; simp
  simp_rw [key]
  by_cases hk' : kk < K
  · rw [dif_pos hk', Finset.sum_eq_single ⟨s, hs⟩]
    · rw [Finset.sum_eq_single ⟨kk, hk'⟩]
      · simp
      · intro k _ hk
        have : (k : ℕ) ≠ kk := fun h => hk (Fin.ext h)
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro j _ hj
      have : (j : ℕ) ≠ s := fun h => hj (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hk']
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    have : (k : ℕ) ≠ kk := fun h => hk' (h ▸ k.isLt)
    simp [this]

/-- `H+` rows on the `-` row of block `k0 + kk` at distance `s`. -/
theorem hRows_eval_minus {K D : ℕ} (hp2 : p ≠ 2) (hD : D ≤ (p - 1) / 2 + 1) (k0 : ℤ)
    (x : Fin D → Fin K → ZMod p) (s : ℕ) (hs : s < D) (hs1 : 1 ≤ s) (kk : ℕ)
    (r : Fin (P.n N)) (hr : (r : ℤ) - P.g N = (k0 + kk) * p - s) :
    hRows P N p K D k0 x r =
      if h : 1 ≤ kk ∧ kk - 1 < K then x ⟨s, hs⟩ ⟨kk - 1, h.2⟩ else 0 := by
  have hodd := native_half_identity hp2
  have hp1 : (0 : ℤ) < p := by
    have := (Fact.out : p.Prime).pos; exact_mod_cast this
  rw [hRows_apply]
  have key : ∀ (j : Fin D) (k : Fin K), pairRowH P N p k0 (j : ℕ) k r =
      if (j : ℕ) = s ∧ (k : ℕ) + 1 = kk then 1 else 0 := by
    intro j k
    have hj := j.isLt
    unfold pairRowH
    have c1 : ¬ ((r : ℤ) - P.g N = (k0 + (k : ℕ)) * p + (j : ℕ)) := by
      intro h
      rw [hr] at h
      have h5 : (((kk : ℕ) : ℤ) - (k : ℕ)) * p = (s : ℤ) + (j : ℕ) := by nlinarith
      have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
      omega
    have c2 : ((r : ℤ) - P.g N = (k0 + (k : ℕ) + 1) * p - (j : ℕ)) ↔
        ((j : ℕ) = s ∧ (k : ℕ) + 1 = kk) := by
      constructor
      · intro h
        rw [hr] at h
        have h5 : (((kk : ℕ) : ℤ) - (k : ℕ) - 1) * p = (s : ℤ) - (j : ℕ) := by nlinarith
        have h6 := no_mult _ _ hp1 (by omega) (by omega) h5
        omega
      · rintro ⟨h1, h2⟩
        rw [hr, h1, ← h2]
        push_cast
        ring
    by_cases hc : (j : ℕ) = s ∧ (k : ℕ) + 1 = kk
    · rw [if_neg c1, if_pos (c2.mpr hc), if_pos hc]; simp
    · rw [if_neg c1, if_neg (fun h => hc (c2.mp h)), if_neg hc]; simp
  simp_rw [key]
  by_cases hk' : 1 ≤ kk ∧ kk - 1 < K
  · rw [dif_pos hk', Finset.sum_eq_single ⟨s, hs⟩]
    · rw [Finset.sum_eq_single ⟨kk - 1, hk'.2⟩]
      · have : (kk - 1) + 1 = kk := by omega
        simp [this]
      · intro k _ hk
        have : (k : ℕ) + 1 ≠ kk := by
          intro h; apply hk; apply Fin.ext; simp only; omega
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro j _ hj
      have : (j : ℕ) ≠ s := fun h => hj (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [dif_neg hk']
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    have : (k : ℕ) + 1 ≠ kk := by
      intro h; apply hk'; refine ⟨by omega, ?_⟩
      have := k.isLt; omega
    simp [this]

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
