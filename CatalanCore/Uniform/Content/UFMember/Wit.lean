module

public import CatalanCore.Uniform.Content.UFMember.Minor
public import CatalanCore.Arith.Hybrid.TwoLevelCauchy
public import CatalanCore.Uniform.Content.Smith.Derived

@[expose] public section

/-!
# UF member package, step 1c: member prices from the FULL matrix's leading data

Instantiation of `two_level_dvd_det_submatrix` at `φ = phiP p`, `π = p`.

* `TwoLevelWit.gle_submatrix`: a two-level witness of `M` prices every minor
  `M[e₁, e₂]` (`k` rows and `k` columns deleted, any positions) at
  `Σ u∘e₁ + Σ v∘e₂ - (a + (a - b))`, `a = |s| - k`.
* `LeadingData.gle_det_submatrix`: with the leading data of `Φ` (UC4), every minor of `Φ` has
  `denexp_p ≤ 2h - |s| - G`, i.e. exactly the full matrix's price (`LeadingData.gle_det`):
  **debit 0** for every deletion.
* `LeadingData.gle_det_uf_submatrix`: Theorem UF (`gle_det_uf`) for every minor, same price.
* `ufMember_gle_of_full`: the deletion member `FullN Fr (common|S) xs ys` gets the full
  matrix's UF price.  So the member needs NO leading data of its own: H6's `ufMember_gle`
  hypothesis "member `LeadingData`" is discharged by the full matrix's `LeadingData`.

This is the level-2 form of Theorem SD of `smith-deletion/THEOREM.md` (whose level-3 statement
carries a debit `k`); the Lean statement needs no Smith form and no length function.
-/

open Polynomial Matrix Finset CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMember

variable {p : ℕ} [Fact p.Prime]

variable (p) in
/-- Every element of `𝔽_p(X)` is a quotient of reductions. -/
theorem phiP_lift (z : RatFunc (ZMod p)) :
    ∃ r d : (LocRing p)[X], phiP p d ≠ 0 ∧ phiP p r = phiP p d * z := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := (ZMod p)[X]) z
  have hsurj : Function.Surjective (redQ p) := fun a => ⟨liftZ p a, redQ_liftZ p a⟩
  obtain ⟨x', hx'⟩ := Polynomial.map_surjective (redQ p) hsurj x
  obtain ⟨y', hy'⟩ := Polynomial.map_surjective (redQ p) hsurj y
  have hphi : ∀ (g : (LocRing p)[X]) (g' : (ZMod p)[X]), g.map (redQ p) = g' →
      phiP p g = algebraMap (ZMod p)[X] (RatFunc (ZMod p)) g' := by
    intro g g' h; rw [← h]; rfl
  have hy0 : algebraMap (ZMod p)[X] (RatFunc (ZMod p)) y ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (ZMod p)[X] (RatFunc (ZMod p)))]
    exact nonZeroDivisors.ne_zero hy
  refine ⟨x', y', by rw [hphi _ _ hy']; exact hy0, ?_⟩
  rw [hphi _ _ hx', hphi _ _ hy']
  field_simp

/-- **A two-level witness prices every minor.** -/
theorem _root_.CatalanCore.Arith.Hybrid.TwoLevelWit.gle_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {M : Matrix ι ι ℚ[X]} {b : ℕ} (W : TwoLevelWit p M b) (e₁ e₂ : κ → ι)
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂) :
    GLE p (∑ v, W.u (e₁ v) + ∑ v, W.v (e₂ v) -
      ((W.s.card + Fintype.card κ - Fintype.card ι) +
        ((W.s.card + Fintype.card κ - Fintype.card ι) - b))) (M.submatrix e₁ e₂).det := by
  have hdvd := two_level_dvd_det_submatrix (phiP p) (Polynomial.prime_C_iff.2 (prime_p p))
    (phiP_eq_zero_iff p) (phiP_lift p) W.Bl W.L W.P W.hL W.hP W.s W.hrow W.hcol
    (Matrix.of fun i j : W.s => quotP p ((W.L * W.Bl * W.P) i j))
    (fun i j => (quotP_spec p (W.hrow i i.2 j)).symm) b W.hH e₁ e₂ he₁ he₂
  exact gle_det_of_scaled_dvd p (M.submatrix e₁ e₂) (W.Bl.submatrix e₁ e₂)
    (fun v => W.u (e₁ v)) (fun v => W.v (e₂ v)) (fun i j => W.hB _ _) _ hdvd

/-- **UC4 for minors, debit 0.**  Every minor of `Φ` (delete `k` rows and `k` columns) has the
price `2h - |s| - G` of the full matrix. -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Φ : Matrix ι ι ℚ[X]} (D : LeadingData p Φ) (G : ℕ)
    (hG : D.nextRed.rank + G ≤ D.s.card) (e₁ e₂ : κ → ι)
    (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂) :
    GLE p (2 * Fintype.card ι - D.s.card - G) (Φ.submatrix e₁ e₂).det := by
  have h := TwoLevelWit.gle_submatrix (D.toWit (D.s.card - G) (by omega)) e₁ e₂ he₁ he₂
  have hk : Fintype.card κ ≤ Fintype.card ι := Fintype.card_le_of_injective e₁ he₁
  refine h.mono ?_
  simp only [LeadingData.toWit, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

/-- The rank of `M_next mod p` when it is the weighted Cauchy matrix of retained poles. -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.rank_le_of_uf {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Φ : Matrix ι ι ℚ[X]} (D : LeadingData p Φ) (v : ZMod p → ZMod p) (I Kill : Finset (ZMod p))
    (mR mC ρ σ : D.s → ZMod p)
    (hI : ∀ c ∈ I, v c = 0) (hKill : ∀ c ∈ Kill, v c = 0)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹))) :
    D.nextRed.rank ≤ p - (I ∪ Kill).card := by
  classical
  have hsupp : ∀ c, c ∉ (univ \ (I ∪ Kill) : Finset (ZMod p)) → v c = 0 := by
    intro c hc
    simp only [mem_sdiff, mem_univ, true_and, not_not, mem_union] at hc
    rcases hc with h | h
    · exact hI c h
    · exact hKill c h
  have hcard : (univ \ (I ∪ Kill) : Finset (ZMod p)).card = p - (I ∪ Kill).card := by
    rw [Finset.card_sdiff_of_subset (subset_univ _), Finset.card_univ, ZMod.card]
  have hsum : ∀ i j, ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹) =
      ∑ c ∈ univ \ (I ∪ Kill), v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹) := fun i j =>
    (Finset.sum_subset (subset_univ _) (fun c _ hc => by rw [hsupp c hc]; simp)).symm
  rw [← hcard]
  refine rank_le_card_of_sum _ D.nextRed (fun r c => rfH p (mR r * (c - ρ r)⁻¹))
    (fun c s => rfH p (v c * (c - σ s)⁻¹ * mC s)) fun r s => ?_
  rw [hnext r s, hsum r s, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← map_mul]; congr 1; ring

/-- **Theorem UF for every minor**, at the full matrix's price (debit 0). -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_uf_submatrix {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {Φ : Matrix ι ι ℚ[X]} (D : LeadingData p Φ) (R0 : ℕ)
    (hR : R0 + D.s.card = Fintype.card ι) (v : ZMod p → ZMod p) (I Kill : Finset (ZMod p))
    (mR mC ρ σ : D.s → ZMod p)
    (hI : ∀ c ∈ I, v c = 0) (hKill : ∀ c ∈ Kill, v c = 0)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹)))
    (e₁ e₂ : κ → ι) (he₁ : Function.Injective e₁) (he₂ : Function.Injective e₂) :
    GLE p (Fintype.card ι + R0 - (D.s.card - (p - (I ∪ Kill).card)))
      (Φ.submatrix e₁ e₂).det := by
  have hrk := D.rank_le_of_uf v I Kill mR mC ρ σ hI hKill hnext
  have hs : D.nextRed.rank ≤ D.s.card := by simpa using Matrix.rank_le_card_width D.nextRed
  have h := D.gle_det_submatrix (D.s.card - (p - (I ∪ Kill).card)) (by omega) e₁ e₂ he₁ he₂
  refine h.mono ?_
  omega

end CatalanCore.Uniform.Content.UFMember
