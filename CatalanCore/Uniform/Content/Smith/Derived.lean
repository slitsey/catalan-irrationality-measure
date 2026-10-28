module

public import CatalanCore.Uniform.Content.Hybrid.Price

@[expose] public section

/-!
# The level-2 Smith formula (Theorem UF): derived-frame Loewner matrices and the price

On `J`-supported kernels the next-level matrix `M_next mod p` (H1: `LeadingData.nextRed`) is a
weighted Cauchy sum over the residues `c` of the pole cells,

  `T_zy = m_z m'_y Σ_c v(c) / ((c - z)(c - y))`   (sum over `c ≠ z, y`: `x⁻¹ = 0` at `x = 0`),

that is, the Loewner matrix of the derived frame with poles `{c : v(c) ≠ 0}` and residues `v(c)`.
Hence its rank is at most the number of retained poles (`rank_cauchyMat_le`), and `LeadingData.gle_det_R0`
turns this into a `p`-adic price (`LeadingData.gle_det_derived`).

* `rank_le_card_of_sum`: a matrix factoring through a finite set `T` has rank `≤ |T|`.
* `rank_cauchyMat_le`: rank of the weighted Cauchy matrix `≤ #{c : v(c) ≠ 0}`.
* `loewner_of_loads`: loads `(m, m·h(z))` with `h(z) = Σ_c v(c)/(c - z)` give the derived Loewner entry.
* `LeadingData.gle_det_derived`, `LeadingData.gle_det_uf`: the UF price; the retained set is the
  complement of the zero-weight set `I_J` (and of any wedge-killed residues).
* `gle_det_hybrid_uf`: composition with H1's price through `gle_det_min`.
-/

open Finset Matrix Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.Smith

section Cauchy

variable {K : Type*} [Field K] {R S C : Type*} [Fintype R] [Fintype S]

/-- A matrix factoring through a finite set `T` has rank at most `|T|`. -/
theorem rank_le_card_of_sum (T : Finset C) (M : Matrix R S K) (A : R → C → K) (B : C → S → K)
    (h : ∀ r s, M r s = ∑ c ∈ T, A r c * B c s) : M.rank ≤ T.card := by
  classical
  let A' : Matrix R T K := Matrix.of fun r c => A r c
  let B' : Matrix T S K := Matrix.of fun c s => B c s
  have hM : M = A' * B' := by
    ext r s
    rw [h r s, Matrix.mul_apply]
    exact (Finset.sum_coe_sort T fun c => A r c * B c s).symm
  rw [hM]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  simpa using Matrix.rank_le_card_width A'

/-- The weighted Cauchy (derived-Loewner) matrix of residues. -/
def cauchyMat (Ret : Finset K) (v : K → K) (mR : R → K) (z : R → K) (mC : S → K) (y : S → K) :
    Matrix R S K :=
  Matrix.of fun r s => mR r * mC s * ∑ c ∈ Ret, v c * ((c - z r)⁻¹ * (c - y s)⁻¹)

/-- **The next level has rank at most the number of retained poles.** -/
theorem rank_cauchyMat_le (Ret : Finset K) (v : K → K) (mR : R → K) (z : R → K) (mC : S → K)
    (y : S → K) : (cauchyMat Ret v mR z mC y).rank ≤ Ret.card := by
  refine rank_le_card_of_sum Ret _ (fun r c => mR r * (c - z r)⁻¹)
    (fun c s => v c * (c - y s)⁻¹ * mC s) fun r s => ?_
  simp only [cauchyMat, Matrix.of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- Zero-weight poles may be dropped. -/
theorem rank_cauchyMat_le_support [DecidableEq K] (Ret : Finset K) (v : K → K) (mR : R → K)
    (z : R → K) (mC : S → K) (y : S → K) :
    (cauchyMat Ret v mR z mC y).rank ≤ (Ret.filter (fun c => v c ≠ 0)).card := by
  have h : cauchyMat Ret v mR z mC y = cauchyMat (Ret.filter (fun c => v c ≠ 0)) v mR z mC y := by
    ext r s
    simp only [cauchyMat, Matrix.of_apply]
    congr 1
    refine (Finset.sum_filter_of_ne ?_).symm
    intro c _ hc h0
    exact hc (by rw [h0, zero_mul])
  rw [h]
  exact rank_cauchyMat_le _ _ _ _ _ _

/-- **Derived frame.** Loads `(m, m·h(z))` with `h(z) = Σ_c v(c)/(c - z)`: the compressed Loewner entry
`ω(x_z, y_y)/(y - z)` is `m m' Σ_c v(c)/((c-z)(c-y))`, provided no weighted pole sits at `z` or `y`. -/
theorem loewner_of_loads (Ret : Finset K) (v : K → K) {z y m m' : K} (hzy : z ≠ y)
    (hz : ∀ c ∈ Ret, v c ≠ 0 → c ≠ z) (hy : ∀ c ∈ Ret, v c ≠ 0 → c ≠ y) :
    (m * (m' * ∑ c ∈ Ret, v c * (c - y)⁻¹) - (m * ∑ c ∈ Ret, v c * (c - z)⁻¹) * m') / (y - z) =
      m * m' * ∑ c ∈ Ret, v c * ((c - z)⁻¹ * (c - y)⁻¹) := by
  have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
  have hterm : ∀ c ∈ Ret, v c * (c - y)⁻¹ - v c * (c - z)⁻¹ =
      (y - z) * (v c * ((c - z)⁻¹ * (c - y)⁻¹)) := by
    intro c hc
    by_cases hv : v c = 0
    · simp [hv]
    · have h1 : c - z ≠ 0 := sub_ne_zero.2 (hz c hc hv)
      have h2 : c - y ≠ 0 := sub_ne_zero.2 (hy c hc hv)
      field_simp
      ring
  have hsum : ∑ c ∈ Ret, v c * (c - y)⁻¹ - ∑ c ∈ Ret, v c * (c - z)⁻¹ =
      (y - z) * ∑ c ∈ Ret, v c * ((c - z)⁻¹ * (c - y)⁻¹) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have : m * (m' * ∑ c ∈ Ret, v c * (c - y)⁻¹) - (m * ∑ c ∈ Ret, v c * (c - z)⁻¹) * m' =
      m * m' * (∑ c ∈ Ret, v c * (c - y)⁻¹ - ∑ c ∈ Ret, v c * (c - z)⁻¹) := by ring
  rw [this, hsum]
  field_simp

end Cauchy

section Price

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}

/-- **Theorem UF, price form.** If `M_next mod p` is a weighted Cauchy matrix of the derived frame
with retained poles `Ret`, then `denexp_p(det Φ) ≤ h + R0 - (|s| - |Ret|)`. -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_derived (D : LeadingData p Φ) (R0 : ℕ)
    (hR : R0 + D.s.card = Fintype.card ι) (Ret : Finset (ZMod p)) (v : ZMod p → ZMod p)
    (mR mC ρ σ : D.s → ZMod p)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c ∈ Ret, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹))) :
    GLE p (Fintype.card ι + R0 - (D.s.card - Ret.card)) Φ.det := by
  apply D.gle_det_R0 R0 _ hR
  have h : D.nextRed.rank ≤ Ret.card := by
    refine rank_le_card_of_sum Ret D.nextRed (fun r c => rfH p (mR r * (c - ρ r)⁻¹))
      (fun c s => rfH p (v c * (c - σ s)⁻¹ * mC s)) fun r s => ?_
    rw [hnext r s, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← map_mul]; congr 1; ring
  have hs : D.nextRed.rank ≤ D.s.card := by
    simpa using Matrix.rank_le_card_width D.nextRed
  omega

/-- **Theorem UF.** The retained poles are the residues outside the zero-weight set `I_J`
(transport and top-extension residues) and outside the wedge-killed residues `Kill`; the retained
count is `p - |I_J ∪ Kill|`. -/
theorem _root_.CatalanCore.Uniform.Content.Hybrid.LeadingData.gle_det_uf (D : LeadingData p Φ) (R0 : ℕ)
    (hR : R0 + D.s.card = Fintype.card ι) (v : ZMod p → ZMod p) (I Kill : Finset (ZMod p))
    (mR mC ρ σ : D.s → ZMod p)
    (hI : ∀ c ∈ I, v c = 0) (hKill : ∀ c ∈ Kill, v c = 0)
    (hnext : ∀ i j, D.nextRed i j =
      rfH p (mR i * mC j * ∑ c, v c * ((c - ρ i)⁻¹ * (c - σ j)⁻¹))) :
    GLE p (Fintype.card ι + R0 - (D.s.card - (p - (I ∪ Kill).card))) Φ.det := by
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
  have := D.gle_det_derived R0 hR (univ \ (I ∪ Kill)) v mR mC ρ σ (fun i j => by
    rw [hnext i j, hsum i j])
  rwa [hcard] at this

end Price

section Compose

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}

/-- Composition with the rank-layer price at one prime. -/
theorem gle_det_hybrid_uf {a b : ℕ} (h1 : GLE p a Φ.det) (h2 : GLE p b Φ.det) :
    GLE p (min a b) Φ.det :=
  gle_det_min h1 h2

end Compose

end CatalanCore.Uniform.Content.Smith
