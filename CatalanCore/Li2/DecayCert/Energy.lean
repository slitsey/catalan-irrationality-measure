module

public import CatalanCore.Li2.DecayCert.Segment

public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

set_option Elab.async false

open MeasureTheory Set Filter Topology

open scoped BigOperators

open CatalanCore.Li2.Decay

namespace CatalanCore.Li2.DecayCert

private theorem partition_lower {J : Type*} [Fintype J] (σ : Measure ℂ) [IsFiniteMeasure σ]

    (f : ℂ → ℝ) (hf : Integrable f σ) (cells : J → Set ℂ) (lower : J → ℝ)

    (hmeas : ∀ j, MeasurableSet (cells j)) (hcover : σ (⋃ j, cells j)ᶜ=0)

    (hnull : ∀ j k, j ≠ k → σ (cells j ∩ cells k)=0)

    (hlo : ∀ j, ∀ᵐ s ∂σ.restrict (cells j), lower j ≤ f s) :

    (∑ j, σ.real (cells j)*lower j) ≤ ∫ s, f s ∂σ := by

  classical

  have hrestrict : σ.restrict (⋃ j, cells j)=σ :=

    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hcover)

  have he := integral_iUnion_ae (μ := σ) (f := f)

    (fun j => (hmeas j).nullMeasurableSet) hnull hf.integrableOn

  rw [hrestrict, tsum_fintype] at he

  rw [he]

  apply Finset.sum_le_sum

  intro j hj

  have h := integral_mono_ae (integrable_const (lower j)) hf.integrableOn (hlo j)

  simpa only [integral_const, smul_eq_mul, Measure.real,

    Measure.restrict_apply MeasurableSet.univ, univ_inter] using h



private theorem energy_of_lower (σ : Measure ℂ) [IsFiniteMeasure σ] (V0 : ℂ → ℝ)

    (hV : Integrable V0 σ) (hU : Integrable (U σ) σ) (b : ℝ)

    (hb : b ≤ ∫ s, V0 s-2*U σ s ∂σ) :

    I σ ≤ ((∫ s, V0 s ∂σ)-b)/2 := by

  have he := integral_sub (μ := σ) (f := V0) (g := fun s => 2*U σ s)

    hV (hU.const_mul 2)

  rw [he, integral_const_mul] at hb

  dsimp only [I]

  linarith



theorem energy_up (σ : Measure ℂ) [IsFiniteMeasure σ] (V0 : ℂ → ℝ)

    (C : Finset (Set ℂ)) (lo : Set ℂ → ℝ)

    (hmeas : ∀ c ∈ C, MeasurableSet c)

    (hdisj : Set.PairwiseDisjoint (↑C : Set (Set ℂ)) id)

    (hcover : σ (⋃ c ∈ C, c)ᶜ=0)

    (hV : Integrable V0 σ) (hU : Integrable (U σ) σ)

    (hlo : ∀ c ∈ C, ∀ᵐ s ∂σ.restrict c, lo c ≤ V0 s-2*U σ s) :

    I σ ≤ ((∫ s, V0 s ∂σ)-∑ c ∈ C, σ.real c*lo c)/2 := by

  classical

  have hcov : σ (⋃ c : C, (c:Set ℂ))ᶜ=0 := by

    have he : (⋃ c : C, (c:Set ℂ)) = ⋃ c ∈ C, c := by ext x; simp

    rw [he]

    exact hcover

  have hn : ∀ j k : C, j ≠ k → σ ((j:Set ℂ) ∩ (k:Set ℂ))=0 := by

    intro j k hjk

    have hd := hdisj j.property k.property (fun h => hjk (Subtype.ext h))

    change Disjoint (j:Set ℂ) (k:Set ℂ) at hd

    rw [Set.disjoint_iff_inter_eq_empty.mp hd, measure_empty]

  have hb := partition_lower σ (fun s => V0 s-2*U σ s) (hV.sub (hU.const_mul 2))

    (fun c : C => (c:Set ℂ)) (fun c : C => lo c)

    (fun c => hmeas c c.property) hcov hn (fun c => hlo c c.property)

  have hsum := Finset.sum_coe_sort C (fun c : Set ℂ => σ.real c*lo c)

  rw [hsum] at hb

  exact energy_of_lower σ V0 hV hU _ hb



theorem energy_up_labelled (K : ℕ) (μ : Fin K → Measure ℂ)

    [∀ i, IsFiniteMeasure (μ i)] (σ : Measure ℂ) [IsFiniteMeasure σ]

    (hσ : σ=∑ i, μ i) (V0 : ℂ → ℝ)

    (count : Fin K → ℕ) (cells : (i : Fin K) → Fin (count i) → Set ℂ)

    (lower : (i : Fin K) → Fin (count i) → ℝ)

    (hmeas : ∀ i j, MeasurableSet (cells i j))

    (hcover : ∀ i, μ i (⋃ j, cells i j)ᶜ=0)

    (hnull : ∀ i, ∀ j k : Fin (count i), j ≠ k → μ i (cells i j ∩ cells i k)=0)

    (hV : Integrable V0 σ) (hU : Integrable (U σ) σ)

    (hlo : ∀ i j, ∀ᵐ s ∂(μ i).restrict (cells i j), lower i j ≤ V0 s-2*U σ s) :

    I σ ≤ ((∫ s, V0 s ∂σ)-∑ i, ∑ j, (μ i).real (cells i j)*lower i j)/2 := by

  classical

  let f : ℂ → ℝ := fun s => V0 s-2*U σ s

  have hf : Integrable f σ := hV.sub (hU.const_mul 2)

  have hfi : ∀ i, Integrable f (μ i) := by

    rw [hσ] at hf

    exact fun i => (integrable_finsetSum_measure.mp hf) i (Finset.mem_univ i)

  have hi : (∫ s, f s ∂σ)=∑ i, ∫ s, f s ∂μ i := by

    rw [hσ]

    exact integral_finsetSum_measure (fun i _ => hfi i)

  have hb : (∑ i, ∑ j, (μ i).real (cells i j)*lower i j) ≤ ∫ s, f s ∂σ := by

    rw [hi]

    exact Finset.sum_le_sum (fun i _ => partition_lower (μ i) f (hfi i)

      (cells i) (lower i) (hmeas i) (hcover i) (hnull i) (hlo i))

  exact energy_of_lower σ V0 hV hU _ hb



theorem energy_up_integral_lower (σ : Measure ℂ) [IsFiniteMeasure σ]
    (V0 L : ℂ → ℝ) (hV : Integrable V0 σ) (hU : Integrable (U σ) σ)
    (hL : Integrable L σ) (hle : ∀ᵐ s ∂σ, L s ≤ V0 s-2*U σ s) :
    I σ ≤ ((∫ s, V0 s ∂σ)-(∫ s, L s ∂σ))/2 := by
  exact energy_of_lower σ V0 hV hU _
    (integral_mono_ae hL (hV.sub (hU.const_mul 2)) hle)

#print axioms energy_up_integral_lower
#print axioms energy_up

#print axioms energy_up_labelled

end CatalanCore.Li2.DecayCert

