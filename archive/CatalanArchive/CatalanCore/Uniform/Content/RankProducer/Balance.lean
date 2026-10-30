import CatalanCore.Uniform.Content.RankProducer.Restriction
import CatalanCore.Uniform.Content.RankProducer.Block
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open CatalanCore CatalanCore.Uniform.Content.Hybrid
  CatalanCore.Uniform.Content.RankProducer
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def retainedDigits (a : ι → ℕ) (K : Finset ι) (x : ZMod p) : Finset ℕ :=
  (K.filter (fun i => (a i : ZMod p) = x)).image (fun i => a i / p)

/-- Rebalance actual killed indices, and pull the retained digits back into each fibre. -/
noncomputable def retainAssignment (a b : ι → ℕ) (cert : ZMod p → FibreCert)
    (KR KC : Finset ι) (x : ZMod p) : FibreCert :=
  trim (cert x) (retainedDigits a KR x) (retainedDigits b KC x)

theorem retained_rows_sub (a : ι → ℕ) (cert : ZMod p → FibreCert)
    (KR : Finset ι) (hKR : KR ⊆ killRows (p := p) a cert) (x : ZMod p) :
    retainedDigits a KR x ⊆ (cert x).kr := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
  obtain ⟨hiK, hix⟩ := Finset.mem_filter.1 hi
  have h := (Finset.mem_filter.1 (hKR hiK)).2
  simpa only [hix] using h

theorem retained_cols_sub (b : ι → ℕ) (cert : ZMod p → FibreCert)
    (KC : Finset ι) (hKC : KC ⊆ killCols (p := p) b cert) (x : ZMod p) :
    retainedDigits b KC x ⊆ (cert x).kc := by
  intro d hd
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
  obtain ⟨hiK, hix⟩ := Finset.mem_filter.1 hi
  have h := (Finset.mem_filter.1 (hKC hiK)).2
  simpa only [hix] using h

theorem retainAssignment_ok (a b : ι → ℕ) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (KR KC : Finset ι)
    (hKR : KR ⊆ killRows (p := p) a cert) (hKC : KC ⊆ killCols (p := p) b cert)
    (x : ZMod p) : (retainAssignment a b cert KR KC x).Ok :=
  trim_ok _ (hOk x) _ _ (retained_rows_sub a cert KR hKR x) (retained_cols_sub b cert KC hKC x)

theorem retainAssignment_killRows (a b : ι → ℕ) (ha : Function.Injective a)
    (cert : ZMod p → FibreCert) (KR KC : Finset ι) :
    killRows (p := p) a (retainAssignment a b cert KR KC) = KR := by
  ext i
  simp only [killRows, Finset.mem_filter, Finset.mem_univ, true_and]
  change a i / p ∈ retainedDigits a KR (a i : ZMod p) ↔ i ∈ KR
  constructor
  · intro hi
    obtain ⟨j, hj, hd⟩ := Finset.mem_image.1 hi
    obtain ⟨hjK, hjx⟩ := Finset.mem_filter.1 hj
    have heq : j = i := ha (node_eq_of_digit hjx hd)
    simpa only [heq] using hjK
  · intro hi
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩, rfl⟩

theorem retainAssignment_killCols (a b : ι → ℕ) (hb : Function.Injective b)
    (cert : ZMod p → FibreCert) (KR KC : Finset ι) :
    killCols (p := p) b (retainAssignment a b cert KR KC) = KC := by
  ext i
  simp only [killCols, Finset.mem_filter, Finset.mem_univ, true_and]
  change b i / p ∈ retainedDigits b KC (b i : ZMod p) ↔ i ∈ KC
  constructor
  · intro hi
    obtain ⟨j, hj, hd⟩ := Finset.mem_image.1 hi
    obtain ⟨hjK, hjx⟩ := Finset.mem_filter.1 hj
    have heq : j = i := hb (node_eq_of_digit hjx hd)
    simpa only [heq] using hjK
  · intro hi
    exact Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨hi, rfl⟩, rfl⟩

theorem exists_balanced_indices (a b : ι → ℕ) (cert : ZMod p → FibreCert) :
    ∃ KR KC : Finset ι,
      KR ⊆ killRows (p := p) a cert ∧ KC ⊆ killCols (p := p) b cert ∧
      KR.card = min (killRows (p := p) a cert).card (killCols (p := p) b cert).card ∧
      KC.card = min (killRows (p := p) a cert).card (killCols (p := p) b cert).card := by
  obtain ⟨KR, hR, hRc⟩ := Finset.exists_subset_card_eq
    (s := killRows (p := p) a cert) (min_le_left (killRows (p := p) a cert).card (killCols (p := p) b cert).card)
  obtain ⟨KC, hC, hCc⟩ := Finset.exists_subset_card_eq
    (s := killCols (p := p) b cert) (min_le_right (killRows (p := p) a cert).card (killCols (p := p) b cert).card)
  exact ⟨KR, KC, hR, hC, hRc, hCc⟩

#print axioms retainAssignment_ok
#print axioms retainAssignment_killRows
#print axioms exists_balanced_indices
end CatalanCore.Uniform.Content.RankProducer
