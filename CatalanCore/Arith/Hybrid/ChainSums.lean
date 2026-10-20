module

public import CatalanCore.Arith.Hybrid.UniformEntries

@[expose] public section

/-! # The singular-support prefix formulas

The quotient residues vanish at every regular index.  Thus the uniform entry
formulas and the transported finite singular-prefix formulas are identical.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

variable {p o N : ℕ} [Fact p.Prime]

theorem regular_of_not_singularNodes {t : ℕ} (ht : 1≤t) (htN : t<N)
    (hn : t∉singularNodes p o N) : ¬p∣t ∧ ¬p∣4*t-o := by
  constructor
  · intro hd
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht,htN⟩,Or.inl hd⟩)
  · intro hd
    exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨ht,htN⟩,Or.inr hd⟩)

theorem interval_sum_eq_Lv {A B : ℕ} (hAB : A≤B) (hB : B<N)
    (v : ℕ→ZMod p) (hv : ∀t, 1≤t → t<N → t∉singularNodes p o N → v t=0) :
    (∑t∈Ioc A B,v t) = Lv (singularNodes p o N) v B - Lv (singularNodes p o N) v A := by
  let s := (singularNodes p o N).filter (fun t => t∈Ioc A B)
  have hsub : s⊆Ioc A B := fun _ ht => (Finset.mem_filter.mp ht).2
  have he : (∑t∈s,v t) = ∑t∈Ioc A B,v t := by
    apply Finset.sum_subset hsub
    intro t ht hn
    have ht' := Finset.mem_Ioc.mp ht
    apply hv t (by omega) (by omega)
    intro hsing
    exact hn (Finset.mem_filter.mpr ⟨hsing,ht⟩)
  rw [←he]
  exact sum_Ioc_Lv _ _ hAB

theorem prefix_sum_eq_Lv {A : ℕ} (hA : A<N)
    (v : ℕ→ZMod p) (hv : ∀t, 1≤t → t<N → t∉singularNodes p o N → v t=0) :
    (∑t∈Icc 1 A,v t) = Lv (singularNodes p o N) v A := by
  let s := (singularNodes p o N).filter (fun t => t∈Icc 1 A)
  have hsub : s⊆Icc 1 A := fun _ ht => (Finset.mem_filter.mp ht).2
  have he : (∑t∈s,v t) = ∑t∈Icc 1 A,v t := by
    apply Finset.sum_subset hsub
    intro t ht hn
    have ht' := Finset.mem_Icc.mp ht
    apply hv t ht'.1 (by omega)
    intro hsing
    exact hn (Finset.mem_filter.mpr ⟨hsing,ht⟩)
  rw [←he]
  exact sum_Icc_Lv _ _ (fun _ ht => (Finset.mem_Ico.mp (Finset.mem_filter.mp ht).1).1)

theorem delta_interval_eq_Lv {A B : ℕ} (hAB : A≤B) (hB : B<N) :
    (∑t∈Ioc A B,deltaResidue p o t) =
      Lv (singularNodes p o N) (deltaResidue p o) B -
        Lv (singularNodes p o N) (deltaResidue p o) A := by
  apply interval_sum_eq_Lv hAB hB
  intro t ht htN hn
  have hh := regular_of_not_singularNodes ht htN hn
  exact deltaResidue_eq_zero hh.1 hh.2

theorem dsq_prefix_eq_Lv {A : ℕ} (hA : A<N) :
    (∑t∈Icc 1 A,dsqResidue p o t) = Lv (singularNodes p o N) (dsqResidue p o) A := by
  apply prefix_sum_eq_Lv hA
  intro t ht htN hn
  have hh := regular_of_not_singularNodes ht htN hn
  exact dsqResidue_eq_zero hh.1 hh.2

end CatalanCore.Arith.Hybrid
