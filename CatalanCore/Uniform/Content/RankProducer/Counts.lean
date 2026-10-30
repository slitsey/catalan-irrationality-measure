module

public import CatalanCore.Uniform.Content.RankProducer.Block

@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore.Uniform.Content.Hybrid
open scoped Classical
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual-index kill counts equal digit counts, summed over the residue fibres. -/
theorem killCount_eq_sum (a : ι → ℕ) (ha : Function.Injective a)
    (K : ZMod p → Finset ℕ)
    (hcov : ∀ x, ∀ d ∈ K x, ∃ i, (a i : ZMod p) = x ∧ a i / p = d) :
    (univ.filter (fun i => a i / p ∈ K (a i : ZMod p))).card = ∑ x, (K x).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun i => (a i : ZMod p)) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro x _
  let F := (univ.filter (fun i => a i / p ∈ K (a i : ZMod p))).filter
    (fun i => (a i : ZMod p) = x)
  change F.card = (K x).card
  have himage : F.image (fun i => a i / p) = K x := by
    ext d
    constructor
    · intro hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hd
      obtain ⟨hiK, hix⟩ := Finset.mem_filter.1 hi
      have h := (Finset.mem_filter.1 hiK).2
      simpa only [hix] using h
    · intro hd
      obtain ⟨i, hix, hid⟩ := hcov x d hd
      have hiK : a i / p ∈ K (a i : ZMod p) := by rw [hix, hid]; exact hd
      exact Finset.mem_image.2 ⟨i,
        Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, hiK⟩, hix⟩, hid⟩
  have hinj : Set.InjOn (fun i => a i / p) (F : Set ι) := by
    intro i hi j hj hij
    have hix := (Finset.mem_filter.1 hi).2
    have hjx := (Finset.mem_filter.1 hj).2
    exact ha (node_eq_of_digit (hix.trans hjx.symm) hij)
  exact (Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card himage)

variable {B : ℕ} {f e : ℕ → ℚ}

theorem killRows_card_eq_sum (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (ha : Function.Injective a) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hReal : ∀ x, Realizes PS a b x (cert x)) :
    (killRows (p := p) a cert).card = ∑ x, (cert x).kr.card :=
  killCount_eq_sum a ha (fun x => (cert x).kr)
    (fun x d hd => (hReal x).r_cov d ((hOk x).kr_sub hd))

theorem killCols_card_eq_sum (PS : PoleSplit p B f e) (a b : ι → ℕ)
    (hb : Function.Injective b) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hReal : ∀ x, Realizes PS a b x (cert x)) :
    (killCols (p := p) b cert).card = ∑ x, (cert x).kc.card :=
  killCount_eq_sum b hb (fun x => (cert x).kc)
    (fun x d hd => (hReal x).c_cov d ((hOk x).kc_sub hd))

/-- Sum the certified contribution on disjoint residue runs; all other fibres
may contribute additional nonnegative kills or load intersections. -/
theorem disjoint_count_lower {α β : Type*} [Fintype α] [DecidableEq α]
    (I : Finset β) (A : β → Finset α) (w : β → ℕ) (f : α → ℕ)
    (hdisj : (I : Set β).PairwiseDisjoint A)
    (hpoint : ∀ i ∈ I, ∀ x ∈ A i, w i ≤ f x) :
    ∑ i ∈ I, (A i).card * w i ≤ ∑ x, f x := by
  calc
    _ = ∑ i ∈ I, ∑ _x ∈ A i, w i := by simp
    _ ≤ ∑ i ∈ I, ∑ x ∈ A i, f x :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun x hx => hpoint i hi x hx))
    _ = ∑ x ∈ I.biUnion A, f x := (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)

#print axioms killRows_card_eq_sum
#print axioms disjoint_count_lower
#print axioms killCols_card_eq_sum
end CatalanCore.Uniform.Content.RankProducer
