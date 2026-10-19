module

public import CatalanFrames.LambdaHybrid.NV.Reduce

/-!
# Lemma 1.2 at `h = ℓ`, split along the four classes of high nodes

`16 · A = W_all W_allᵀ + cc` with `W_all` the Cauchy columns of all high nodes `[K, ℓ)` (this is
the legacy `G`), and the high nodes split as `C_high ⊔ absent ⊔ X' ⊔ Y'`.
-/

@[expose] public section

open Finset CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

/-- the absent high nodes -/
def absS (K ℓ : ℕ) (C X Y : Finset ℕ) : Finset ℕ :=
  (Ico K ℓ).filter (fun n => n ∉ C ∧ n ∉ X ∧ n ∉ Y)

lemma sum_split {M : Type*} [AddCommMonoid M] (K ℓ : ℕ) (C X Y : Finset ℕ)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) (hXY : Disjoint X Y)
    (hC : ∀ n ∈ C, n < ℓ) (hX : ∀ n ∈ X, K ≤ n ∧ n < ℓ) (hY : ∀ n ∈ Y, K ≤ n ∧ n < ℓ)
    (F : ℕ → M) :
    ∑ n ∈ Ico K ℓ, F n = ∑ n ∈ C.filter (fun n => K ≤ n), F n + ∑ n ∈ absS K ℓ C X Y, F n +
      ∑ n ∈ X, F n + ∑ n ∈ Y, F n := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Ico K ℓ) (fun n => n ∈ C) F]
  rw [← Finset.sum_filter_add_sum_filter_not ((Ico K ℓ).filter (fun n => n ∉ C))
    (fun n => n ∈ X) F]
  rw [← Finset.sum_filter_add_sum_filter_not (((Ico K ℓ).filter (fun n => n ∉ C)).filter
    (fun n => n ∉ X)) (fun n => n ∈ Y) F]
  have e1 : (Ico K ℓ).filter (fun n => n ∈ C) = C.filter (fun n => K ≤ n) := by
    ext n; simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h1⟩
    · rintro ⟨h3, h1⟩; exact ⟨⟨h1, hC n h3⟩, h3⟩
  have e2 : ((Ico K ℓ).filter (fun n => n ∉ C)).filter (fun n => n ∈ X) = X := by
    ext n; simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      exact ⟨⟨⟨(hX n h).1, (hX n h).2⟩, Finset.disjoint_right.1 hCX h⟩, h⟩
  have e3 : (((Ico K ℓ).filter (fun n => n ∉ C)).filter (fun n => n ∉ X)).filter
      (fun n => n ∈ Y) = Y := by
    ext n; simp only [mem_filter, mem_Ico]
    constructor
    · rintro ⟨_, h⟩; exact h
    · intro h
      exact ⟨⟨⟨⟨(hY n h).1, (hY n h).2⟩, Finset.disjoint_right.1 hCY h⟩,
        Finset.disjoint_right.1 hXY h⟩, h⟩
  have e4 : (((Ico K ℓ).filter (fun n => n ∉ C)).filter (fun n => n ∉ X)).filter
      (fun n => n ∉ Y) = absS K ℓ C X Y := by
    ext n; simp only [mem_filter, mem_Ico, absS]
    tauto
  rw [e1, e2, e3, e4]
  abel

/-- sum over an injective family covering a finset -/
lemma sum_family {M : Type*} [AddCommMonoid M] {g : Type*} [Fintype g] (nd : g → ℕ)
    (hnd : Function.Injective nd) (S : Finset ℕ) (hS : ∀ n, (∃ i, nd i = n) ↔ n ∈ S) (F : ℕ → M) :
    ∑ i : g, F (nd i) = ∑ n ∈ S, F n := by
  classical
  have : S = (Finset.univ : Finset g).image nd := by
    ext n; rw [← hS n]; simp
  rw [this, Finset.sum_image (fun a _ b _ h => hnd h)]

section Ident

variable {ℓ K : ℕ} [Fact ℓ.Prime]

lemma xs_family (G : Geometry) : Function.Injective G.xs ∧ ∀ n, (∃ i, G.xs i = n) ↔ n ∈ G.X' := by
  refine ⟨(Finset.orderEmbOfFin G.X' rfl).injective, fun n => ?_⟩
  have := Finset.range_orderEmbOfFin G.X' (rfl : G.X'.card = G.k)
  constructor
  · rintro ⟨i, rfl⟩; exact xs_mem G i
  · intro h
    have h' : n ∈ Set.range (Finset.orderEmbOfFin G.X' (rfl : G.X'.card = G.k)) := by
      rw [this]; exact h
    exact h'

lemma ys_family (G : Geometry) : Function.Injective G.ys ∧ ∀ n, (∃ i, G.ys i = n) ↔ n ∈ G.Y' := by
  refine ⟨(Finset.orderEmbOfFin G.Y' G.card_eq.symm).injective, fun n => ?_⟩
  have := Finset.range_orderEmbOfFin G.Y' G.card_eq.symm
  constructor
  · rintro ⟨i, rfl⟩; exact ys_mem G i
  · intro h
    have h' : n ∈ Set.range (Finset.orderEmbOfFin G.Y' G.card_eq.symm) := by
      rw [this]; exact h
    exact h'

lemma hic_family (K : ℕ) (G : Geometry) :
    Function.Injective (fun b : HiC K G => ((b.1 : G.C) : ℕ)) ∧
      ∀ n, (∃ b : HiC K G, ((b.1 : G.C) : ℕ) = n) ↔ n ∈ G.C.filter (fun n => K ≤ n) := by
  refine ⟨fun b b' h => Subtype.ext (Subtype.ext h), fun n => ?_⟩
  constructor
  · rintro ⟨b, rfl⟩
    exact Finset.mem_filter.2 ⟨b.1.2, by have := b.2; omega⟩
  · intro h
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h
    exact ⟨⟨⟨n, h1⟩, by show ¬ n < K; omega⟩, rfl⟩

end Ident

end CatalanFrames.LambdaHybrid.NV
