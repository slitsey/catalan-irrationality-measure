module

public import CatalanCore.Uniform.Content.RankProducer.ClosedMember
public import CatalanCore.Uniform.Content.RankProducer.TrimCost

@[expose] public section
set_option Elab.async false

/-! # Counting with deletions (Theorem R, "Deletions"; NOTES P5, lane C2L)

The objects are the `m` row border nodes, the `m` column border nodes and the `nsq` square
residues `[r + 2m - p, min(r, ρ))`.  Untouched objects (no deleted common node in their residue
class) carry certificates; `exists_assign` chooses balanced `RA ⊆ RU`, `CA ⊆ CU` and proves

  `m + nsq ≤ |RA| + |SQ| + δ`,   `w_l ≤ |RA_l| + |CA_l| + 2 [l = D0] |SQ| + 2 δ`,

`δ = r - |T|` the number of deleted nodes, `w_l` the class-`l` border count plus `2 nsq` for D0.
The touched objects number at most `δ`: residues are injective on the window
`[r + 2m - p, r + 2m)`, and every touched residue is the residue of a deleted node.
-/

namespace CatalanCore.Uniform.Content.RankProducer
open Finset CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Wire
open scoped Classical

section Count
variable {G : BlockGeom} {r : ℕ}

/-- Row border nodes. -/
def rowB (r m : ℕ) : Finset ℕ := (Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 0)
/-- Column border nodes. -/
def colB (r m : ℕ) : Finset ℕ := (Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 1)
/-- Square residues. -/
def sqAll (r m p ρ : ℕ) : Finset ℕ := Ico (r + 2 * m - p) (min r ρ)
/-- The residue class of `t` has no deleted common node. -/
def untouched (T : Finset (G.geometry r).C) (p t : ℕ) : Prop :=
  ∀ d < t / p, keptN T (t % p + p * d)

theorem card_rowB (r m : ℕ) : (rowB r m).card = m := by
  have : rowB r m = (range m).image (fun i => r + 2 * i) := by
    ext t
    simp only [rowB, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(t - r) / 2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simp at h; omega), Finset.card_range]

theorem card_colB (r m : ℕ) : (colB r m).card = m := by
  have : colB r m = (range m).image (fun i => r + 2 * i + 1) := by
    ext t
    simp only [colB, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨(t - r) / 2, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simp at h; omega), Finset.card_range]

/-- The deleted common nodes number `r - |T|`. -/
theorem card_deleted (hs : HybShape G r) (T : Finset (G.geometry r).C) :
    ((range r).filter (fun n => ¬ keptN T n)).card = r - T.card := by
  have hk : (range r).filter (fun n => keptN T n) = T.image (fun a => ((a : (G.geometry r).C) : ℕ)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨-, a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨keptN_lt hs ⟨a, ha, rfl⟩, a, ha, rfl⟩
  have hc : (T.image (fun a => ((a : (G.geometry r).C) : ℕ))).card = T.card :=
    Finset.card_image_of_injective _ Subtype.val_injective
  have := Finset.card_filter_add_card_filter_not (s := range r) (fun n => keptN T n)
  rw [hk, hc, Finset.card_range] at this
  omega

/-- **Touched objects.** At most `r - |T|` objects are touched. -/
theorem touched_le (hs : HybShape G r) (T : Finset (G.geometry r).C) {m p ρ : ℕ}
    [hp : Fact p.Prime] (hpm : 2 * m < p) (hρp : ρ < p) :
    ((rowB r m).card - ((rowB r m).filter (untouched T p)).card) +
      ((colB r m).card - ((colB r m).filter (untouched T p)).card) +
      ((sqAll r m p ρ).card - ((sqAll r m p ρ).filter (keptN T)).card) ≤ r - T.card := by
  have hp0 := hp.out.pos
  set A1 := rowB r m \ (rowB r m).filter (untouched T p) with hA1
  set A2 := colB r m \ (colB r m).filter (untouched T p) with hA2
  set A3 := sqAll r m p ρ \ (sqAll r m p ρ).filter (keptN T) with hA3
  have c1 : A1.card = (rowB r m).card - ((rowB r m).filter (untouched T p)).card :=
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  have c2 : A2.card = (colB r m).card - ((colB r m).filter (untouched T p)).card :=
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  have c3 : A3.card = (sqAll r m p ρ).card - ((sqAll r m p ρ).filter (keptN T)).card :=
    Finset.card_sdiff_of_subset (Finset.filter_subset _ _)
  have m1 : ∀ t ∈ A1, r ≤ t ∧ t < r + 2 * m ∧ (t - r) % 2 = 0 ∧ ¬ untouched T p t := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
    exact ⟨(Finset.mem_Ico.1 h3).1, (Finset.mem_Ico.1 h3).2, h4,
      fun hu => h2 (Finset.mem_filter.2 ⟨h1, hu⟩)⟩
  have m2 : ∀ t ∈ A2, r ≤ t ∧ t < r + 2 * m ∧ (t - r) % 2 = 1 ∧ ¬ untouched T p t := by
    intro t ht
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ht
    obtain ⟨h3, h4⟩ := Finset.mem_filter.1 h1
    exact ⟨(Finset.mem_Ico.1 h3).1, (Finset.mem_Ico.1 h3).2, h4,
      fun hu => h2 (Finset.mem_filter.2 ⟨h1, hu⟩)⟩
  have m3 : ∀ x ∈ A3, r + 2 * m - p ≤ x ∧ x < r ∧ x < ρ ∧ ¬ keptN T x := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hx
    have h3 := Finset.mem_Ico.1 h1
    exact ⟨h3.1, by have := h3.2; omega, by have := h3.2; omega,
      fun hk => h2 (Finset.mem_filter.2 ⟨h1, hk⟩)⟩
  have d12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro t h1 h2
    have := (m1 t h1).2.2.1; have := (m2 t h2).2.2.1; omega
  have d3 : Disjoint (A1 ∪ A2) A3 := by
    rw [Finset.disjoint_left]; intro t h h3
    have := (m3 t h3).2.1
    rcases Finset.mem_union.1 h with h | h
    · have := (m1 t h).1; omega
    · have := (m2 t h).1; omega
  have hcardO : (A1 ∪ A2 ∪ A3).card = A1.card + A2.card + A3.card := by
    rw [Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d12]
  have hwin : ∀ t ∈ A1 ∪ A2 ∪ A3, r + 2 * m - p ≤ t ∧ t < r + 2 * m := by
    intro t ht
    rcases Finset.mem_union.1 ht with h | h
    · rcases Finset.mem_union.1 h with h | h
      · have := m1 t h; omega
      · have := m2 t h; omega
    · have := m3 t h; omega
  have hinjO : Set.InjOn (· % p) ((A1 ∪ A2 ∪ A3 : Finset ℕ) : Set ℕ) := by
    intro t ht t' ht' h
    have w1 := hwin t ht
    have w2 := hwin t' ht'
    exact eq_of_mod_eq hp0 h (by omega) (by omega)
  have hsub : (A1 ∪ A2 ∪ A3).image (· % p) ⊆
      ((range r).filter (fun n => ¬ keptN T n)).image (· % p) := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hy
    rcases Finset.mem_union.1 ht with h | h
    · have hbord : r ≤ t ∧ t < r + 2 * m ∧ ¬ untouched T p t := by
        rcases Finset.mem_union.1 h with h | h
        · obtain ⟨a1, a2, -, a4⟩ := m1 t h; exact ⟨a1, a2, a4⟩
        · obtain ⟨a1, a2, -, a4⟩ := m2 t h; exact ⟨a1, a2, a4⟩
      obtain ⟨b1, b2, b3⟩ := hbord
      unfold untouched at b3
      push_neg at b3
      obtain ⟨d, hd, hnk⟩ := b3
      have hlt := lt_of_digit hp0 (show t < r + p by omega) hd
      refine Finset.mem_image.2 ⟨t % p + p * d, Finset.mem_filter.2
        ⟨Finset.mem_range.2 hlt, hnk⟩, ?_⟩
      exact mod_digit (Nat.mod_lt t hp0)
    · obtain ⟨-, a2, a3, a4⟩ := m3 t h
      exact Finset.mem_image.2 ⟨t, Finset.mem_filter.2 ⟨Finset.mem_range.2 a2, a4⟩, rfl⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinjO, hcardO] at h1
  have h2 := Finset.card_image_le (s := (range r).filter (fun n => ¬ keptN T n)) (f := (· % p))
  rw [card_deleted hs T] at h2
  omega

/-- **The assignment.** -/
theorem exists_assign (hs : HybShape G r) (T : Finset (G.geometry r).C) {m p ρ : ℕ}
    [hp : Fact p.Prime] (hpm : 2 * m < p) (hρp : ρ < p) :
    ∃ RA CA SQ : Finset ℕ, Assign r m p ρ T RA CA SQ ∧
      m + (sqAll r m p ρ).card ≤ RA.card + SQ.card + (r - T.card) ∧
      ∀ l : LineCls,
        ((Ico r (r + 2 * m)).filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
            2 * (if l = none then (sqAll r m p ρ).card else 0) ≤
          (RA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
          (CA.filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card +
          2 * (if l = none then SQ.card else 0) + 2 * (r - T.card) := by
  have hT := touched_le hs T hpm hρp
  set RU := (rowB r m).filter (untouched T p) with hRU
  set CU := (colB r m).filter (untouched T p) with hCU
  set SQ := (sqAll r m p ρ).filter (keptN T) with hSQ
  obtain ⟨RA, hRAs, hRAc⟩ := Finset.exists_subset_card_eq (s := RU)
    (n := min RU.card CU.card) (min_le_left _ _)
  obtain ⟨CA, hCAs, hCAc⟩ := Finset.exists_subset_card_eq (s := CU)
    (n := min RU.card CU.card) (min_le_right _ _)
  rw [card_rowB, card_colB] at hT
  have hRUs : RU ⊆ rowB r m := Finset.filter_subset _ _
  have hCUs : CU ⊆ colB r m := Finset.filter_subset _ _
  have hSQs : SQ ⊆ sqAll r m p ρ := Finset.filter_subset _ _
  have hRUc : RU.card ≤ m := by
    have := Finset.card_le_card hRUs; rw [card_rowB] at this; exact this
  have hCUc : CU.card ≤ m := by
    have := Finset.card_le_card hCUs; rw [card_colB] at this; exact this
  have hSQc : SQ.card ≤ (sqAll r m p ρ).card := Finset.card_le_card hSQs
  refine ⟨RA, CA, SQ, ⟨?_, ?_, ?_, by rw [hRAc, hCAc], hρp⟩, ?_, ?_⟩
  · intro t ht
    have h1 := hRAs ht
    obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
    obtain ⟨h4, h5⟩ := Finset.mem_filter.1 h2
    exact ⟨(Finset.mem_Ico.1 h4).1, (Finset.mem_Ico.1 h4).2, h5, h3⟩
  · intro t ht
    have h1 := hCAs ht
    obtain ⟨h2, h3⟩ := Finset.mem_filter.1 h1
    obtain ⟨h4, h5⟩ := Finset.mem_filter.1 h2
    exact ⟨(Finset.mem_Ico.1 h4).1, (Finset.mem_Ico.1 h4).2, h5, h3⟩
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    have h3 := Finset.mem_Ico.1 h1
    refine ⟨by have := h3.2; omega, by omega, by have := h3.2; omega, h2⟩
  · omega
  · intro l
    have hsplit : ((Ico r (r + 2 * m)).filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card =
        ((rowB r m).filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card + ((colB r m).filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))).card := by
      have h := Finset.card_filter_add_card_filter_not
        (s := (Ico r (r + 2 * m)).filter (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))) (fun t => (t - r) % 2 = 0)
      rw [← h]
      congr 2
      · ext t
        simp only [rowB, Finset.mem_filter]
        tauto
      · ext t
        simp only [colB, Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, by omega⟩, h2⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h3⟩, by omega⟩
    have e1 := filter_card_loss (rowB r m) RU hRUs (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))
    have e2 := filter_card_loss RU RA hRAs (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))
    have e3 := filter_card_loss (colB r m) CU hCUs (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))
    have e4 := filter_card_loss CU CA hCAs (fun t => inCls l (t / p) (decide (ρ ≤ t % p)))
    rw [card_rowB] at e1
    rw [card_colB] at e3
    rw [hRAc] at e2
    rw [hCAc] at e4
    have hsqA : (if l = none then (sqAll r m p ρ).card else 0) ≤
        (if l = none then SQ.card else 0) + ((sqAll r m p ρ).card - SQ.card) := by
      split_ifs <;> omega
    generalize (if l = none then (sqAll r m p ρ).card else 0) = a at hsqA ⊢
    generalize (if l = none then SQ.card else 0) = b at hsqA ⊢
    omega

end Count

#print axioms touched_le
#print axioms exists_assign
end CatalanCore.Uniform.Content.RankProducer
