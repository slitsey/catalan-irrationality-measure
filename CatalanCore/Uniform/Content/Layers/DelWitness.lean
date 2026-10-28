module
public import CatalanCore.Uniform.Content.Layers.DelBounds
public import CatalanCore.Arith.Hybrid.WitnessWeight
@[expose] public section

/-!
# Theorem M3D: the low-band saving for deletion members

For the member `P_{r,I}` (core `C' = [0,r) \ I`, border `X' = {r+2i}`, `Y' = {r+2j+1}`) and a
witness segment `[a,b)` the denominator exponent at `p` is at most
`2(r - |I|) + (2m - (b - a')) + |I|`, `a' = max a (r+2m-p)`; since the full-member price is
`P3 = 2r + (2m - (b - a'))`, the debit relative to `P3 - |I|` is `≤ 0`.

The weight table is `0` only where both nodes lie in the central segment `[a',b)` *and* both
residues avoid `res(I)`; elsewhere it is raised to `1` (distinct residues) or `2` (equal residues).
The covering hypothesis of `member_det_weighted` holds exactly at the zero entries.
-/

open Matrix Polynomial Finset CatalanCore
namespace CatalanCore.Uniform.Content.Layers.Del
open CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses
  CatalanCore.Arith.Hybrid.Periodic

/-- The raised witness weight. -/
def delWeight (p a' b : ℕ) (S : Finset ℕ) (z y : ℕ) : ℕ :=
  if a' ≤ z ∧ z < b ∧ a' ≤ y ∧ y < b ∧ z % p ∉ S ∧ y % p ∉ S then 0
  else if z % p = y % p then 2 else 1

def delTable (p r m a' b : ℕ) (S : Finset ℕ) (i j : Fin m) : ℕ :=
  delWeight p a' b S (r + 2 * (i : ℕ)) (r + 2 * (j : ℕ) + 1)

/-- Node cost of the interval dual. -/
def nodeCost (p a' b : ℕ) (S : Finset ℕ) (z : ℕ) : ℕ :=
  if a' ≤ z ∧ z < b ∧ z % p ∉ S then 0 else 1

lemma delWeight_le_two (p a' b : ℕ) (S : Finset ℕ) (z y : ℕ) : delWeight p a' b S z y ≤ 2 := by
  unfold delWeight; split_ifs <;> omega

lemma delWeight_zero {p a' b : ℕ} {S : Finset ℕ} {z y : ℕ} (h : delWeight p a' b S z y = 0) :
    a' ≤ z ∧ z < b ∧ a' ≤ y ∧ y < b ∧ z % p ∉ S ∧ y % p ∉ S := by
  by_contra hn
  unfold delWeight at h
  rw [if_neg hn] at h
  split_ifs at h <;> omega

lemma delWeight_one {p a' b : ℕ} {S : Finset ℕ} {z y : ℕ} (h : delWeight p a' b S z y = 1) :
    z % p ≠ y % p := by
  intro heq
  unfold delWeight at h
  split_ifs at h <;> omega

lemma delTable_le_cost {p r m a' b : ℕ} (S : Finset ℕ) (hlo : r + 2 * m - p ≤ a') (hra : r ≤ a')
    (hb : b ≤ r + 2 * m) (hbp : b ≤ r + p) (i j : Fin m) :
    delTable p r m a' b S i j ≤
      nodeCost p a' b S (r + 2 * (i : ℕ)) + nodeCost p a' b S (r + 2 * (j : ℕ) + 1) := by
  have hi := i.isLt
  have hj := j.isLt
  unfold delTable
  by_cases hx : a' ≤ r + 2 * (i : ℕ) ∧ r + 2 * (i : ℕ) < b ∧ (r + 2 * (i : ℕ)) % p ∉ S
  · by_cases hy : a' ≤ r + 2 * (j : ℕ) + 1 ∧ r + 2 * (j : ℕ) + 1 < b ∧
        (r + 2 * (j : ℕ) + 1) % p ∉ S
    · have : delWeight p a' b S (r + 2 * (i : ℕ)) (r + 2 * (j : ℕ) + 1) = 0 := by
        unfold delWeight; rw [if_pos ⟨hx.1, hx.2.1, hy.1, hy.2.1, hx.2.2, hy.2.2⟩]
      rw [this]; exact Nat.zero_le _
    · have hne := central_noncong (p := p) (r := r) (N := r + 2 * m) (z := r + 2 * (i : ℕ))
        (y := r + 2 * (j : ℕ) + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hc : nodeCost p a' b S (r + 2 * (j : ℕ) + 1) = 1 := by
        unfold nodeCost; rw [if_neg hy]
      have hc0 : nodeCost p a' b S (r + 2 * (i : ℕ)) = 0 := by
        unfold nodeCost; rw [if_pos hx]
      rw [hc, hc0]
      unfold delWeight
      split_ifs <;> omega
  · have hc : nodeCost p a' b S (r + 2 * (i : ℕ)) = 1 := by
      unfold nodeCost; rw [if_neg hx]
    by_cases hy : a' ≤ r + 2 * (j : ℕ) + 1 ∧ r + 2 * (j : ℕ) + 1 < b ∧
        (r + 2 * (j : ℕ) + 1) % p ∉ S
    · have hne := central_noncong (p := p) (r := r) (N := r + 2 * m) (z := r + 2 * (j : ℕ) + 1)
        (y := r + 2 * (i : ℕ)) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hc0 : nodeCost p a' b S (r + 2 * (j : ℕ) + 1) = 0 := by
        unfold nodeCost; rw [if_pos hy]
      rw [hc, hc0]
      unfold delWeight
      split_ifs <;> omega
    · have hc' : nodeCost p a' b S (r + 2 * (j : ℕ) + 1) = 1 := by
        unfold nodeCost; rw [if_neg hy]
      rw [hc, hc']
      exact delWeight_le_two _ _ _ _ _ _

lemma cost_sum {p r m a' b : ℕ} (S : Finset ℕ) (hra : r ≤ a') (hab : a' ≤ b)
    (hb : b ≤ r + 2 * m) (hbp : b ≤ a' + p) :
    (∑ i : Fin m, nodeCost p a' b S (r + 2 * (i : ℕ))) +
      (∑ j : Fin m, nodeCost p a' b S (r + 2 * (j : ℕ) + 1)) ≤ 2 * m - (b - a') + S.card := by
  rw [sum_zone r m (nodeCost p a' b S)]
  let P : ℕ → Prop := fun z => a' ≤ z ∧ z < b ∧ z % p ∉ S
  have hsum : ∑ z ∈ Ico r (r + 2 * m), nodeCost p a' b S z =
      ((Ico r (r + 2 * m)).filter (fun z => ¬ P z)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro z _
    unfold nodeCost
    by_cases h : P z
    · rw [if_pos h, if_neg (not_not.mpr h)]
    · rw [if_neg h, if_pos h]
  rw [hsum]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ico r (r + 2 * m)) P
  have hcard : (Ico r (r + 2 * m)).card = 2 * m := by simp
  have hfilter : (Ico r (r + 2 * m)).filter P = (Ico a' b).filter (fun z => z % p ∉ S) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Ico, P]
    constructor
    · rintro ⟨_, h3, h4, h5⟩
      exact ⟨⟨h3, h4⟩, h5⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, by omega⟩, h1, h2, h3⟩
  have hsplit2 := Finset.card_filter_add_card_filter_not (s := Ico a' b) (fun z => z % p ∉ S)
  have hB : ((Ico a' b).filter (fun z => ¬ (z % p ∉ S))).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun z => z % p)
    · intro z hz
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq, not_not] at hz
      exact hz.2
    · intro z hz z' hz' h
      simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hz hz'
      have h1 : z ≤ z' := Nat.ModEq.le_of_lt_add h (by omega)
      have h2 : z' ≤ z := Nat.ModEq.le_of_lt_add h.symm (by omega)
      omega
  rw [hfilter] at hsplit
  have hIco : (Ico a' b).card = b - a' := Nat.card_Ico _ _
  omega

lemma delTable_trop {p r m a' b : ℕ} (S : Finset ℕ) (hlo : r + 2 * m - p ≤ a') (hra : r ≤ a')
    (hab : a' ≤ b) (hb : b ≤ r + 2 * m) (hbp : b ≤ r + p) :
    tropVal (delTable p r m a' b S) ≤ 2 * m - (b - a') + S.card :=
  (tropVal_le_nat_dual (delTable p r m a' b S)
    (fun i => nodeCost p a' b S (r + 2 * (i : ℕ)))
    (fun j => nodeCost p a' b S (r + 2 * (j : ℕ) + 1))
    (fun i j => delTable_le_cost S hlo hra hb hbp i j)).trans
    (cost_sum S hra hab hb (by omega))

lemma card_core {r : ℕ} (I : Finset ℕ) (hI : ∀ u ∈ I, u < r) :
    Fintype.card {c : Fin r // c.val ∉ I} = r - I.card := by
  rw [Fintype.card_subtype]
  have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun c : Fin r => c.val ∈ I)
  have h2 : ((Finset.univ : Finset (Fin r)).filter (fun c : Fin r => c.val ∈ I)).card = I.card := by
    have : ((Finset.univ : Finset (Fin r)).filter (fun c : Fin r => c.val ∈ I)).map
        Fin.valEmbedding = I := by
      ext u
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply]
      constructor
      · rintro ⟨c, hc, rfl⟩; exact hc
      · intro hu; exact ⟨⟨u, hI u hu⟩, hu, rfl⟩
    have h3 := Finset.card_map (s := (Finset.univ : Finset (Fin r)).filter (fun c : Fin r => c.val ∈ I)) (Fin.valEmbedding (n := r))
    rw [this] at h3
    exact h3.symm
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

/-- **Theorem M3D.**  Let `D` be periodic pole data for `p` on `[0, r+2m)`, `I ⊆ [0,r)` a deletion
set, and `[a,b)` a segment with no cut in `(a, b-1]` inside the window `[r, r+p)`.  The
deletion member (core `[0,r) \ I`, border nodes `r+2i`, `r+2j+1`) satisfies
`v_p(den P_{r,I}) ≤ 2(r-|I|) + (2m - (b - a')) + |I|`, `a' = max a (r+2m-p)`. -/
theorem M3D {p r m a b : ℕ} [Fact p.Prime] {Fr : Frame} (D : PoleData Fr p (r + 2 * m))
    (hN : r + 2 * m < p * p) (I : Finset ℕ) (hI : ∀ u ∈ I, u < r)
    (hra : r ≤ a) (hab : a ≤ b) (hb : b ≤ r + 2 * m) (hbp : b ≤ r + p)
    (hj : max a (r + 2 * m - p) ≤ b)
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r D.singular) (min (x : ℤ) y) (max (x : ℤ) y)) :
    GLE p (2 * (r - I.card) + (2 * m - (b - max a (r + 2 * m - p))) + I.card)
      (Rect.FullN Fr (fun i : {c : Fin r // c.val ∉ I} => i.1.val)
        (fun i : Fin m => r + 2 * i.val) (fun j : Fin m => r + 2 * j.val + 1) (X : ℚ[X])).det := by
  set a' := max a (r + 2 * m - p) with ha'
  have hlo : r + 2 * m - p ≤ a' := le_max_right _ _
  have hra' : r ≤ a' := hra.trans (le_max_left _ _)
  have hSle : (I.image (fun u => u % p)).card ≤ I.card := Finset.card_image_le
  have H := member_det_weighted (e := fun i : {c : Fin r // c.val ∉ I} => i.1)
    Subtype.val_injective D hN (Nat.le_add_right r (2 * m))
    (fun z => by have := z.isLt; omega) (fun y => by have := y.isLt; omega)
    (fun z => by omega) (fun y => by omega) (fun z y => by omega)
    (delTable p r m a' b (I.image (fun u => u % p))) (fun z y => delWeight_le_two _ _ _ _ _ _)
    (by
      intro z y hz
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := delWeight_zero hz
      refine ⟨hcut _ _ (le_trans (le_max_left _ _) h1) h2 (le_trans (le_max_left _ _) h3) h4, ?_, ?_⟩
      · intro c hc
        have : c.val ∉ I := fun hcI => h5 (Finset.mem_image.mpr ⟨c.val, hcI, hc⟩)
        exact ⟨⟨c, this⟩, rfl⟩
      · intro c hc
        have : c.val ∉ I := fun hcI => h6 (Finset.mem_image.mpr ⟨c.val, hcI, hc⟩)
        exact ⟨⟨c, this⟩, rfl⟩)
    (fun z y hz => delWeight_one hz)
  have hT := delTable_trop (I.image (fun u => u % p)) hlo hra' hj hb hbp
  rw [card_core I hI] at H
  exact H.mono (by omega)

/-- **M3D, debit form.**  With `P3 = 2r + (2m - (b - a'))` the full-member price,
`v_p(den P_{r,I}) ≤ P3 - |I|`: the debit is `≤ 0`. -/
theorem M3D_debit {p r m a b : ℕ} [Fact p.Prime] {Fr : Frame} (D : PoleData Fr p (r + 2 * m))
    (hN : r + 2 * m < p * p) (I : Finset ℕ) (hI : ∀ u ∈ I, u < r)
    (hra : r ≤ a) (hab : a ≤ b) (hb : b ≤ r + 2 * m) (hbp : b ≤ r + p)
    (hj : max a (r + 2 * m - p) ≤ b)
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r D.singular) (min (x : ℤ) y) (max (x : ℤ) y)) :
    GLE p (2 * r + (2 * m - (b - max a (r + 2 * m - p))) - I.card)
      (Rect.FullN Fr (fun i : {c : Fin r // c.val ∉ I} => i.1.val)
        (fun i : Fin m => r + 2 * i.val) (fun j : Fin m => r + 2 * j.val + 1) (X : ℚ[X])).det := by
  have hk : I.card ≤ r := by
    have : I ⊆ Finset.range r := fun u hu => Finset.mem_range.mpr (hI u hu)
    simpa using Finset.card_le_card this
  exact (M3D D hN I hI hra hab hb hbp hj hcut).mono (by omega)

end CatalanCore.Uniform.Content.Layers.Del
