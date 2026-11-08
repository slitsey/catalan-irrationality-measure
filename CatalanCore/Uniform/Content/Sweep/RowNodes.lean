module

public import CatalanCore.Uniform.Content.Sweep.RowG

@[expose] public section

/-!
# Window family: explicit node form of Theorem G (lane H, wave H2b; ledger P213, P206)

`PLANE2-P1-ROW` §4 for the member with window rows `r + 2 i`, window columns `r + 2 i + 1` (`i < m`) and
retained common nodes `c` below `r`; pivot system `(κ, k')`, `(κ − 1) p ≤ r < κ p`, parity `π = (r+1) % 2`.

* `exists_colNode_iff`, `exists_rowNode_iff`: the pivot nodes are `t < (κ + 2k') p` with `t < κ p` or the
  right parity (Lemma C, `oc_node`).
* `ORs`, `OCs` (outside rows/columns), `TRs = Tdel 1`, `TCs = Tdel 0` (deleted pivot columns/rows at or above
  `r`); `sum_RowOut`, `sum_ColOut`, `sum_DelC`, `sum_DelR`, `card_free` turn the label sums of
  `RowG.member_gle` into sums over these node sets.
* `member_gle_P`: if potentials `φR`, `φC` (`3` below `r`) cover `Wlab` on the four families of pairs
  (deleted pivot / outside, rows / columns) and `3 r + 3 m + Σφ ≤ E + 3 (#TRs + #ORs)`, then
  `GLE p E` of the determinant of the member.  Everything left for `RowE1`, `RowP1` is arithmetic on nodes.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section PivNodes

variable {p : ℕ} [hp : Fact p.Prime] {κ k' σ : ℕ}

/-- The nodes of the pivot columns of the system `σ`. -/
theorem exists_colNode_iff (hodd : p % 2 = 1) (hσ : σ ≤ 1) (t : ℕ) :
    (∃ y : PivIdx p κ k', colNode p κ k' σ y = t) ↔ t < (κ + 2 * k') * p ∧ (t < κ * p ∨ t % 2 = σ) := by
  have hp0 : 0 < p := hp.out.pos
  constructor
  · rintro ⟨y, rfl⟩
    have hj := (mem_Cper (κ := κ) (k' := k')).1 (colPer_mem κ k' _ (oc_le (π := σ) (κ := κ) (p := p) y.1) y.2)
    have hω := y.1.2
    set j := colPer κ k' (oc p κ σ y.1) y.2 with hjdef
    have ht : colNode p κ k' σ y = j * p + y.1 := rfl
    rw [ht]
    refine ⟨by nlinarith [hj.1], ?_⟩
    by_cases hjk : j < κ
    · left; nlinarith
    · have h := hj.2.resolve_left hjk
      right
      have hmod : (j * p + y.1) % p = y.1 := node_mod hω
      have hdiv : (j * p + y.1) / p = j := node_div hp0 hω
      have hoc := oc_node (p := p) (κ := κ) hodd hσ (j * p + y.1)
      rw [hmod, hdiv] at hoc
      by_contra hne
      rw [if_neg hne] at hoc
      omega
  · rintro ⟨h1, h2⟩
    have hmem : t / p ∈ Cper κ k' (oc p κ σ (t % p)) := by
      rw [mem_Cper]
      refine ⟨(Nat.div_lt_iff_lt_mul hp0).2 h1, ?_⟩
      rcases h2 with h | h
      · left; exact (Nat.div_lt_iff_lt_mul hp0).2 h
      · by_cases hj : t / p < κ
        · left; exact hj
        · right
          have hoc := oc_node (p := p) (κ := κ) hodd hσ t
          rw [if_pos h] at hoc
          omega
    obtain ⟨a, ha⟩ := exists_colPer κ k' _ (oc_le (π := σ) (κ := κ) (p := p) _) hmem
    refine ⟨(⟨t % p, Nat.mod_lt _ hp0⟩, a), ?_⟩
    show colPer κ k' (oc p κ σ (t % p)) a * p + t % p = t
    rw [ha]; have := Nat.div_add_mod t p; rw [Nat.mul_comm] at this; exact this

theorem exists_rowNode_iff (hodd : p % 2 = 1) (hσ : σ ≤ 1) (t : ℕ) :
    (∃ y : PivIdx p κ k', rowNode p κ k' σ y = t) ↔ t < (κ + 2 * k') * p ∧ (t < κ * p ∨ t % 2 = 1 - σ) := by
  simp only [rowNode_eq_colNode κ k' σ hσ]
  exact exists_colNode_iff hodd (by omega) t


end PivNodes

section Sets

variable (p κ k' r m : ℕ)

/-- Outside rows: the X-parity window nodes beyond the pivot range. -/
def ORs : Finset ℕ := (Finset.Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 0 ∧ (κ + 2 * k') * p ≤ t)
/-- Outside columns. -/
def OCs : Finset ℕ := (Finset.Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = 1 ∧ (κ + 2 * k') * p ≤ t)
/-- Deleted pivot nodes at or above `r` (`off = 1`: columns, `off = 0`: rows): the nodes of the window
parity `off` beyond the window, and those of the other parity inside the first period range. -/
def Tdel (off : ℕ) : Finset ℕ := (Finset.Ico r ((κ + 2 * k') * p)).filter
  (fun t => ((t - r) % 2 = off ∧ r + 2 * m ≤ t) ∨ ((t - r) % 2 = 1 - off ∧ t < κ * p))
/-- Deleted pivot columns at or above `r`. -/
abbrev TRs : Finset ℕ := Tdel p κ k' r m 1
/-- Deleted pivot rows at or above `r`. -/
abbrev TCs : Finset ℕ := Tdel p κ k' r m 0

end Sets

section SumOmega

variable {p : ℕ} [hp : Fact p.Prime] {κ k' σ : ℕ}

theorem sum_Omega_col (hodd : p % 2 = 1) (hσ : σ ≤ 1) (P : ℕ → Prop) [DecidablePred P] (G : ℕ → ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ k' => P (colNode p κ k' σ y)), G (colNode p κ k' σ y) =
      ∑ t ∈ (Finset.range ((κ + 2 * k') * p)).filter (fun t => (t < κ * p ∨ t % 2 = σ) ∧ P t), G t := by
  have hp0 : 0 < p := hp.out.pos
  refine Finset.sum_nbij (colNode p κ k' σ) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨((exists_colNode_iff hodd hσ _).1 ⟨y, rfl⟩).1, ((exists_colNode_iff hodd hσ _).1 ⟨y, rfl⟩).2, hy⟩
  · intro a _ b _ h; exact colNode_injective hp0 h
  · intro t ht
    have ht := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    rw [Finset.mem_range] at ht
    obtain ⟨y, hy⟩ := (exists_colNode_iff hodd hσ t).2 ⟨ht.1, ht.2.1⟩
    exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hy]; exact ht.2.2⟩, hy⟩

theorem sum_Omega_row (hodd : p % 2 = 1) (hσ : σ ≤ 1) (P : ℕ → Prop) [DecidablePred P] (G : ℕ → ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ k' => P (rowNode p κ k' σ y)), G (rowNode p κ k' σ y) =
      ∑ t ∈ (Finset.range ((κ + 2 * k') * p)).filter (fun t => (t < κ * p ∨ t % 2 = 1 - σ) ∧ P t), G t := by
  have h := sum_Omega_col (p := p) (κ := κ) (k' := k') (σ := 1 - σ) hodd (by omega) P G
  rw [← h]
  refine Finset.sum_congr ?_ (fun y _ => ?_)
  · ext y; simp [rowNode_eq_colNode κ k' σ hσ]
  · rw [rowNode_eq_colNode κ k' σ hσ]

end SumOmega

section Stride

/-- Sum over the stride-2 window nodes `r + 2 i + off` equals a sum over a filter of an interval. -/
theorem sum_stride (r m off : ℕ) (hoff : off ≤ 1) (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℕ) :
    ∑ i ∈ Finset.range m, (if P (r + 2 * i + off) then F (r + 2 * i + off) else 0) =
      ∑ t ∈ (Finset.Ico r (r + 2 * m)).filter (fun t => (t - r) % 2 = off ∧ P t), F t := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij (fun i => r + 2 * i + off) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    simp only [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, by omega, hi.2⟩
  · intro a _ b _ h; simp only at h; omega
  · intro t ht
    have ht := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    rw [Finset.mem_Ico] at ht
    refine ⟨(t - r - off) / 2, ?_, by show r + 2 * ((t - r - off) / 2) + off = t; omega⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), ?_⟩
    have : r + 2 * ((t - r - off) / 2) + off = t := by omega
    rw [this]; exact ht.2.2

end Stride

section Reduce

variable {p : ℕ} [hp : Fact p.Prime] {κ k' r m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)

/-- Outside rows of the member: the window rows beyond the pivot range (for `π = (r+1) % 2`). -/
theorem sum_RowOut (hodd : p % 2 = 1) (hκr : r < κ * p) (hκH : κ * p ≤ (κ + 2 * k') * p)
    (hcr : ∀ i, c i < r) (f : ℕ → ℕ) :
    ∑ a ∈ Finset.univ.filter (fun a : ι ⊕ Fin m =>
        ¬ ∃ x : PivIdx p κ k', rowNode p κ k' ((r + 1) % 2) x = memRow c (fun i : Fin m => r + 2 * (i : ℕ)) a),
      f (memRow c (fun i : Fin m => r + 2 * (i : ℕ)) a) = ∑ t ∈ ORs p κ k' r m, f t := by
  classical
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have h1 : ∀ i : ι, (if ¬ ∃ x : PivIdx p κ k' , rowNode p κ k' ((r + 1) % 2) x = memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inl i)
      then f (memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inl i)) else 0) = 0 := by
    intro i
    rw [if_neg]
    push_neg
    simp only [memRow, Sum.elim_inl]
    rw [exists_rowNode_iff hodd hπ]
    exact ⟨by nlinarith [hcr i], Or.inl (by nlinarith [hcr i])⟩
  have h2 : ∀ j : Fin m, (if ¬ ∃ x : PivIdx p κ k' , rowNode p κ k' ((r + 1) % 2) x = memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inr j)
      then f (memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inr j)) else 0) =
      (if (κ + 2 * k') * p ≤ r + 2 * (j : ℕ) + 0 then f (r + 2 * (j : ℕ) + 0) else 0) := by
    intro j
    have hex : (∃ x : PivIdx p κ k', rowNode p κ k' ((r + 1) % 2) x = r + 2 * (j : ℕ)) ↔
        r + 2 * (j : ℕ) < (κ + 2 * k') * p := by
      rw [exists_rowNode_iff hodd hπ]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, Or.inr (by omega)⟩
    by_cases h : (κ + 2 * k') * p ≤ r + 2 * (j : ℕ) + 0
    · have hn : ¬ ∃ x : PivIdx p κ k', rowNode p κ k' ((r + 1) % 2) x = memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inr j) := by
        intro hx
        have := hex.1 hx
        omega
      rw [if_pos hn, if_pos h]; rfl
    · have hn : ¬ ¬ ∃ x : PivIdx p κ k', rowNode p κ k' ((r + 1) % 2) x = memRow c (fun i : Fin m => r + 2 * (i : ℕ)) (Sum.inr j) := by
        intro hx
        apply hx
        exact hex.2 (by omega)
      rw [if_neg hn, if_neg h]
  rw [Finset.sum_eq_zero (fun i _ => h1 i), zero_add, Finset.sum_congr rfl (fun j _ => h2 j),
    Fin.sum_univ_eq_sum_range (fun j => if (κ + 2 * k') * p ≤ r + 2 * j + 0 then f (r + 2 * j + 0) else 0) m,
    sum_stride r m 0 (by norm_num) (fun t => (κ + 2 * k') * p ≤ t) f]
  rfl

end Reduce

section Del

variable {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)

theorem card_free (hcinj : Function.Injective c) (r : ℕ) (hcr : ∀ i, c i < r) :
    ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card = r - Fintype.card ι := by
  classical
  have h1 : (Finset.range r).filter (fun t => ∀ i, t ≠ c i) = Finset.range r \ Finset.univ.image c := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
      true_and, not_exists]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i h => h2 i h.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun i h => h2 i h.symm⟩
  rw [h1, Finset.card_sdiff_of_subset, Finset.card_range, Finset.card_image_of_injective _ hcinj,
    Finset.card_univ]
  intro t ht
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ht
  obtain ⟨i, rfl⟩ := ht
  exact Finset.mem_range.2 (hcr i)

/-- The sum over the deleted pivot nodes. -/
theorem sum_del_aux (p κ k' r m off : ℕ) (hoff : off ≤ 1) (hκr : r < κ * p)
    (hκH : κ * p ≤ (κ + 2 * k') * p) (hcr : ∀ i, c i < r) (G : ℕ → ℕ) :
    ∑ t ∈ (Finset.range ((κ + 2 * k') * p)).filter
        (fun t => (t < κ * p ∨ t % 2 = (r + off) % 2) ∧
          ∀ b : ι ⊕ Fin m, t ≠ Sum.elim c (fun j : Fin m => r + 2 * (j : ℕ) + off) b), G t =
      ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), G t + ∑ t ∈ Tdel p κ k' r m off, G t := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_range_add_sum_Ico _ (show r ≤ (κ + 2 * k') * p by omega)]
  congr 1
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht := Finset.mem_range.1 ht
    have hiff : ((t < κ * p ∨ t % 2 = (r + off) % 2) ∧
        ∀ b : ι ⊕ Fin m, t ≠ Sum.elim c (fun j : Fin m => r + 2 * (j : ℕ) + off) b) ↔ ∀ i, t ≠ c i := by
      constructor
      · rintro ⟨_, h⟩ i; exact h (Sum.inl i)
      · intro h
        refine ⟨Or.inl (by omega), ?_⟩
        rintro (i | j)
        · exact h i
        · simp only [Sum.elim_inr]; omega
    by_cases h : ∀ i, t ≠ c i
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  · rw [Tdel, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_Ico] at ht
    have hiff : ((t < κ * p ∨ t % 2 = (r + off) % 2) ∧
        ∀ b : ι ⊕ Fin m, t ≠ Sum.elim c (fun j : Fin m => r + 2 * (j : ℕ) + off) b) ↔
        (((t - r) % 2 = off ∧ r + 2 * m ≤ t) ∨ ((t - r) % 2 = 1 - off ∧ t < κ * p)) := by
      constructor
      · rintro ⟨h1, h2⟩
        by_cases hpar : (t - r) % 2 = off
        · left
          refine ⟨hpar, ?_⟩
          by_contra hlt
          have hlt : t < r + 2 * m := by omega
          have := h2 (Sum.inr ⟨(t - r - off) / 2, by omega⟩)
          simp only [Sum.elim_inr] at this
          apply this; omega
        · right
          refine ⟨by omega, ?_⟩
          rcases h1 with h1 | h1
          · exact h1
          · omega
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · refine ⟨Or.inr (by omega), ?_⟩
          rintro (i | j)
          · have := hcr i; simp only [Sum.elim_inl]; omega
          · simp only [Sum.elim_inr]; omega
        · refine ⟨Or.inl h2, ?_⟩
          rintro (i | j)
          · have := hcr i; simp only [Sum.elim_inl]; omega
          · simp only [Sum.elim_inr]; omega
    by_cases h : ((t - r) % 2 = off ∧ r + 2 * m ≤ t) ∨ ((t - r) % 2 = 1 - off ∧ t < κ * p)
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

end Del

section Reduce2

variable {p : ℕ} [hp : Fact p.Prime] {κ k' r m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ)

theorem sum_ColOut (hodd : p % 2 = 1) (hκr : r < κ * p) (hκH : κ * p ≤ (κ + 2 * k') * p)
    (hcr : ∀ i, c i < r) (f : ℕ → ℕ) :
    ∑ b ∈ Finset.univ.filter (fun b : ι ⊕ Fin m =>
        ¬ ∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) b),
      f (memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) b) = ∑ t ∈ OCs p κ k' r m, f t := by
  classical
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  rw [Finset.sum_filter, Fintype.sum_sum_type]
  have h1 : ∀ i : ι, (if ¬ ∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inl i)
      then f (memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inl i)) else 0) = 0 := by
    intro i
    rw [if_neg]
    push_neg
    simp only [memCol, Sum.elim_inl]
    rw [exists_colNode_iff hodd hπ]
    exact ⟨by nlinarith [hcr i], Or.inl (by nlinarith [hcr i])⟩
  have h2 : ∀ j : Fin m, (if ¬ ∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inr j)
      then f (memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inr j)) else 0) =
      (if (κ + 2 * k') * p ≤ r + 2 * (j : ℕ) + 1 then f (r + 2 * (j : ℕ) + 1) else 0) := by
    intro j
    have hex : (∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = r + 2 * (j : ℕ) + 1) ↔
        r + 2 * (j : ℕ) + 1 < (κ + 2 * k') * p := by
      rw [exists_colNode_iff hodd hπ]
      constructor
      · intro h; exact h.1
      · intro h; exact ⟨h, Or.inr (by omega)⟩
    by_cases h : (κ + 2 * k') * p ≤ r + 2 * (j : ℕ) + 1
    · have hn : ¬ ∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inr j) := by
        intro hx
        have := hex.1 hx
        omega
      rw [if_pos hn, if_pos h]; rfl
    · have hn : ¬ ¬ ∃ y : PivIdx p κ k', colNode p κ k' ((r + 1) % 2) y = memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Sum.inr j) := by
        intro hx
        apply hx
        exact hex.2 (by omega)
      rw [if_neg hn, if_neg h]
  rw [Finset.sum_eq_zero (fun i _ => h1 i), zero_add, Finset.sum_congr rfl (fun j _ => h2 j),
    Fin.sum_univ_eq_sum_range (fun j => if (κ + 2 * k') * p ≤ r + 2 * j + 1 then f (r + 2 * j + 1) else 0) m,
    sum_stride r m 1 (by norm_num) (fun t => (κ + 2 * k') * p ≤ t) f]
  rfl

theorem sum_DelC (hodd : p % 2 = 1) (hκr : r < κ * p) (hκH : κ * p ≤ (κ + 2 * k') * p)
    (hcr : ∀ i, c i < r) (G : ℕ → ℕ) :
    ∑ y ∈ Finset.univ.filter (fun y : PivIdx p κ k' =>
        ∀ b, colNode p κ k' ((r + 1) % 2) y ≠ memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) b),
      G (colNode p κ k' ((r + 1) % 2) y) =
      ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), G t + ∑ t ∈ TRs p κ k' r m, G t := by
  classical
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  refine (sum_Omega_col hodd hπ (fun t => ∀ b, t ≠ memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) b) G).trans ?_
  exact sum_del_aux c p κ k' r m 1 (by norm_num) hκr hκH hcr G

theorem sum_DelR (hodd : p % 2 = 1) (hκr : r < κ * p) (hκH : κ * p ≤ (κ + 2 * k') * p)
    (hcr : ∀ i, c i < r) (G : ℕ → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : PivIdx p κ k' =>
        ∀ a, rowNode p κ k' ((r + 1) % 2) x ≠ memRow c (fun i : Fin m => r + 2 * (i : ℕ)) a),
      G (rowNode p κ k' ((r + 1) % 2) x) =
      ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), G t + ∑ t ∈ TCs p κ k' r m, G t := by
  classical
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  refine (sum_Omega_row hodd hπ (fun t => ∀ b, t ≠ memRow c (fun i : Fin m => r + 2 * (i : ℕ)) b) G).trans ?_
  have h := sum_del_aux c p κ k' r m 0 (by norm_num) hκr hκH hcr G
  have e : 1 - (r + 1) % 2 = (r + 0) % 2 := by omega
  rw [e]
  simpa [memRow] using h

end Reduce2

section MemberP

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N' : ℕ}

/-- **Theorem G for the window family, in explicit node form.**  Window rows `r + 2 i`, columns
`r + 2 i + 1` (`i < m`), retained common nodes `c` below `r`, pivot system `(κ, k')` with
`(κ − 1) p ≤ r < κ p` and parity `π = (r + 1) % 2`.  The label nodes are the outside rows `ORs`, the
outside columns `OCs`, the deleted pivot columns `TRs` and the deleted pivot rows `TCs` at or above `r`
(the deleted common nodes below `r` carry the potential `3`).  If the potentials cover `Wlab` on the four
families of pairs and `hsum` holds, every coefficient of the determinant has denominator at most `E`. -/
theorem member_gle_P (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N' < p * p)
    {r m κ k' : ℕ} (hκr : r < κ * p) (hH : (κ + 2 * k') * p ≤ N')
    (hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ N')
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (φR φC : ℕ → ℕ) (hφ : ∀ t, t < r → φR t = 3 ∧ φC t = 3)
    (hpp : ∀ n ∈ TRs p κ k' r m, ∀ n' ∈ TCs p κ k' r m,
      Wlab u p false false (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ φR n + φC n')
    (hpo : ∀ n ∈ TRs p κ k' r m, ∀ n' ∈ OCs p κ k' r m,
      Wlab u p false true (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ φR n + φC n')
    (hop : ∀ n ∈ ORs p κ k' r m, ∀ n' ∈ TCs p κ k' r m,
      Wlab u p true false (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ φR n + φC n')
    (hoo : ∀ n ∈ ORs p κ k' r m, ∀ n' ∈ OCs p κ k' r m,
      Wlab u p true true (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n' ≤ φR n + φC n')
    (E : ℕ)
    (hsum : 3 * r + 3 * m + (∑ t ∈ TRs p κ k' r m, φR t + ∑ t ∈ ORs p κ k' r m, φR t +
        ∑ t ∈ TCs p κ k' r m, φC t + ∑ t ∈ OCs p κ k' r m, φC t) ≤
      E + 3 * ((TRs p κ k' r m).card + (ORs p κ k' r m).card)) :
    GLE p E (seqFullN (fS v u) (eS v u) c
      (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  have hπ : (r + 1) % 2 ≤ 1 := by omega
  have hκH : κ * p ≤ (κ + 2 * k') * p := Nat.mul_le_mul_right p (by omega)
  have hxinj : Function.Injective (fun i : Fin m => r + 2 * (i : ℕ)) := by
    intro i j h; apply Fin.ext; simp only at h; omega
  have hyinj : Function.Injective (fun i : Fin m => r + 2 * (i : ℕ) + 1) := by
    intro i j h; apply Fin.ext; simp only at h; omega
  have h1 : ∀ (i : ι) (j : Fin m), c i ≠ r + 2 * (j : ℕ) + 1 := by
    intro i j; have := hcr i; omega
  have h2 : ∀ (i : Fin m) (j : ι), r + 2 * (i : ℕ) ≠ c j := by
    intro i j; have := hcr j; omega
  have h3 : ∀ (i j : Fin m), r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by
    intro i j; omega
  have hrow : ∀ a, memRow c (fun i : Fin m => r + 2 * (i : ℕ)) a < r + 2 * m := by
    rintro (i | i)
    · have := hcr i; simp only [memRow, Sum.elim_inl]; omega
    · have := i.2; simp only [memRow, Sum.elim_inr]; omega
  have hcol : ∀ a, memCol c (fun i : Fin m => r + 2 * (i : ℕ) + 1) a < r + 2 * m := by
    rintro (i | i)
    · have := hcr i; simp only [memCol, Sum.elim_inl]; omega
    · have := i.2; simp only [memCol, Sum.elim_inr]; omega
  have hcardι : Fintype.card ι ≤ r := by
    have := Fintype.card_le_of_injective (fun i => (⟨c i, hcr i⟩ : Fin r)) (by
      intro i j h; apply hcinj; simpa using congrArg Fin.val h)
    simpa using this
  have hfree := card_free c hcinj r hcr
  refine member_gle (p := p) (π := (r + 1) % 2) (κ := κ) (k' := k') v u c
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) hpv hodd hp5 hN hH hπ hcinj hxinj
    hyinj h1 h2 h3 (fun a => hcompl _ (hrow a)) (fun a => hcompl _ (hcol a)) φR φC ?_ E ?_
  · -- the weights
    intro n n' kR kC hR hC
    have hRc : (kR = true ∧ n ∈ ORs p κ k' r m) ∨ (kR = false ∧ (n < r ∨ n ∈ TRs p κ k' r m)) := by
      rcases hR with ⟨hk, a, hna, hnp⟩ | ⟨hk, y, hyn, hb⟩
      · left
        refine ⟨hk, ?_⟩
        rcases a with i | j
        · exfalso
          apply hnp
          simp only [memRow, Sum.elim_inl] at hna
          rw [← hna, exists_rowNode_iff hodd hπ]
          exact ⟨by have := hcr i; nlinarith, Or.inl (by have := hcr i; nlinarith)⟩
        · simp only [memRow, Sum.elim_inr] at hna
          rw [exists_rowNode_iff hodd hπ] at hnp
          have hj := j.2
          unfold ORs
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
          by_contra hlt
          apply hnp
          exact ⟨by omega, Or.inr (by omega)⟩
      · right
        refine ⟨hk, ?_⟩
        obtain ⟨hyn1, hyn2⟩ := (exists_colNode_iff hodd hπ n).1 ⟨y, hyn⟩
        by_cases hr : n < r
        · exact Or.inl hr
        · right
          unfold TRs Tdel
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, hyn1⟩, ?_⟩
          by_cases hpar : (n - r) % 2 = 1
          · left
            refine ⟨hpar, ?_⟩
            by_contra hlt
            have hlt : n < r + 2 * m := by omega
            exact hb (Sum.inr ⟨(n - r - 1) / 2, by omega⟩) (by simp only [memCol, Sum.elim_inr]; omega)
          · right
            exact ⟨by omega, by omega⟩
    have hCc : (kC = true ∧ n' ∈ OCs p κ k' r m) ∨ (kC = false ∧ (n' < r ∨ n' ∈ TCs p κ k' r m)) := by
      rcases hC with ⟨hk, a, hna, hnp⟩ | ⟨hk, x, hxn, hb⟩
      · left
        refine ⟨hk, ?_⟩
        rcases a with i | j
        · exfalso
          apply hnp
          simp only [memCol, Sum.elim_inl] at hna
          rw [← hna, exists_colNode_iff hodd hπ]
          exact ⟨by have := hcr i; nlinarith, Or.inl (by have := hcr i; nlinarith)⟩
        · simp only [memCol, Sum.elim_inr] at hna
          rw [exists_colNode_iff hodd hπ] at hnp
          have hj := j.2
          unfold OCs
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, by omega⟩, by omega, ?_⟩
          by_contra hlt
          apply hnp
          exact ⟨by omega, Or.inr (by omega)⟩
      · right
        refine ⟨hk, ?_⟩
        obtain ⟨hxn1, hxn2⟩ := (exists_rowNode_iff hodd hπ n').1 ⟨x, hxn⟩
        by_cases hr : n' < r
        · exact Or.inl hr
        · right
          unfold TCs Tdel
          rw [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨⟨by omega, hxn1⟩, ?_⟩
          by_cases hpar : (n' - r) % 2 = 0
          · left
            refine ⟨hpar, ?_⟩
            by_contra hlt
            have hlt : n' < r + 2 * m := by omega
            exact hb (Sum.inr ⟨(n' - r) / 2, by omega⟩) (by simp only [memRow, Sum.elim_inr]; omega)
          · right
            exact ⟨by omega, by omega⟩
    have hle := Wlab_le u p kR kC (oc p κ ((r + 1) % 2) (n % p)) (oc p κ (1 - (r + 1) % 2) (n' % p)) n n'
    rcases hRc with ⟨rfl, hn⟩ | ⟨rfl, hn | hn⟩
    · rcases hCc with ⟨rfl, hn'⟩ | ⟨rfl, hn' | hn'⟩
      · exact hoo n hn n' hn'
      · have := (hφ n' hn').2; omega
      · exact hop n hn n' hn'
    · have := (hφ n hn).1; omega
    · rcases hCc with ⟨rfl, hn'⟩ | ⟨rfl, hn' | hn'⟩
      · exact hpo n hn n' hn'
      · have := (hφ n' hn').2; omega
      · exact hpp n hn n' hn'
  · -- the sum condition
    have eR := sum_RowOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φR
    have eR1 := sum_RowOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have eC := sum_ColOut (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φC
    have dC := sum_DelC (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φR
    have dC1 := sum_DelC (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr (fun _ => 1)
    have dR := sum_DelR (p := p) (κ := κ) (k' := k') (m := m) c hodd hκr hκH hcr φC
    have hF3 : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φR t =
        3 * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).1
      omega
    have hF3' : ∑ t ∈ (Finset.range r).filter (fun t => ∀ i, t ≠ c i), φC t =
        3 * ((Finset.range r).filter (fun t => ∀ i, t ≠ c i)).card := by
      rw [Finset.card_eq_sum_ones, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      have := (hφ t (Finset.mem_range.1 (Finset.mem_filter.1 ht).1)).2
      omega
    simp only [Finset.sum_const, smul_eq_mul, mul_one, ← Finset.card_eq_sum_ones] at eR1 dC1
    rw [Fintype.card_sum, Fintype.card_fin]
    rw [hF3] at dC
    rw [hF3'] at dR
    omega

end MemberP

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.member_gle_P
#print axioms CatalanCore.Uniform.Content.Sweep.exists_colNode_iff
