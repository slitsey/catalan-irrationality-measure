module
public import CatalanCore.Uniform.Frame.Family
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Floor.Ring
@[expose] public section

namespace CatalanCore.Uniform
open Finset

/-- A single residue of a fixed rational periodic block. A residue-set block is
expanded into finitely many of these, preserving arbitrary fixed periodic data. -/
structure PeriodicBlock where
  u : ℚ
  v : ℚ
  d : ℕ
  residue : ℕ
  hu : 0 ≤ u
  huv : u < v
  hd : 0 < d
  hresidue : residue < d

namespace PeriodicBlock

def lower (b : PeriodicBlock) (r : ℕ) : ℕ :=
  ⌈(b.u * r - b.residue) / b.d⌉₊
def upper (b : PeriodicBlock) (r : ℕ) : ℕ :=
  ⌈(b.v * r - b.residue) / b.d⌉₊

def nodes (b : PeriodicBlock) (r : ℕ) : Finset ℕ :=
  (Finset.Ico (b.lower r) (b.upper r)).image (fun k => b.d * k + b.residue)

def mass (b : PeriodicBlock) : ℚ := (b.v - b.u) / b.d

theorem mass_pos (b : PeriodicBlock) : 0 < b.mass := by
  unfold mass
  exact div_pos (sub_pos.mpr b.huv) (by exact_mod_cast b.hd)

theorem lower_le_upper (b : PeriodicBlock) (r : ℕ) : b.lower r ≤ b.upper r := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast b.hd.le)
  have : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  nlinarith [b.huv]

theorem card_nodes (b : PeriodicBlock) (r : ℕ) :
    (b.nodes r).card = b.upper r - b.lower r := by
  unfold nodes
  rw [Finset.card_image_of_injective, Nat.card_Ico]
  intro a c hac
  have hmul : b.d * a = b.d * c := Nat.add_right_cancel hac
  exact Nat.eq_of_mul_eq_mul_left b.hd hmul

private theorem ceil_lt_add_one_of_gt_neg_one {a : ℚ} (ha : -1 < a) :
    (⌈a⌉₊ : ℚ) < a + 1 := by
  by_cases h : 0 ≤ a
  · exact Nat.ceil_lt_add_one h
  · have heq : ⌈a⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by linarith)
    rw [heq]; norm_num; linarith

/-- Exact finite count differs from its mass times scale by less than one. -/
theorem count_bounds (b : PeriodicBlock) (r : ℕ) :
    b.mass * r - 1 < ((b.nodes r).card : ℚ) ∧
      ((b.nodes r).card : ℚ) < b.mass * r + 1 := by
  have hd : (0 : ℚ) < b.d := by exact_mod_cast b.hd
  have hs : (b.residue : ℚ) < b.d := by exact_mod_cast b.hresidue
  have hr : (0 : ℚ) ≤ r := Nat.cast_nonneg _
  have hu : -1 < (b.u * r - b.residue) / b.d := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith [b.hu]
  have hv : -1 < (b.v * r - b.residue) / b.d := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith [b.hu, b.huv]
  have hlo := Nat.le_ceil ((b.u * r - b.residue) / b.d)
  have hhi := Nat.le_ceil ((b.v * r - b.residue) / b.d)
  have hlo' := ceil_lt_add_one_of_gt_neg_one hu
  have hhi' := ceil_lt_add_one_of_gt_neg_one hv
  change (b.u * r - b.residue) / b.d ≤ (b.lower r : ℚ) at hlo
  change (b.v * r - b.residue) / b.d ≤ (b.upper r : ℚ) at hhi
  change (b.lower r : ℚ) < (b.u * r - b.residue) / b.d + 1 at hlo'
  change (b.upper r : ℚ) < (b.v * r - b.residue) / b.d + 1 at hhi'
  have hdiff : (b.v * r - b.residue) / b.d - (b.u * r - b.residue) / b.d =
      b.mass * r := by unfold mass; ring
  rw [b.card_nodes, Nat.cast_sub (b.lower_le_upper r)]
  constructor <;> linarith

/-- The residue parametrization describes precisely the intended half-open block. -/
theorem mem_nodes (b : PeriodicBlock) (r j : ℕ) :
    j ∈ b.nodes r ↔ b.u * r ≤ (j : ℚ) ∧ (j : ℚ) < b.v * r ∧ j % b.d = b.residue := by
  have hd : (0 : ℚ) < b.d := by exact_mod_cast b.hd
  constructor
  · intro hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk
    have hlo' : (b.u * r - b.residue) / b.d ≤ (k : ℚ) :=
      (Nat.ceil_le).mp hlo
    have hhi' : (k : ℚ) < (b.v * r - b.residue) / b.d := Nat.lt_ceil.mp hhi
    have hlo'' := (div_le_iff₀ hd).mp hlo'
    have hhi'' := (lt_div_iff₀ hd).mp hhi'
    refine ⟨?_, ?_, ?_⟩
    · push_cast; nlinarith
    · push_cast; nlinarith
    · simp [Nat.add_mod, Nat.mod_eq_of_lt b.hresidue]
  · rintro ⟨hlo, hhi, hmod⟩
    have hj : b.d * (j / b.d) + b.residue = j := by
      simpa [hmod, Nat.add_comm] using Nat.mod_add_div j b.d
    apply Finset.mem_image.mpr
    refine ⟨j / b.d, Finset.mem_Ico.mpr ⟨?_, ?_⟩, hj⟩
    · apply Nat.ceil_le.mpr
      apply (div_le_iff₀ hd).mpr
      have hjQ : (b.d : ℚ) * (j / b.d : ℕ) + b.residue = j := by exact_mod_cast hj
      nlinarith
    · apply Nat.lt_ceil.mpr
      apply (lt_div_iff₀ hd).mpr
      have hjQ : (b.d : ℚ) * (j / b.d : ℕ) + b.residue = j := by exact_mod_cast hj
      nlinarith

end PeriodicBlock
/-- Finite disjoint periodic data; separation is a finite-geometry condition,
not a hypothesis about an asymptotic determinant or its analytic error. -/
structure BlockCollection where
  n : ℕ
  block : Fin n → PeriodicBlock
  separated : ∀ r, Pairwise (fun i j => Disjoint ((block i).nodes r) ((block j).nodes r))

namespace BlockCollection

def nodes (B : BlockCollection) (r : ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => (B.block i).nodes r)

def mass (B : BlockCollection) : ℚ := ∑ i, (B.block i).mass

theorem card_nodes (B : BlockCollection) (r : ℕ) :
    (B.nodes r).card = ∑ i, ((B.block i).nodes r).card := by
  apply Finset.card_biUnion
  intro i hi j hj hij
  exact B.separated r hij

/-- Explicit finite rounding bounds, including empty collections. -/
theorem count_bounds (B : BlockCollection) (r : ℕ) :
    B.mass * r - B.n ≤ ((B.nodes r).card : ℚ) ∧
      ((B.nodes r).card : ℚ) ≤ B.mass * r + B.n := by
  have hlo : ∑ i : Fin B.n, ((B.block i).mass * r - 1) ≤
      ∑ i : Fin B.n, (((B.block i).nodes r).card : ℚ) :=
    Finset.sum_le_sum fun i _ => ((B.block i).count_bounds r).1.le
  have hhi : ∑ i : Fin B.n, (((B.block i).nodes r).card : ℚ) ≤
      ∑ i : Fin B.n, ((B.block i).mass * r + 1) :=
    Finset.sum_le_sum fun i _ => ((B.block i).count_bounds r).2.le
  rw [B.card_nodes]
  push_cast
  simpa [mass, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]
    using And.intro hlo hhi

end BlockCollection

/-- Keep the smallest `k` nodes. All trim choices are made before any decay data. -/
def keepNodes (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  ((s.sort (· ≤ ·)).take k).toFinset

theorem keepNodes_subset (s : Finset ℕ) (k : ℕ) : keepNodes s k ⊆ s := by
  intro j hj
  have hj' := List.mem_of_mem_take (List.mem_toFinset.mp hj)
  exact (Finset.mem_sort (· ≤ ·)).mp hj'

theorem card_keepNodes (s : Finset ℕ) (k : ℕ) :
    (keepNodes s k).card = min k s.card := by
  have hnodup : ((s.sort (· ≤ ·)).take k).Nodup := (Finset.sort_nodup s _).take
  rw [keepNodes, List.toFinset_card_of_nodup hnodup, List.length_take, Finset.length_sort]

/-- Any predetermined valid balancing trim policy. The source theorem is not
restricted to keeping the smallest nodes. -/
structure TrimPolicy where
  keep : Finset ℕ → ℕ → Finset ℕ
  subset : ∀ s k, keep s k ⊆ s
  card : ∀ s k, (keep s k).card = min k s.card

def TrimPolicy.smallest : TrimPolicy where
  keep := keepNodes
  subset := keepNodes_subset
  card := card_keepNodes
/-- General rational periodic blocks with positive common density. Border
balance is imposed only on their exact rational masses; finite counts are
balanced by the explicit bounded trimming operation. -/
structure BlockGeom where
  common : BlockCollection
  row : BlockCollection
  column : BlockCollection
  common_pos : 0 < common.mass
  border_mass : row.mass = column.mass
  trim : TrimPolicy := TrimPolicy.smallest
  disjCR : ∀ r, Disjoint (common.nodes r) (row.nodes r)
  disjCC : ∀ r, Disjoint (common.nodes r) (column.nodes r)
  disjRC : ∀ r, Disjoint (row.nodes r) (column.nodes r)

namespace BlockGeom

def borderSize (G : BlockGeom) (r : ℕ) : ℕ := min (G.row.nodes r).card (G.column.nodes r).card

def geometry (G : BlockGeom) (r : ℕ) : Rect.Geometry where
  C := G.common.nodes r
  X' := G.trim.keep (G.row.nodes r) (G.borderSize r)
  Y' := G.trim.keep (G.column.nodes r) (G.borderSize r)
  disjCX := (G.disjCR r).mono_right (G.trim.subset _ _)
  disjCY := (G.disjCC r).mono_right (G.trim.subset _ _)
  disjXY := (G.disjRC r).mono (G.trim.subset _ _) (G.trim.subset _ _)
  card_eq := by
    rw [G.trim.card, G.trim.card]
    unfold borderSize
    omega

/-- The actual common-node count has an explicit O(1) error. -/
theorem card_common (G : BlockGeom) (r : ℕ) :
    G.common.mass * r - G.common.n ≤ ((G.geometry r).C.card : ℚ) ∧
      ((G.geometry r).C.card : ℚ) ≤ G.common.mass * r + G.common.n :=
  G.common.count_bounds r

/-- Only a bounded number of border nodes are removed. -/
theorem trim_bound (G : BlockGeom) (r : ℕ) :
    (G.row.nodes r).card - (G.geometry r).X'.card ≤ G.row.n + G.column.n ∧
    (G.column.nodes r).card - (G.geometry r).Y'.card ≤ G.row.n + G.column.n := by
  have hx := G.row.count_bounds r
  have hy := G.column.count_bounds r
  rw [G.border_mass] at hx
  have hxy : (G.row.nodes r).card ≤ (G.column.nodes r).card + (G.row.n + G.column.n) := by
    have : ((G.row.nodes r).card : ℚ) ≤
        (G.column.nodes r).card + (G.row.n + G.column.n) := by linarith
    exact_mod_cast this
  have hyx : (G.column.nodes r).card ≤ (G.row.nodes r).card + (G.row.n + G.column.n) := by
    have : ((G.column.nodes r).card : ℚ) ≤
        (G.row.nodes r).card + (G.row.n + G.column.n) := by linarith
    exact_mod_cast this
  change (G.row.nodes r).card - (G.trim.keep _ _).card ≤ _ ∧
    (G.column.nodes r).card - (G.trim.keep _ _).card ≤ _
  rw [G.trim.card, G.trim.card]
  unfold borderSize
  omega

noncomputable abbrev family (G : BlockGeom) (Fr : Frame) (depth : ℕ) : PolyFamily :=
  NodeFamily.family Fr G.geometry depth

abbrev scale (G : BlockGeom) (i : NodeFamily.Index G.geometry) : ℕ := i.1

/-- The family degree budget is bounded in the original physical scale. -/
theorem degree_bound (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    (i : (G.family Fr depth).ι) :
    ((G.family Fr depth).deg i : ℝ) ≤
      (G.common.mass : ℝ) * G.scale i + G.common.n := by
  have hd := NodeFamily.degree_le_common Fr G.geometry depth i
  have hc := (G.card_common i.1).2
  have hdc : ((G.family Fr depth).deg i : ℚ) ≤ (G.geometry i.1).C.card := by
    exact_mod_cast hd
  have : ((G.family Fr depth).deg i : ℚ) ≤
      G.common.mass * i.1 + G.common.n := hdc.trans hc
  exact_mod_cast this

end BlockGeom
end CatalanCore.Uniform




