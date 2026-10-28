module

public import CatalanCore.Uniform.Content.Wire.Shape
public import CatalanCore.Uniform.Content.Shape.Keep

@[expose] public section

/-!
# The alternating block geometry is hybrid-shaped at every even scale (lane H7)

`altGeom c`: common block `[0, r)`, row block `{even j : r ≤ j < (1+c) r}` and column block
`{odd j : r ≤ j < (1+c) r}` (modulus `2`).  Its geometry is exactly `HybShape` at every even `r`:
`xs i = r + 2 i`, `ys i = r + 2 i + 1`, with `m = min ⌈c r / 2⌉ ⌈(c r - 1)/2⌉`.
At odd `r` the parities swap (`xs i = r + 1 + 2 i`, `ys i = r + 2 i`), so `HybShape` fails there;
`altGeom_not_hybShape_odd` records this.
-/

namespace CatalanCore.Uniform.Content.Shape

open Finset CatalanCore.Uniform CatalanCore.Uniform.Content.Wire

def commonB : PeriodicBlock := ⟨0, 1, 1, 0, le_refl _, by norm_num, one_pos, one_pos⟩
def rowB (c : ℚ) (hc : 0 < c) : PeriodicBlock :=
  ⟨1, 1 + c, 2, 0, zero_le_one, by linarith, two_pos, by norm_num⟩
def colB (c : ℚ) (hc : 0 < c) : PeriodicBlock :=
  ⟨1, 1 + c, 2, 1, zero_le_one, by linarith, two_pos, by norm_num⟩

def single (b : PeriodicBlock) : BlockCollection :=
  ⟨1, fun _ => b, fun _ i j h => absurd (Subsingleton.elim i j) h⟩

theorem univ_fin_one : (Finset.univ : Finset (Fin 1)) = {0} := by decide

theorem single_nodes (b : PeriodicBlock) (r : ℕ) : (single b).nodes r = b.nodes r := by
  show (Finset.univ : Finset (Fin 1)).biUnion (fun _ => b.nodes r) = _
  rw [univ_fin_one, Finset.singleton_biUnion]

theorem single_mass (b : PeriodicBlock) : (single b).mass = b.mass := by
  show ∑ _i : Fin 1, b.mass = _
  rw [univ_fin_one, Finset.sum_singleton]

theorem commonB_nodes (r : ℕ) : commonB.nodes r = Finset.range r := by
  ext j
  rw [PeriodicBlock.mem_nodes]
  simp [commonB, Nat.mod_one]

/-- The alternating block geometry. -/
def altGeom (c : ℚ) (hc : 0 < c) : BlockGeom where
  common := single commonB
  row := single (rowB c hc)
  column := single (colB c hc)
  common_pos := by simp [single_mass, PeriodicBlock.mass, commonB]
  border_mass := by simp [single_mass, PeriodicBlock.mass, rowB, colB]
  disjCR := by
    intro r
    simp only [single_nodes]
    rw [Finset.disjoint_left]
    intro j h1 h2
    rw [PeriodicBlock.mem_nodes] at h1 h2
    simp only [commonB, rowB] at h1 h2
    linarith [h1.2.1, h2.1]
  disjCC := by
    intro r
    simp only [single_nodes]
    rw [Finset.disjoint_left]
    intro j h1 h2
    rw [PeriodicBlock.mem_nodes] at h1 h2
    simp only [commonB, colB] at h1 h2
    linarith [h1.2.1, h2.1]
  disjRC := by
    intro r
    simp only [single_nodes]
    rw [Finset.disjoint_left]
    intro j h1 h2
    rw [PeriodicBlock.mem_nodes] at h1 h2
    simp only [rowB, colB] at h1 h2
    omega

variable (c : ℚ) (hc : 0 < c)

theorem rowB_nodes {r : ℕ} (hr : r % 2 = 0) :
    (rowB c hc).nodes r = (Finset.range ⌈c * r / 2⌉₊).image (fun i => r + 2 * i) := by
  ext j
  rw [PeriodicBlock.mem_nodes, Finset.mem_image]
  simp only [rowB, Finset.mem_range, Nat.lt_ceil]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hj : r ≤ j := by
      have : (r : ℚ) ≤ j := by linarith
      exact_mod_cast this
    have hi : r + 2 * ((j - r) / 2) = j := by omega
    refine ⟨(j - r) / 2, ?_, hi⟩
    have : (r : ℚ) + 2 * (((j - r) / 2 : ℕ) : ℚ) = j := by exact_mod_cast hi
    linarith
  · rintro ⟨i, hi, rfl⟩
    push_cast
    refine ⟨by nlinarith, by linarith, by omega⟩

theorem colB_nodes {r : ℕ} (hr : r % 2 = 0) :
    (colB c hc).nodes r = (Finset.range ⌈(c * r - 1) / 2⌉₊).image (fun i => r + 2 * i + 1) := by
  ext j
  rw [PeriodicBlock.mem_nodes, Finset.mem_image]
  simp only [colB, Finset.mem_range, Nat.lt_ceil]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hj : r ≤ j := by
      have : (r : ℚ) ≤ j := by linarith
      exact_mod_cast this
    have hi : r + 2 * ((j - r - 1) / 2) + 1 = j := by omega
    refine ⟨(j - r - 1) / 2, ?_, hi⟩
    have : (r : ℚ) + 2 * (((j - r - 1) / 2 : ℕ) : ℚ) + 1 = j := by exact_mod_cast hi
    linarith
  · rintro ⟨i, hi, rfl⟩
    push_cast
    refine ⟨by nlinarith, by linarith, by omega⟩

theorem altGeom_C (r : ℕ) : ((altGeom c hc).geometry r).C = Finset.range r := by
  show (single commonB).nodes r = _
  rw [single_nodes, commonB_nodes]

/-- The border size of the alternating geometry at an even scale. -/
theorem altGeom_borderSize {r : ℕ} (hr : r % 2 = 0) :
    (altGeom c hc).borderSize r = min ⌈c * r / 2⌉₊ ⌈(c * r - 1) / 2⌉₊ := by
  have hf : Function.Injective (fun i : ℕ => r + 2 * i) := fun a b h => by simp at h; omega
  have hg : Function.Injective (fun i : ℕ => r + 2 * i + 1) := fun a b h => by simp at h; omega
  show min ((single (rowB c hc)).nodes r).card ((single (colB c hc)).nodes r).card = _
  rw [single_nodes, single_nodes, rowB_nodes c hc hr, colB_nodes c hc hr,
    Finset.card_image_of_injective _ hf, Finset.card_image_of_injective _ hg,
    Finset.card_range, Finset.card_range]

theorem altGeom_X {r : ℕ} (hr : r % 2 = 0) :
    ((altGeom c hc).geometry r).X' =
      (Finset.range ((altGeom c hc).borderSize r)).image (fun i => r + 2 * i) := by
  have hmono : StrictMono (fun i : ℕ => r + 2 * i) := fun a b h => by simp; omega
  show keepNodes ((single (rowB c hc)).nodes r) _ = _
  rw [single_nodes, rowB_nodes c hc hr]
  exact keepNodes_image_range _ hmono (by rw [altGeom_borderSize c hc hr]; exact min_le_left _ _)

theorem altGeom_Y {r : ℕ} (hr : r % 2 = 0) :
    ((altGeom c hc).geometry r).Y' =
      (Finset.range ((altGeom c hc).borderSize r)).image (fun i => r + 2 * i + 1) := by
  have hmono : StrictMono (fun i : ℕ => r + 2 * i + 1) := fun a b h => by simp; omega
  show keepNodes ((single (colB c hc)).nodes r) _ = _
  rw [single_nodes, colB_nodes c hc hr]
  exact keepNodes_image_range _ hmono (by rw [altGeom_borderSize c hc hr]; exact min_le_right _ _)

/-- **`HybShape` for the alternating geometry at every even scale.** -/
theorem altGeom_hybShape {r : ℕ} (hr : r % 2 = 0) : HybShape (altGeom c hc) r := by
  have hf : Function.Injective (fun i : ℕ => r + 2 * i) := fun a b h => by simp at h; omega
  have hg : Function.Injective (fun i : ℕ => r + 2 * i + 1) := fun a b h => by simp at h; omega
  have hkX : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r := by
    show ((altGeom c hc).geometry r).X'.card = _
    rw [altGeom_X c hc hr, Finset.card_image_of_injective _ hf, Finset.card_range]
  refine ⟨altGeom_C c hc r, ?_, ?_⟩
  · intro i
    have := congrFun (Finset.orderEmbOfFin_unique (s := ((altGeom c hc).geometry r).X')
      (h := rfl) (f := fun i : Fin ((altGeom c hc).geometry r).k => r + 2 * (i : ℕ))
      (fun x => by
        rw [altGeom_X c hc hr, Finset.mem_image]
        exact ⟨x, Finset.mem_range.2 (hkX ▸ x.2), rfl⟩)
      (fun a b h => by simp; exact h)) i
    exact this.symm
  · intro i
    have := congrFun (Finset.orderEmbOfFin_unique (s := ((altGeom c hc).geometry r).Y')
      (h := ((altGeom c hc).geometry r).card_eq.symm)
      (f := fun i : Fin ((altGeom c hc).geometry r).k => r + 2 * (i : ℕ) + 1)
      (fun x => by
        rw [altGeom_Y c hc hr, Finset.mem_image]
        exact ⟨x, Finset.mem_range.2 (hkX ▸ x.2), rfl⟩)
      (fun a b h => by simp; exact h)) i
    exact this.symm

end CatalanCore.Uniform.Content.Shape
