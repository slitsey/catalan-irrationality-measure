module

public import CatalanCore.Uniform.Frame.Block

@[expose] public section

/-!
# Smallest-`m` trimming of an arithmetic progression (lane H7)

`keepNodes (f '' range N) m = f '' range m` for strictly increasing `f` and `m ≤ N`.
-/

namespace CatalanCore.Uniform.Content.Shape

open Finset

theorem sort_image_range (f : ℕ → ℕ) (hf : StrictMono f) (N : ℕ) :
    ((Finset.range N).image f).sort (· ≤ ·) = (List.range N).map f := by
  refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _) ?_ ?_
  swap
  · apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup _ _
    · exact (List.nodup_range).map hf.injective
    · ext x
      simp [Finset.mem_sort]
  · exact (List.pairwise_map.2 (by
      refine List.Pairwise.imp (fun {a b} hab => ?_) List.pairwise_lt_range
      exact (hf hab).le))

theorem keepNodes_image_range (f : ℕ → ℕ) (hf : StrictMono f) {N m : ℕ} (h : m ≤ N) :
    keepNodes ((Finset.range N).image f) m = (Finset.range m).image f := by
  unfold keepNodes
  rw [sort_image_range f hf, ← List.map_take, List.take_range, Nat.min_eq_left h]
  ext x
  simp

end CatalanCore.Uniform.Content.Shape
