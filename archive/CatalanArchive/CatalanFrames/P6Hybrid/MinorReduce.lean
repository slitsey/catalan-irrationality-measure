module
public import CatalanCore.Rect.CommonMinor.Low
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.MinorReduce
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Rect
open CatalanFrames.LambdaHybrid.NV
namespace CatalanFrames.P6Hybrid

/-- Convert the low-block principal minor into the retained-node family index. -/
theorem exists_commonMinor_of_after_low (Fr : Frame) (r m K dmax : ℕ) (hKr : K ≤ r)
    (d : Finset (Fin K)) (hd : d.card ≤ dmax) (x : ℚ)
    (hdet : ((after r m).Full Fr x |>.submatrix
      (fun i => eIdx K (after r m) (fun n hn => by simp [after]; omega)
        (lowKeep (Subtype.val : {a : Fin K // a ∉ d} → Fin K) i))
      (fun i => eIdx K (after r m) (fun n hn => by simp [after]; omega)
        (lowKeep (Subtype.val : {a : Fin K // a ∉ d} → Fin K) i))).det ≠ 0) :
    ∃ s : Finset (Fin r), r - s.card ≤ dmax ∧ (commonMinorPoly Fr r m s).eval x ≠ 0 := by
  let G := after r m
  have hlow : ∀ n, n < K → n ∈ G.C := fun n hn => by simp [G, after]; omega
  let f : {a : Fin K // a ∉ d} → Fin K := Subtype.val
  let I := {a : Fin K // a ∉ d} ⊕ HiC K G
  let c : I → Fin r := fun i => ⟨(commonKeep G hlow f i : ℕ), by
    have h := (commonKeep G hlow f i).2
    exact Finset.mem_range.mp h⟩
  have hc : Function.Injective c := by
    intro i j hij
    apply commonKeep_injective G hlow f Subtype.val_injective
    apply Subtype.ext
    exact congrArg Fin.val hij
  have hKcard : K + Fintype.card (HiC K G) = r := by
    have ht := Fintype.card_congr (eIdx K G hlow)
    simp only [Fintype.card_sum, Fintype.card_fin] at ht
    have hC : Fintype.card G.C = r := by
      change Fintype.card (Finset.range r) = r
      rw [Fintype.card_coe, Finset.card_range]
    omega
  have hlowcard : Fintype.card {a : Fin K // a ∉ d} = K - d.card := by
    simpa using Fintype.card_subtype_compl (fun a : Fin K => a ∈ d)
  have hcard : r - Fintype.card I ≤ dmax := by
    have hdc : d.card ≤ K := by simpa using card_le_univ d
    simp only [I, Fintype.card_sum, hlowcard]
    omega
  apply exists_commonMinor_of_fullN Fr r m dmax c hc hcard x
  have he : (G.Full Fr x).submatrix
      (fun i => eIdx K G hlow (lowKeep f i))
      (fun i => eIdx K G hlow (lowKeep f i)) =
      FullN Fr (fun i : I => (c i : ℕ)) G.xs G.ys x := by
    simp only [eIdx_lowKeep]
    exact FullN_submatrix_common Fr (commonKeep G hlow f)
      (commonKeep_injective G hlow f Subtype.val_injective) (fun a : G.C => (a : ℕ)) G.xs G.ys x
  have hn : (FullN Fr (fun i : I => (c i : ℕ)) G.xs G.ys x).det ≠ 0 := by
    rw [← he]
    exact hdet
  have hh := det_fullN_reindex Fr (fun i : I => (c i : ℕ)) G.xs G.ys
    (fun i : I => (c i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Equiv.refl I) (finCongr (after_k r m)).symm
    (fun _ => rfl) (fun i => by rw [after_xs]; rfl) (fun i => by rw [after_ys]; rfl) x
  rwa [hh]
theorem exists_commonMinor_of_after (Fr : Frame) (r m dmax : ℕ) (x : ℚ)
    (hdet : ((after r m).Full Fr x).det ≠ 0) :
    ∃ s : Finset (Fin r), r - s.card ≤ dmax ∧ (commonMinorPoly Fr r m s).eval x ≠ 0 := by
  let G := after r m
  let c : G.C → Fin r := fun a => ⟨a.val, Finset.mem_range.mp a.2⟩
  have hc : Function.Injective c := by
    intro a b h
    exact Subtype.ext (congrArg Fin.val h)
  have hcard : r - Fintype.card G.C ≤ dmax := by
    have hh : Fintype.card G.C = r := by
      change Fintype.card (Finset.range r) = r
      rw [Fintype.card_coe, Finset.card_range]
    simp [hh]
  apply exists_commonMinor_of_fullN Fr r m dmax c hc hcard x
  have hh := det_fullN_reindex Fr (fun a : G.C => (a : ℕ)) G.xs G.ys
    (fun a : G.C => (a : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
    (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Equiv.refl G.C) (finCongr (after_k r m)).symm
    (fun _ => rfl) (fun i => by rw [after_xs]; rfl) (fun i => by rw [after_ys]; rfl) x
  rwa [hh]
end CatalanFrames.P6Hybrid
#print axioms CatalanFrames.P6Hybrid.exists_commonMinor_of_after_low
