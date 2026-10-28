module
public import CatalanCore.Uniform.Decay.Nodes.EnergyGeom
@[expose] public section

/-!
# Canonical enumeration of the row/column lists (common nodes first)

`BlockGeom.nodeEnum G r : NodeEnum G r (|C| + |X'|) |C|`: `nR` lists the common nodes in
increasing order and then `X'` in increasing order; `nQ` the same common nodes and then `Y'`.
-/

namespace CatalanCore.Uniform
open Finset

/-- Common nodes first (increasing), then the border nodes (increasing). -/
noncomputable def enumApp (C X : Finset ℕ) {k : ℕ} (hk : X.card = k) : Fin (C.card + k) → ℕ :=
  Fin.append (fun i : Fin C.card => (C.orderEmbOfFin rfl i : ℕ))
    (fun j : Fin k => (X.orderEmbOfFin hk j : ℕ))

theorem enumApp_inj (C X : Finset ℕ) {k : ℕ} (hk : X.card = k) (hd : Disjoint C X) :
    Function.Injective (enumApp C X hk) := by
  intro a b hab
  unfold enumApp at hab
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      simp only [Fin.append_left] at hab
      have := (C.orderEmbOfFin rfl).injective hab
      rw [this]
    | right j =>
      simp only [Fin.append_left, Fin.append_right] at hab
      exact absurd (hab ▸ Finset.orderEmbOfFin_mem C rfl i) (fun h =>
        Finset.disjoint_left.mp hd h (Finset.orderEmbOfFin_mem X hk j))
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      simp only [Fin.append_left, Fin.append_right] at hab
      exact absurd (hab ▸ Finset.orderEmbOfFin_mem C rfl j) (fun h =>
        Finset.disjoint_left.mp hd h (Finset.orderEmbOfFin_mem X hk i))
    | right j =>
      simp only [Fin.append_right] at hab
      have := (X.orderEmbOfFin hk).injective hab
      rw [this]

theorem enumApp_image (C X : Finset ℕ) {k : ℕ} (hk : X.card = k) :
    Finset.univ.image (enumApp C X hk) = C ∪ X := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨b, rfl⟩
    induction b using Fin.addCases with
    | left i =>
      left
      simp only [enumApp, Fin.append_left]
      exact Finset.orderEmbOfFin_mem C rfl i
    | right i =>
      right
      simp only [enumApp, Fin.append_right]
      exact Finset.orderEmbOfFin_mem X hk i
  · rintro (h | h)
    · have : j ∈ Set.range (C.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact h
      obtain ⟨i, hi⟩ := this
      exact ⟨Fin.castAdd _ i, by simp [enumApp, hi]⟩
    · have : j ∈ Set.range (X.orderEmbOfFin hk) := by
        rw [Finset.range_orderEmbOfFin]; exact h
      obtain ⟨i, hi⟩ := this
      exact ⟨Fin.natAdd _ i, by simp [enumApp, hi]⟩

namespace BlockGeom

/-- The canonical node enumeration of a block geometry. -/
noncomputable def nodeEnum (G : BlockGeom) (r : ℕ) :
    NodeEnum G r ((G.geometry r).C.card + (G.geometry r).X'.card) (G.geometry r).C.card where
  nR := enumApp (G.geometry r).C (G.geometry r).X' rfl
  nQ := enumApp (G.geometry r).C (G.geometry r).Y' (G.geometry r).card_eq.symm
  injR := enumApp_inj _ _ rfl (G.geometry r).disjCX
  injQ := enumApp_inj _ _ _ (G.geometry r).disjCY
  imgR := enumApp_image _ _ rfl
  imgQ := enumApp_image _ _ _
  commonAgree := by
    intro b hb
    induction b using Fin.addCases with
    | left i => simp [enumApp]
    | right i => simp at hb
  commonMem := by
    intro b hb
    induction b using Fin.addCases with
    | left i =>
      simp only [enumApp, Fin.append_left]
      exact Finset.orderEmbOfFin_mem _ rfl i
    | right i => simp at hb

end BlockGeom
end CatalanCore.Uniform
