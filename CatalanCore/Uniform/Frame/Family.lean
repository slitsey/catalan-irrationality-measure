module
public import CatalanCore.Rect.CommonMinor
public import CatalanCore.Uniform.Measure.NV0
@[expose] public section

namespace CatalanCore.Uniform
open Polynomial Finset Matrix

/-- Arbitrary balanced finite node geometries, indexed by the physical scale. -/
abbrev NodeFamily := ℕ → Rect.Geometry

namespace NodeFamily

abbrev Index (G : NodeFamily) := (r : ℕ) × Finset (G r).C

/-- Keep exactly the specified common nodes; the border node sets are unchanged. -/
noncomputable def polynomial (Fr : Frame) (G : NodeFamily) (i : G.Index) : ℚ[X] :=
  (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
    (G i.1).xs (G i.1).ys (X : ℚ[X])).det

/-- The actual selected family. The degree budget is the number of retained common nodes. -/
noncomputable abbrev family (Fr : Frame) (G : NodeFamily) (depth : ℕ) : PolyFamily where
  const := Fr.const
  ι := G.Index
  deg := fun i => i.2.card
  Adm := fun i => (G i.1).C.card - i.2.card ≤ depth
  Q := G.polynomial Fr

abbrev scale (G : NodeFamily) (i : G.Index) : ℕ := i.1

/-- No monicity or border invertibility is needed for the degree upper bound. -/
theorem polynomial_degree (Fr : Frame) (G : NodeFamily) (i : G.Index) :
    (G.polynomial Fr i).natDegree ≤ i.2.card := by
  simpa [polynomial] using Rect.natDegree_fullN_le Fr
    (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys

theorem family_degree (Fr : Frame) (G : NodeFamily) (depth : ℕ)
    (i : (G.family Fr depth).ι) :
    ((G.family Fr depth).Q i).natDegree ≤ (G.family Fr depth).deg i :=
  G.polynomial_degree Fr i

theorem degree_le_common (Fr : Frame) (G : NodeFamily) (depth : ℕ)
    (i : (G.family Fr depth).ι) : (G.family Fr depth).deg i ≤ (G i.1).C.card := by
  simpa [family] using Finset.card_le_univ i.2

/-- Rational evaluation is the determinant of the actual finite Loewner pencil. -/
theorem evalQ_polynomial (Fr : Frame) (G : NodeFamily) (depth : ℕ)
    (i : (G.family Fr depth).ι) (x : ℚ) :
    (G.family Fr depth).evalQ i x =
      (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
        (G i.1).xs (G i.1).ys x).det := by
  change (G.polynomial Fr i).eval x = _
  unfold polynomial
  have h := (Polynomial.evalRingHom x).map_det
    (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
      (G i.1).xs (G i.1).ys (X : ℚ[X]))
  rw [Rect.fullN_map_eval] at h
  exact h

/-- Real evaluation uses the same matrix and normalization. -/
theorem evalR_polynomial (Fr : Frame) (G : NodeFamily) (depth : ℕ)
    (i : (G.family Fr depth).ι) (x : ℝ) :
    (G.family Fr depth).evalR i x =
      (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
        (G i.1).xs (G i.1).ys x).det := by
  change Polynomial.aeval x (G.polynomial Fr i) = _
  unfold polynomial
  have h := (Polynomial.aeval x).toRingHom.map_det
    (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
      (G i.1).xs (G i.1).ys (X : ℚ[X]))
  change Polynomial.aeval x
      (Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
        (G i.1).xs (G i.1).ys (X : ℚ[X])).det =
    ((Rect.FullN Fr (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ))
      (G i.1).xs (G i.1).ys (X : ℚ[X])).map (Polynomial.aeval x)).det at h
  rw [Rect.map_fullN] at h
  exact h

/-- The generic characteristic-zero selector adapter retains the exact member scope. -/
theorem hasNV0_of_minors (Fr : Frame) (G : NodeFamily) (depth R0 : ℕ)
    (hnv : ∀ r, R0 ≤ r → ∀ x : ℚ, ∃ S : Finset (G r).C,
      (G r).C.card - S.card ≤ depth ∧
      (Rect.FullN Fr (fun a : S => ((a.1 : (G r).C) : ℕ))
        (G r).xs (G r).ys x).det ≠ 0) :
    HasNV0 (G.family Fr depth) G.scale := by
  refine ⟨R0, ?_⟩
  intro r hr x
  obtain ⟨S, hS, hdet⟩ := hnv r hr x
  refine ⟨⟨r, S⟩, hS, rfl, ?_⟩
  rw [G.evalQ_polynomial Fr depth]
  exact hdet

end NodeFamily
end CatalanCore.Uniform


