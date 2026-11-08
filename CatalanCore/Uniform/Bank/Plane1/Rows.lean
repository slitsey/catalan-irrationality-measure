module

public import CatalanCore.Uniform.Bank.Plane1.Content
public import CatalanCore.Uniform.Bank.Plane1.Decay
public import CatalanCore.Uniform.Content.Shape.Irrational

@[expose] public section
set_option Elab.async false

/-! # Row form: Theorem R, the plane frames, sixths and its mirror (wave H4 statements; ledger P113, P117, P118)

* `alt_row_theorem` (Theorem R, **P113**): for the alternating geometry `altGeom c` and any frame, a content
  `Λ` for the even-scale family, a decay `(D, cc)` for the family, `Λ < D`, `cc > 0` and non-vanishing at even
  scales give `MeasureLB (cc / (D - Λ))` for the even-scale family **and** irrationality of its constant.  The
  plane theorem is the case `c = 1/6`; a special row is the same theorem with its own `α` and cover.
* `plane_frame_point`: for a plane frame with three nonzero weights, `L₃ + t π²`, `t = planeT σ a b`, has
  `MeasureLBAt` with exponent `cc / (D - Λ)` and is irrational.  It consumes content and decay for the frame (the
  covers enter as `D`, `T`; see `Plane1.Content`, `Plane1.Decay`).
* `sixths_point` (**P118**, the corollary at `t = 11/135`, frame `(5, -2, -3)` on `S⁺`) and `mirror_point`
  (**P117**, the same frame on `S⁻`, `t = -11/135`): the mirror is the `S⁻` instance of the same theorem, not a
  separate development. -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Measure
  CatalanCore.Uniform.Content.BankShared.Check CatalanFrames.P6

/-- **Theorem R, row form (P113)**: content, decay and non-vanishing for an alternating geometry. -/
theorem alt_row_theorem (c : ℚ) (hc : 0 < c) (Fr : Frame) (depth : ℕ) {Λ D cc : ℝ}
    (hΛ : HasScaledContent (AltEven c hc Fr depth) (altGeom c hc).scale Λ)
    (hD : HasScaledDecay ((altGeom c hc).family Fr depth) (altGeom c hc).scale D cc)
    (hη : Λ < D) (hcc : 0 < cc)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).Adm n ∧
        (altGeom c hc).scale n = 2 * s ∧
        (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).evalQ n x ≠ 0) :
    (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).MeasureLB (1 * cc / (D - Λ)) ∧
      Irrational Fr.const := by
  have hmass : ((altGeom c hc).common.mass : ℝ) = 1 := by
    have : (altGeom c hc).common.mass = 1 := by
      simp [altGeom, single_mass, commonB, PeriodicBlock.mass]
    rw [this]; norm_num
  have hdeg : ∀ n, (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).Adm n →
      ((((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).deg n : ℝ) ≤
        1 * ((altGeom c hc).scale n : ℝ) + (altGeom c hc).common.n := by
    intro n _
    have := (altGeom c hc).degree_bound Fr depth n
    rw [hmass] at this
    exact this
  have hD' : HasScaledDecay (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0))
      (altGeom c hc).scale D cc := by
    intro ε hε
    obtain ⟨R0, hR⟩ := hD ε hε
    exact ⟨R0, fun n (hn : (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)).Adm n) => hR n hn.1⟩
  refine ⟨measure_of_family_nv0_even (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) (altGeom c hc).scale (γ := 1) (K := (altGeom c hc).common.n)
    hΛ hD' hη hcc one_pos (Nat.cast_nonneg _) hdeg (fun n hn => hn.2) hnv, ?_⟩
  exact irrational_of_family_nv0_even (((altGeom c hc).family Fr depth).restrictAdm (fun i => i.1 % 2 = 0)) (altGeom c hc).scale hΛ hD' hη hcc one_pos (Nat.cast_nonneg _)
    hdeg (fun n hn => hn.2) hnv

/-- **A plane frame with three nonzero weights** (P116 at the frame level): the number `L₃ + t π²`,
`t = planeT σ a b`, has the measure bound `cc / (D - Λ)` and is irrational, given content `Λ`, decay `(D, cc)`
of the frame at the selection depth. -/
theorem plane_frame_point (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) {Λ D cc : ℚ}
    (hΛ : HasScaledContent (AltEven planeC planeC_pos (planeFrame σ a b c h0) planeDepth)
      planeG.scale (Λ : ℝ))
    (hD : HasScaledDecay (planeG.family (planeFrame σ a b c h0) planeDepth) planeG.scale (D : ℝ) (cc : ℝ))
    (hη : Λ < D) (hcc : 0 < cc) :
    MeasureLBAt (chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2) ((cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) ∧
      Irrational (chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2) := by
  have hη' : (Λ : ℝ) < D := by exact_mod_cast hη
  have hcc' : (0 : ℝ) < cc := by exact_mod_cast hcc
  obtain ⟨hLB, hirr⟩ := alt_row_theorem planeC planeC_pos (planeFrame σ a b c h0) planeDepth hΛ hD hη' hcc'
    (plane_nv0_even σ a b c h0 ha hb hc planeDepth le_rfl)
  have hu : planeU σ a ≠ 0 := by
    unfold planeU
    have : (σ.sgn : ℚ) ≠ 0 := by cases σ <;> simp [Support.sgn]
    have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    positivity
  have hconst := plane_const σ a b c h0 ha
  have hE : (0 : ℝ) ≤ 1 * (cc : ℝ) / ((D : ℝ) - (Λ : ℝ)) := by
    have : (0 : ℝ) < (D : ℝ) - Λ := by linarith
    positivity
  have h1 : MeasureLBAt (planeFrame σ a b c h0).const (1 * (cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) :=
    (MeasureLB_iff _ _).mp hLB
  have hx : chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2 =
      (((planeU σ a)⁻¹ : ℚ) : ℝ) * (planeFrame σ a b c h0).const + ((0 : ℚ) : ℝ) := by
    rw [hconst]
    have hu' : ((planeU σ a : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hu
    push_cast
    field_simp
    ring
  rw [hx]
  refine ⟨?_, irrational_affine hirr _ 0 (inv_ne_zero hu)⟩
  rw [one_mul] at h1 hE
  simpa using h1.affine (by simpa using hE) ((planeU σ a)⁻¹) 0 (inv_ne_zero hu)

/-- **The zero-weight frame (0, 1, -1)** (a = 0, P119): `π²` has the measure bound `cc / (D - Λ)` and is irrational. -/
theorem plane_frame_point_pi (σ : Support) {Λ D cc : ℚ}
    (hΛ : HasScaledContent (AltEven planeC planeC_pos (planeFrame σ 0 1 (-1) (by norm_num)) planeDepth)
      planeG.scale (Λ : ℝ))
    (hD : HasScaledDecay (planeG.family (planeFrame σ 0 1 (-1) (by norm_num)) planeDepth) planeG.scale
      (D : ℝ) (cc : ℝ))
    (hη : Λ < D) (hcc : 0 < cc) :
    MeasureLBAt (Real.pi ^ 2) ((cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) ∧ Irrational (Real.pi ^ 2) := by
  have hη' : (Λ : ℝ) < D := by exact_mod_cast hη
  have hcc' : (0 : ℝ) < cc := by exact_mod_cast hcc
  obtain ⟨hLB, hirr⟩ := alt_row_theorem planeC planeC_pos (planeFrame σ 0 1 (-1) (by norm_num)) planeDepth
    hΛ hD hη' hcc' (plane_nv0_even_zero σ 1 (-1) (by norm_num) (by norm_num) planeDepth le_rfl)
  have hconst : (planeFrame σ 0 1 (-1) (by norm_num)).const = Real.pi ^ 2 / 3 := by
    rw [plane_const_ab]
    have : planeU σ 0 = 0 := by simp [planeU]
    rw [this]; push_cast; ring
  have hE : (0 : ℝ) ≤ 1 * (cc : ℝ) / ((D : ℝ) - (Λ : ℝ)) := by
    have : (0 : ℝ) < (D : ℝ) - Λ := by linarith
    positivity
  have h1 : MeasureLBAt (planeFrame σ 0 1 (-1) (by norm_num)).const (1 * (cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) :=
    (MeasureLB_iff _ _).mp hLB
  rw [hconst] at h1 hirr
  have hx : Real.pi ^ 2 = ((3 : ℚ) : ℝ) * (Real.pi ^ 2 / 3) + ((0 : ℚ) : ℝ) := by push_cast; ring
  rw [hx]
  rw [one_mul] at h1 hE
  refine ⟨?_, irrational_affine hirr 3 0 (by norm_num)⟩
  simpa using h1.affine (by simpa using hE) 3 0 (by norm_num)

/-- **Sixths (P118)**: `t = 11/135`, the frame `(5, -2, -3)` on `S⁺` (`ψ′(1/6) - ζ(2) = (45/2)(L₃ + 11π²/135)`). -/
theorem sixths_point {Λ D cc : ℚ}
    (hΛ : HasScaledContent (AltEven planeC planeC_pos
      (planeFrame .plus 5 (-2) (-3) (by norm_num)) planeDepth) planeG.scale (Λ : ℝ))
    (hD : HasScaledDecay (planeG.family (planeFrame .plus 5 (-2) (-3) (by norm_num)) planeDepth)
      planeG.scale (D : ℝ) (cc : ℝ))
    (hη : Λ < D) (hcc : 0 < cc) :
    MeasureLBAt (chi3L2 + ((11 / 135 : ℚ) : ℝ) * Real.pi ^ 2) ((cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) ∧
      Irrational (chi3L2 + ((11 / 135 : ℚ) : ℝ) * Real.pi ^ 2) := by
  have e : planeT .plus 5 (-2) = 11 / 135 := by norm_num [planeT, Support.sgn]
  have := plane_frame_point .plus 5 (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΛ hD hη hcc
  rwa [e] at this

/-- **The mirror (P117)**: the same frame on `S⁻`, `t = -11/135`, on the same cover. -/
theorem mirror_point {Λ D cc : ℚ}
    (hΛ : HasScaledContent (AltEven planeC planeC_pos
      (planeFrame .minus 5 (-2) (-3) (by norm_num)) planeDepth) planeG.scale (Λ : ℝ))
    (hD : HasScaledDecay (planeG.family (planeFrame .minus 5 (-2) (-3) (by norm_num)) planeDepth)
      planeG.scale (D : ℝ) (cc : ℝ))
    (hη : Λ < D) (hcc : 0 < cc) :
    MeasureLBAt (chi3L2 + ((-(11 / 135) : ℚ) : ℝ) * Real.pi ^ 2) ((cc : ℝ) / ((D : ℝ) - (Λ : ℝ))) ∧
      Irrational (chi3L2 + ((-(11 / 135) : ℚ) : ℝ) * Real.pi ^ 2) := by
  have e : planeT .minus 5 (-2) = -(11 / 135) := by norm_num [planeT, Support.sgn]
  have := plane_frame_point .minus 5 (-2) (-3) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hΛ hD hη hcc
  rwa [e] at this

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.alt_row_theorem
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_frame_point
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_frame_point_pi
#print axioms CatalanCore.Uniform.Bank.Plane1.sixths_point
#print axioms CatalanCore.Uniform.Bank.Plane1.mirror_point
