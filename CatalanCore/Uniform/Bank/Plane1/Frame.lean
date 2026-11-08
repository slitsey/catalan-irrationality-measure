module

public import CatalanFrames.P6.Const
public import Mathlib.NumberTheory.ZetaValues
public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Frame.NVAdapter
public import CatalanCore.Uniform.Content.Shape.Reindex
public import CatalanCore.Uniform.Decay.ContourCheck
public import CatalanCore.Measure.Scaling

@[expose] public section
set_option Elab.async false

/-! # The frames of the plane `L₃ + tπ²` (wave H4; ledger P101, P110, P112)

Let `L₃ = L(2, χ₋₃)`.  A **plane frame** is a frame `F(z) = a ψ(z+s) + b ψ(z+½) + c ψ(z+1)`, `a + b + c = 0`,
on one of the two supports `S⁺ = (⅓, ½, 1)` (`ρ = 2`, denominators `3k - 2`) and `S⁻ = (⅔, ½, 1)` (`ρ = 1`,
denominators `3k - 1`), normalisation `1`, contour data `xs = ¾` (`S⁺`), `¼` (`S⁻`), `δ0 = ¼`, `n0off = 1`.

* `planeFrame σ a b c h0` (P101): a frame for every integer triple of sum zero (the non-vanishing of the weights
  is needed only for `plane_nv0_even`);
* `plane_const` (P112, generalising `p6Frame_const`): `const = u (L₃ + t π²)`, with `u = ± 9a/2`,
  `t = ± (3a + 2b)/(27 a)` (sign `+` on `S⁺`, `-` on `S⁻`);
* `plane_nv0_even` (P110): non-vanishing of the even-scale family `altGeom (1/6)` for weights all nonzero
  (Theorem UNV, `L = 2`, `hasNV0`);
* `exists_planeFrame` (P113, the frame of Theorem R): every rational `t` is `planeT σ a b` for a plane frame with
  three nonzero weights, `S⁺` except at `t ∈ {1/9, 1/27}` where the mirror support `S⁻` is used. -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.P6

/-- The two supports of the plane. -/
inductive Support
  | plus
  | minus
  deriving DecidableEq

namespace Support

/-- The first shift: `⅓` on `S⁺`, `⅔` on `S⁻`. -/
def shift : Support → ℚ
  | plus => 1 / 3
  | minus => 2 / 3

/-- The offset of `3k - ρ`: `ρ = 2` on `S⁺`, `1` on `S⁻` (`3 (k - 1) + 3 s = 3k - ρ`). -/
def rho : Support → ℕ
  | plus => 2
  | minus => 1

/-- The contour abscissa offset. -/
def xs : Support → ℚ
  | plus => 3 / 4
  | minus => 1 / 4

/-- The sign `±1` of the support. -/
def sgn : Support → ℤ
  | plus => 1
  | minus => -1

theorem shift_pos (σ : Support) : 0 < σ.shift := by cases σ <;> norm_num [shift]
theorem shift_lt_one (σ : Support) : σ.shift < 1 := by cases σ <;> norm_num [shift]
theorem shift_ne_half (σ : Support) : σ.shift ≠ 1 / 2 := by cases σ <;> norm_num [shift]
theorem shift_ne_one (σ : Support) : σ.shift ≠ 1 := by cases σ <;> norm_num [shift]

end Support

/-- **The plane frame** (P101): weights `(a, b, c)` of sum zero on the support `σ`, normalisation `1`. -/
def planeFrame (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) : Frame where
  d := 3
  μ := ![σ.shift, 1 / 2, 1]
  w := ![a, b, c]
  norm := 1
  xs := σ.xs
  δ0 := 1 / 4
  n0off := 1
  hμ := by
    intro i
    fin_cases i
    · exact ⟨σ.shift_pos, σ.shift_lt_one.le⟩
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, le_rfl⟩
  hμinj := by
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp at hij h
    all_goals first
      | exact σ.shift_ne_half (by simpa [one_div] using h)
      | exact σ.shift_ne_half (by simpa [one_div] using h.symm)
      | exact σ.shift_ne_one h
      | exact σ.shift_ne_one h.symm
      | (norm_num at h)
  hw := by simp [Fin.sum_univ_three, h0]
  hnorm := by norm_num

section FrameFacts
variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

@[simp] theorem planeFrame_d : (planeFrame σ a b c h0).d = 3 := rfl
@[simp] theorem planeFrame_norm : (planeFrame σ a b c h0).norm = 1 := rfl
@[simp] theorem planeFrame_xs : (planeFrame σ a b c h0).xs = σ.xs := rfl
@[simp] theorem planeFrame_δ0 : (planeFrame σ a b c h0).δ0 = 1 / 4 := rfl
@[simp] theorem planeFrame_n0off : (planeFrame σ a b c h0).n0off = 1 := rfl

theorem planeFrame_mu (i : Fin 3) :
    (planeFrame σ a b c h0).μ i = ![σ.shift, 1 / 2, 1] i := rfl

theorem planeFrame_w (i : Fin 3) : (planeFrame σ a b c h0).w i = ![a, b, c] i := rfl

/-- The shifts of a plane frame are at least `1/3`. -/
theorem planeFrame_mu_ge (i : Fin (planeFrame σ a b c h0).d) :
    (1 / 3 : ℚ) ≤ (planeFrame σ a b c h0).μ i := by
  have key : ∀ j : Fin 3, (1 / 3 : ℚ) ≤ ![σ.shift, 1 / 2, 1] j := by
    intro j
    fin_cases j
    · cases σ <;> norm_num [Support.shift]
    · norm_num
    · norm_num
  exact key i

/-- The floor condition of the decay theorem, at `n0off = 1`. -/
theorem planeFrame_hAR (i : Fin (planeFrame σ a b c h0).d) :
    ((⌊(planeFrame σ a b c h0).xs - (planeFrame σ a b c h0).μ i⌋ : ℤ) : ℚ) +
      (planeFrame σ a b c h0).μ i ≤ (planeFrame σ a b c h0).n0off := by
  have hi : i.1 < 3 := i.2
  rcases i with ⟨k, hk⟩
  interval_cases k <;> cases σ
  · have : ⌊(3 / 4 : ℚ) - 1 / 3⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, Support.shift, this]; norm_num
  · have : ⌊(1 / 4 : ℚ) - 2 / 3⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, Support.shift, this]; norm_num
  · have : ⌊(3 / 4 : ℚ) - 1 / 2⌋ = 0 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, this]; norm_num
  · have : ⌊(1 / 4 : ℚ) - 1 / 2⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, this]; norm_num
  · have : ⌊(3 / 4 : ℚ) - 1⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, this]; norm_num
  · have : ⌊(1 / 4 : ℚ) - 1⌋ = -1 := by rw [Int.floor_eq_iff]; norm_num
    simp only [planeFrame, Support.xs, this]; norm_num

/-- The contour check of the decay theorems does not read the weights. -/
theorem planeFrame_contourCheck : Frame.contourCheck (planeFrame σ a b c h0) = true := by
  cases σ
  · have e : Frame.contourCheck (planeFrame .plus a b c h0) = Frame.contourCheck (planeFrame .plus 1 1 (-2) (by norm_num)) := rfl
    rw [e]; decide +kernel
  · have e : Frame.contourCheck (planeFrame .minus a b c h0) = Frame.contourCheck (planeFrame .minus 1 1 (-2) (by norm_num)) := rfl
    rw [e]; decide +kernel

end FrameFacts

/-! ### The constant (P112) -/

/-- `ζ(2, 2/3) = 9 ∑ 1/(3k+2)²`. -/
theorem hurwitz_two_thirds :
    hurwitzTail2 (2 / 3) = 9 * ∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 := by
  unfold hurwitzTail2
  rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  push_cast
  have : (3 : ℝ) * k + 2 ≠ 0 := by positivity
  have : (k : ℝ) + 2 / 3 ≠ 0 := by positivity
  field_simp
  norm_num

/-- `a = ∑ 1/(3k+1)²`, `b = ∑ 1/(3k+2)²` in terms of `L₃` and `π²`. -/
theorem three_classes :
    (∑' k : ℕ, 1 / ((3 * k + 1 : ℕ) : ℝ) ^ 2 = chi3L2 / 2 + 4 * (Real.pi ^ 2 / 6) / 9) ∧
    (∑' k : ℕ, 1 / ((3 * k + 2 : ℕ) : ℝ) ^ 2 = -chi3L2 / 2 + 4 * (Real.pi ^ 2 / 6) / 9) := by
  have h3 := split_three
  rw [hasSum_zeta_two.tsum_eq] at h3
  have hl := chi3L2_eq_sub
  constructor <;> linarith

/-- `ζ(2, 1/2) = π²/2`, `ζ(2, 1) = π²/6`. -/
theorem hurwitz_half_pi : hurwitzTail2 (1 / 2) = Real.pi ^ 2 / 2 := by
  have h2 := split_two
  rw [hasSum_zeta_two.tsum_eq] at h2
  rw [hurwitz_half]
  linarith

theorem hurwitz_one_pi : hurwitzTail2 1 = Real.pi ^ 2 / 6 := by
  rw [hurwitz_one, hasSum_zeta_two.tsum_eq]

theorem hurwitz_third_pi : hurwitzTail2 (1 / 3) = 9 * chi3L2 / 2 + 2 * Real.pi ^ 2 / 3 := by
  rw [hurwitz_third]
  have := three_classes.1
  rw [this]; ring

theorem hurwitz_two_thirds_pi : hurwitzTail2 (2 / 3) = -(9 * chi3L2 / 2) + 2 * Real.pi ^ 2 / 3 := by
  rw [hurwitz_two_thirds]
  have := three_classes.2
  rw [this]; ring

/-- The shift `s` of the support satisfies `ζ(2, s) = sgn · (9/2) L₃ + (2/3) π²`. -/
theorem hurwitz_shift_pi (σ : Support) :
    hurwitzTail2 σ.shift = (σ.sgn : ℝ) * (9 * chi3L2 / 2) + 2 * Real.pi ^ 2 / 3 := by
  cases σ
  · simpa [Support.shift, Support.sgn] using hurwitz_third_pi
  · simp only [Support.shift, Support.sgn]
    push_cast
    rw [hurwitz_two_thirds_pi]; ring

/-- The multiplier `u = ± 9a/2` of `L₃`. -/
def planeU (σ : Support) (a : ℤ) : ℚ := (σ.sgn : ℚ) * 9 * a / 2

/-- The target `t = ± (3a + 2b)/(27 a)` of the frame (`a ≠ 0`; the value is `0` at `a = 0`). -/
def planeT (σ : Support) (a b : ℤ) : ℚ := (σ.sgn : ℚ) * (3 * a + 2 * b) / (27 * a)

/-- **The constant of the plane frame** (P112): `F'(0) = u (L₃ + t π²)`. -/
theorem plane_const (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (ha : a ≠ 0) :
    (planeFrame σ a b c h0).const =
      ((planeU σ a : ℚ) : ℝ) * (chi3L2 + ((planeT σ a b : ℚ) : ℝ) * Real.pi ^ 2) := by
  have e : (planeFrame σ a b c h0).const =
      (∑ i : Fin 3, ((![a, b, c] i : ℤ) : ℝ) * hurwitzTail2 (![σ.shift, 1 / 2, 1] i)) /
        ((1 : ℚ) : ℝ) := rfl
  rw [e, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [hurwitz_shift_pi, hurwitz_half_pi, hurwitz_one_pi]
  have hc : (c : ℝ) = -a - b := by
    have : c = -a - b := by omega
    rw [this]; push_cast; ring
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hs : (σ.sgn : ℝ) ^ 2 = 1 := by cases σ <;> simp [Support.sgn]
  unfold planeU planeT
  push_cast
  rw [hc]
  field_simp
  linear_combination (-(486 * (a : ℝ) + 324 * b) * Real.pi ^ 2) * hs

/-- The rational form of `plane_const`, for a statement about `L₃ + t π²`. -/
theorem plane_const_eq (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (ha : a ≠ 0) (t : ℚ)
    (ht : planeT σ a b = t) :
    (planeFrame σ a b c h0).const =
      ((planeU σ a : ℚ) : ℝ) * ((1 : ℚ) * (chi3L2 + (t : ℝ) * Real.pi ^ 2) + (0 : ℚ) : ℝ) := by
  rw [plane_const σ a b c h0 ha, ht]
  push_cast; ring

/-! ### Every rational `t` has a plane frame with three nonzero weights (P113) -/

/-- Three nonzero weights of sum zero on a support with target `t`. -/
def PlaneRow (t : ℚ) : Prop :=
  ∃ (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ planeT σ a b = t

theorem planeT_of (σ : Support) (a b : ℤ) (ha : a ≠ 0) (t : ℚ) (hb : (b : ℚ) = a * (27 * σ.sgn * t - 3) / 2) :
    planeT σ a b = t := by
  unfold planeT
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hs : (σ.sgn : ℚ) ^ 2 = 1 := by cases σ <;> simp [Support.sgn]
  have e : 3 * (a : ℚ) + 2 * b = 27 * σ.sgn * t * a := by rw [hb]; ring
  rw [e]
  field_simp
  have : (σ.sgn : ℚ) * (σ.sgn * t) = t := by rw [← mul_assoc, ← sq, hs, one_mul]
  nlinarith [this]

/-- The explicit weights `a = 2 den t`, `b = 27 s num - 3 den`, `c = den - 27 s num` of target `t` on `σ`. -/
theorem row_of (σ : Support) (t : ℚ) (h9 : (σ.sgn : ℚ) * t ≠ 1 / 9) (h27 : (σ.sgn : ℚ) * t ≠ 1 / 27) :
    PlaneRow t := by
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  have hnd : t * t.den = t.num := Rat.mul_den_eq_num t
  refine ⟨σ, 2 * t.den, 27 * σ.sgn * t.num - 3 * t.den, t.den - 27 * σ.sgn * t.num, by ring,
    ?_, ?_, ?_, ?_⟩
  · have := t.den_pos; omega
  · intro hb
    apply h9
    have hb' : (27 * (σ.sgn : ℚ) * t.num - 3 * t.den) = 0 := by exact_mod_cast hb
    have : ((σ.sgn : ℚ) * t - 1 / 9) * t.den = 0 := by
      linear_combination (1 / 27) * hb' + (σ.sgn : ℚ) * hnd
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hd.ne'
  · intro hc
    apply h27
    have hc' : ((t.den : ℚ) - 27 * σ.sgn * t.num) = 0 := by exact_mod_cast hc
    have : ((σ.sgn : ℚ) * t - 1 / 27) * t.den = 0 := by
      linear_combination (-1 / 27) * hc' + (σ.sgn : ℚ) * hnd
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hd.ne'
  · apply planeT_of σ _ _ (by have := t.den_pos; omega) t
    push_cast
    linear_combination (-27 * (σ.sgn : ℚ)) * hnd

/-- **Every rational `t` has a plane frame with three nonzero weights** (Theorem R, P113): on `S⁺` with
`a = 2 den t`, `b = 27 num - 3 den`, except at `t ∈ {1/9, 1/27}`, where `S⁻` is used. -/
theorem exists_planeRow (t : ℚ) : PlaneRow t := by
  by_cases h : t = 1 / 9 ∨ t = 1 / 27
  · refine row_of .minus t ?_ ?_ <;> rcases h with rfl | rfl <;> norm_num [Support.sgn]
  · push_neg at h
    exact row_of .plus t (by simpa [Support.sgn] using h.1) (by simpa [Support.sgn] using h.2)

/-! ### Non-vanishing (P110) -/

/-- The block geometry of the plane: `altGeom (1/6)`, `α = 1/12`. -/
def planeC : ℚ := 1 / 6

theorem planeC_pos : 0 < planeC := by norm_num [planeC]

theorem planeC_le_one : planeC ≤ 1 := by norm_num [planeC]

/-- The alternating geometry of the plane, `c = 2α = 1/6`. -/
noncomputable abbrev planeG : BlockGeom := altGeom planeC planeC_pos

/-- The selection depth of the plane geometry (period `L = 2`, three atoms). -/
noncomputable def planeDepth : ℕ := planeG.selectionDepth (planeFrame .plus 1 1 (-2) (by norm_num)) 2

theorem planeDepth_le : planeDepth ≤ 64 := by
  unfold planeDepth BlockGeom.selectionDepth
  decide +kernel

theorem selectionDepth_plane (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) :
    planeG.selectionDepth (planeFrame σ a b c h0) 2 = planeDepth := rfl

theorem plane_w_ne {σ : Support} {a b c : ℤ} {h0 : a + b + c = 0} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (i : Fin (planeFrame σ a b c h0).d) : (planeFrame σ a b c h0).w i ≠ 0 := by
  have key : ∀ j : Fin 3, ![a, b, c] j ≠ 0 := by
    intro j; fin_cases j
    · exact ha
    · exact hb
    · exact hc
  exact key i

/-- **Non-vanishing of the even-scale plane family** (P110, Theorem UNV): for three nonzero weights, and every
depth `≥ planeDepth`, the even-scale members of `altGeom (1/6)` do not all vanish at a rational point. -/
theorem plane_nv0_even (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (depth : ℕ) (hdepth : planeDepth ≤ depth) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, ((planeG.family (planeFrame σ a b c h0) depth).restrictAdm (fun i => i.1 % 2 = 0)).Adm n ∧
        planeG.scale n = 2 * s ∧
        ((planeG.family (planeFrame σ a b c h0) depth).restrictAdm (fun i => i.1 % 2 = 0)).evalQ n x ≠ 0 := by
  obtain ⟨R0, hR⟩ := planeG.hasNV0 (planeFrame σ a b c h0) 2 depth (by norm_num) (by show 1 ≤ 3; norm_num)
    (plane_w_ne ha hb hc)
    (fun i => by simp [planeG, planeC, altGeom, single, commonB])
    (fun i => by simp [planeG, planeC, altGeom, single, rowB])
    (fun i => by simp [planeG, planeC, altGeom, single, colB]) hdepth
  refine ⟨R0, fun s hs x => ?_⟩
  obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
  exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : planeG.scale n = n.1 := rfl; omega⟩, hsc, hne⟩

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.plane_const
#print axioms CatalanCore.Uniform.Bank.Plane1.exists_planeRow
#print axioms CatalanCore.Uniform.Bank.Plane1.plane_nv0_even
#print axioms CatalanCore.Uniform.Bank.Plane1.planeFrame_contourCheck
