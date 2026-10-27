module
public import CatalanCore.Uniform.Frame.Family
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
@[expose] public section

namespace CatalanCore.Uniform
open Finset Polynomial Matrix

/-- Finite all-deletion-to-window estimate. `k` common nodes were already
removed; `S` ranges over all further retained common nodes. The proof uses
multilinearity, so it does not require invertibility, a selector or positivity. -/
theorem deletion_window_finite (Fr : Frame)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (common : ι → ℕ) (rows cols : κ → ℕ)
    (r k : ℕ) (D c x t : ℝ)
    (hminor : ∀ S : Finset ι,
      |(Rect.FullN Fr (fun a : S => common a.1) rows cols x).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * (k + (Fintype.card ι - S.card : ℕ))))
    (ht : |t| ≤ Real.exp (-c * r)) :
    |(Rect.FullN Fr common rows cols (x + t)).det| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r * k + Fintype.card ι * Real.log 2) := by
  rw [Rect.det_fullN_expansion]
  let B := Real.exp (-D * (r : ℝ) ^ 2 + c * r * k)
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hterm (S : Finset ι) :
      |t ^ (Fintype.card ι - S.card) *
        (Rect.FullN Fr (fun a : S => common a.1) rows cols x).det| ≤ B := by
    rw [abs_mul, abs_pow]
    calc
      |t| ^ (Fintype.card ι - S.card) *
          |(Rect.FullN Fr (fun a : S => common a.1) rows cols x).det| ≤
        Real.exp (-c * r) ^ (Fintype.card ι - S.card) *
          Real.exp (-D * (r : ℝ) ^ 2 + c * r * (k + (Fintype.card ι - S.card : ℕ))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ht _)
          (hminor S) (abs_nonneg _) (by positivity)
      _ = B := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
  calc
    |∑ S ∈ (univ : Finset ι).powerset,
        t ^ (Fintype.card ι - S.card) *
          (Rect.FullN Fr (fun a : S => common a.1) rows cols x).det| ≤
      ∑ S ∈ (univ : Finset ι).powerset,
        |t ^ (Fintype.card ι - S.card) *
          (Rect.FullN Fr (fun a : S => common a.1) rows cols x).det| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ (univ : Finset ι).powerset, B := Finset.sum_le_sum fun S _ => hterm S
    _ = (2 : ℝ) ^ Fintype.card ι * B := by
      simp [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
    _ = _ := by
      rw [show (2 : ℝ) ^ Fintype.card ι =
        Real.exp (Fintype.card ι * Real.log 2) by
          rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]; simp]
      rw [← Real.exp_add]
      congr 1
      ring

/-- A fixed affine error is absorbed by an arbitrarily small quadratic loss.
This supplies the uniform finite threshold for bounded-deletion windows. -/
theorem eventually_affine_le_quadratic (A B ε : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hε : 0 < ε) :
    ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → A * r + B ≤ ε * (r : ℝ) ^ 2 := by
  refine ⟨max 1 ⌈(A + B) / ε⌉₊, ?_⟩
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_left _ _).trans hr
  have hrbound : (A + B) / ε ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hmul : A + B ≤ ε * r := by
    have := (div_le_iff₀ hε).mp hrbound
    nlinarith
  have hB' : B ≤ B * r := by nlinarith
  have hmain := mul_le_mul_of_nonneg_right hmul (by linarith : (0 : ℝ) ≤ r)
  nlinarith

/-- Changing the labels of common nodes preserves the determinant because the
same permutation is applied to rows and columns. -/
theorem det_fullN_equiv (Fr : Frame)
    {ι ι' κ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [Fintype κ] [DecidableEq κ] (e : ι ≃ ι') (common : ι' → ℕ)
    (rows cols : κ → ℕ) (x : ℝ) :
    (Rect.FullN Fr (common ∘ e) rows cols x).det =
      (Rect.FullN Fr common rows cols x).det := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl κ))]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Rect.FullN, Rect.Blk, Rect.blkA, Rect.blkB, Rect.blkC, Rect.blkD,
      Matrix.fromBlocks, Matrix.one_apply, Function.comp_def]

namespace NodeFamily

/-- The analytic provider before bounded selection: every common deletion,
uniformly at the exact source constant and original physical scale. -/
def HasAllMinorDecay (G : NodeFamily) (Fr : Frame) (D c : ℝ) : Prop :=
  ∀ δ > 0, ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → ∀ S : Finset (G r).C,
    |(Rect.FullN Fr (fun a : S => ((a.1 : (G r).C) : ℕ))
      (G r).xs (G r).ys Fr.const).det| ≤
        Real.exp (-(D - δ) * (r : ℝ) ^ 2 + c * r * ((G r).C.card - S.card : ℕ))

private def flatten {α : Type} [DecidableEq α] (S : Finset α) (T : Finset S) : Finset α :=
  T.image Subtype.val

private noncomputable def flattenEquiv {α : Type} [DecidableEq α]
    (S : Finset α) (T : Finset S) : T ≃ flatten S T :=
  Equiv.ofBijective (fun a => ⟨a.1.1, Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩⟩) (by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : flatten S T => (z : α)) h
    · intro y
      obtain ⟨a, ha, hay⟩ := Finset.mem_image.mp y.2
      exact ⟨⟨a, ha⟩, Subtype.ext hay⟩)

private theorem card_flatten {α : Type} [DecidableEq α] (S : Finset α) (T : Finset S) :
    (flatten S T).card = T.card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

/-- All-minor source bounds imply the perturbed determinant estimate for each
selected member. This is an actual determinant expansion, not a source flag. -/
theorem window_of_all_minors (G : NodeFamily) (Fr : Frame) (depth : ℕ)
    {r : ℕ} (S : Finset (G r).C) (D c t : ℝ)
    (hminor : ∀ T : Finset (G r).C,
      |(Rect.FullN Fr (fun a : T => ((a.1 : (G r).C) : ℕ))
        (G r).xs (G r).ys Fr.const).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * ((G r).C.card - T.card : ℕ)))
    (ht : |t| ≤ Real.exp (-c * r)) :
    |(G.family Fr depth).evalR ⟨r, S⟩ (Fr.const + t)| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r * ((G r).C.card - S.card : ℕ) +
        S.card * Real.log 2) := by
  rw [G.evalR_polynomial]
  have hsub : ∀ T : Finset S,
      |(Rect.FullN Fr (fun a : T => (((a.1 : S).1 : (G r).C) : ℕ))
        (G r).xs (G r).ys Fr.const).det| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r *
        (((G r).C.card - S.card : ℕ) + (Fintype.card S - T.card : ℕ))) := by
    intro T
    let U := flatten S T
    let e := flattenEquiv S T
    have hdet := det_fullN_equiv Fr e
      (fun a : U => ((a.1 : (G r).C) : ℕ)) (G r).xs (G r).ys Fr.const
    change (Rect.FullN Fr (fun a : T => (((a.1 : S).1 : (G r).C) : ℕ))
      (G r).xs (G r).ys Fr.const).det =
      (Rect.FullN Fr (fun a : U => ((a.1 : (G r).C) : ℕ))
        (G r).xs (G r).ys Fr.const).det at hdet
    have hm := hminor U
    have hcard : U.card = T.card := card_flatten S T
    have hTS : T.card ≤ S.card := by simpa using Finset.card_le_univ T
    have hSC : S.card ≤ (G r).C.card := by simpa using Finset.card_le_univ S
    have hdiff : (G r).C.card - U.card =
        (G r).C.card - S.card + (S.card - T.card) := by omega
    rw [← hdet, hdiff] at hm
    simpa only [Fintype.card_coe, Nat.cast_add] using hm
  simpa only [Fintype.card_coe] using
    deletion_window_finite Fr (fun a : S => ((a.1 : (G r).C) : ℕ))
      (G r).xs (G r).ys r ((G r).C.card - S.card) D c Fr.const t hsub ht
/-- The all-common-deletion estimate yields the full paper epsilon window for
any fixed deletion depth and affine common-node count. -/
theorem scaledDecay_of_all_minors (G : NodeFamily) (Fr : Frame) (depth : ℕ)
    {D c γ K : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hcount : ∀ r, ((G r).C.card : ℝ) ≤ γ * r + K)
    (hminor : G.HasAllMinorDecay Fr D c) :
    HasScaledDecay (G.family Fr depth) G.scale D c := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨R1, hR1⟩ := hminor (ε / 2) hhalf
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨R2, hR2⟩ := eventually_affine_le_quadratic
    (c * depth + γ * Real.log 2) (K * Real.log 2) (ε / 2)
    (by positivity) (by positivity) hhalf
  refine ⟨max R1 R2, ?_⟩
  intro i hi hr t ht
  rcases i with ⟨r, S⟩
  have hr1 : R1 ≤ r := (le_max_left _ _).trans hr
  have hr2 : R2 ≤ r := (le_max_right _ _).trans hr
  have ht' : |t| ≤ Real.exp (-c * r) := by
    apply ht.trans (Real.exp_le_exp.mpr ?_)
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    nlinarith
  have hfinite := G.window_of_all_minors Fr depth S (D - ε / 2) c t (hR1 r hr1) ht'
  apply hfinite.trans
  apply Real.exp_le_exp.mpr
  have hdepth : (G r).C.card - S.card ≤ depth := hi
  have hdepthR : (((G r).C.card - S.card : ℕ) : ℝ) ≤ depth := by exact_mod_cast hdepth
  have hS : (S.card : ℝ) ≤ (G r).C.card := by
    exact_mod_cast (show S.card ≤ (G r).C.card from by simpa using Finset.card_le_univ S)
  have hSk : (S.card : ℝ) * Real.log 2 ≤ (γ * r + K) * Real.log 2 :=
    mul_le_mul_of_nonneg_right (hS.trans (hcount r)) hlog2
  have hd := mul_le_mul_of_nonneg_left hdepthR
    (mul_nonneg hc (Nat.cast_nonneg r))
  have herr := hR2 r hr2
  dsimp [NodeFamily.scale, NodeFamily.family]
  nlinarith only [hSk, hd, herr]

end NodeFamily
end CatalanCore.Uniform


