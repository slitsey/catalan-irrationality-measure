module

public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Frame.Deletion

@[expose] public section
set_option Elab.async false

/-!
# The deletion window for the Löwner family of two sequences (lane H, wave H2c; ledger S15, mixed `FullN`)

`SeqAllMinorDecay f g const G D c` is the analytic provider of the support route, the analogue of
`NodeFamily.HasAllMinorDecay`: every principal common-node restriction of `seqFullN f g … const` is at most
`exp (-(D - δ) r² + c r · (deleted nodes))`.  `scaledDecay_of_seq_all_minors` is the mixed copy of
`NodeFamily.scaledDecay_of_all_minors`: it gives `HasScaledDecay (seqFamily f g const G depth) scale D c`.

All of it is the multilinearity expansion `det_blk_expansion` and arithmetic, with no frame in sight.
-/

open Finset Polynomial Matrix

namespace CatalanCore.Uniform.Support

open CatalanCore CatalanCore.Rect CatalanCore.Uniform

/-- Finite all-deletion-to-window estimate for `seqFullN` (the mixed copy of `deletion_window_finite`). -/
theorem seq_deletion_window_finite (f g : ℕ → ℚ)
    {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (common : ι → ℕ) (rows cols : κ → ℕ)
    (r k : ℕ) (D c x t : ℝ)
    (hminor : ∀ S : Finset ι,
      |(seqFullN f g (fun a : S => common a.1) rows cols x).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * (k + (Fintype.card ι - S.card : ℕ))))
    (ht : |t| ≤ Real.exp (-c * r)) :
    |(seqFullN f g common rows cols (x + t)).det| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r * k + Fintype.card ι * Real.log 2) := by
  have hexp := det_blk_expansion
    (Matrix.of fun a b : ι => algebraMap ℚ ℝ (lw f g (common a) (common b)))
    (Matrix.of fun a j : _ => algebraMap ℚ ℝ (lw f g (common a) (cols j)))
    (Matrix.of fun i b : _ => algebraMap ℚ ℝ (lw f g (rows i) (common b)))
    (Matrix.of fun i j : κ => algebraMap ℚ ℝ (lw f g (rows i) (cols j))) x t
  have hS : ∀ S : Finset ι, (blkRestrict
      (Matrix.of fun a b : ι => algebraMap ℚ ℝ (lw f g (common a) (common b)))
      (Matrix.of fun a j : _ => algebraMap ℚ ℝ (lw f g (common a) (cols j)))
      (Matrix.of fun i b : _ => algebraMap ℚ ℝ (lw f g (rows i) (common b)))
      (Matrix.of fun i j : κ => algebraMap ℚ ℝ (lw f g (rows i) (cols j))) S x).det =
      (seqFullN f g (fun a : S => common a.1) rows cols x).det := fun S => rfl
  have hfull : (seqFullN f g common rows cols (x + t)).det = ∑ S ∈ (univ : Finset ι).powerset,
      t ^ (Fintype.card ι - S.card) * (seqFullN f g (fun a : S => common a.1) rows cols x).det := by
    rw [show seqFullN f g common rows cols (x + t) = Blk
      (Matrix.of fun a b : ι => algebraMap ℚ ℝ (lw f g (common a) (common b)))
      (Matrix.of fun a j : _ => algebraMap ℚ ℝ (lw f g (common a) (cols j)))
      (Matrix.of fun i b : _ => algebraMap ℚ ℝ (lw f g (rows i) (common b)))
      (Matrix.of fun i j : κ => algebraMap ℚ ℝ (lw f g (rows i) (cols j))) (x + t) from rfl, hexp]
    exact Finset.sum_congr rfl (fun S _ => by rw [hS S])
  rw [hfull]
  let B := Real.exp (-D * (r : ℝ) ^ 2 + c * r * k)
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hterm (S : Finset ι) :
      |t ^ (Fintype.card ι - S.card) *
        (seqFullN f g (fun a : S => common a.1) rows cols x).det| ≤ B := by
    rw [abs_mul, abs_pow]
    calc
      |t| ^ (Fintype.card ι - S.card) *
          |(seqFullN f g (fun a : S => common a.1) rows cols x).det| ≤
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
          (seqFullN f g (fun a : S => common a.1) rows cols x).det| ≤
      ∑ S ∈ (univ : Finset ι).powerset,
        |t ^ (Fintype.card ι - S.card) *
          (seqFullN f g (fun a : S => common a.1) rows cols x).det| :=
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

/-- Relabelling the common nodes preserves the determinant (the same permutation on rows and columns). -/
theorem det_seqFullN_equiv (f g : ℕ → ℚ)
    {ι ι' κ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    [Fintype κ] [DecidableEq κ] (e : ι ≃ ι') (common : ι' → ℕ)
    (rows cols : κ → ℕ) (x : ℝ) :
    (seqFullN f g (common ∘ e) rows cols x).det = (seqFullN f g common rows cols x).det := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl κ))]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply, Function.comp_def]

/-- The analytic provider of the support route: every principal common-node restriction. -/
def SeqAllMinorDecay (f g : ℕ → ℚ) (const : ℝ) (G : NodeFamily) (D c : ℝ) : Prop :=
  ∀ δ > 0, ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → ∀ S : Finset (G r).C,
    |(seqFullN f g (fun a : S => ((a.1 : (G r).C) : ℕ)) (G r).xs (G r).ys const).det| ≤
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
    (flatten S T).card = T.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

/-- All-minor bounds imply the perturbed determinant estimate for each member. -/
theorem seq_window_of_all_minors (f g : ℕ → ℚ) (const : ℝ) (G : NodeFamily) (depth : ℕ)
    {r : ℕ} (S : Finset (G r).C) (D c t : ℝ)
    (hminor : ∀ T : Finset (G r).C,
      |(seqFullN f g (fun a : T => ((a.1 : (G r).C) : ℕ)) (G r).xs (G r).ys const).det| ≤
        Real.exp (-D * (r : ℝ) ^ 2 + c * r * ((G r).C.card - T.card : ℕ)))
    (ht : |t| ≤ Real.exp (-c * r)) :
    |(seqFamily f g const G depth).evalR ⟨r, S⟩ (const + t)| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r * ((G r).C.card - S.card : ℕ) +
        S.card * Real.log 2) := by
  rw [SeqFamily.evalR_poly]
  have hsub : ∀ T : Finset S,
      |(seqFullN f g (fun a : T => (((a.1 : S).1 : (G r).C) : ℕ))
        (G r).xs (G r).ys const).det| ≤
      Real.exp (-D * (r : ℝ) ^ 2 + c * r *
        (((G r).C.card - S.card : ℕ) + (Fintype.card S - T.card : ℕ))) := by
    intro T
    let U := flatten S T
    let e := flattenEquiv S T
    have hdet := det_seqFullN_equiv f g e
      (fun a : U => ((a.1 : (G r).C) : ℕ)) (G r).xs (G r).ys const
    change (seqFullN f g (fun a : T => (((a.1 : S).1 : (G r).C) : ℕ))
      (G r).xs (G r).ys const).det =
      (seqFullN f g (fun a : U => ((a.1 : (G r).C) : ℕ))
        (G r).xs (G r).ys const).det at hdet
    have hm := hminor U
    have hcard : U.card = T.card := card_flatten S T
    have hTS : T.card ≤ S.card := by simpa using Finset.card_le_univ T
    have hSC : S.card ≤ (G r).C.card := by simpa using Finset.card_le_univ S
    have hdiff : (G r).C.card - U.card =
        (G r).C.card - S.card + (S.card - T.card) := by omega
    rw [← hdet, hdiff] at hm
    simpa only [Fintype.card_coe, Nat.cast_add] using hm
  simpa only [Fintype.card_coe] using
    seq_deletion_window_finite f g (fun a : S => ((a.1 : (G r).C) : ℕ))
      (G r).xs (G r).ys r ((G r).C.card - S.card) D c const t hsub ht

/-- **The mixed copy of `scaledDecay_of_all_minors`.**  The all-common-deletion estimate yields the
epsilon window of `seqFamily` for any fixed deletion depth and affine common-node count. -/
theorem scaledDecay_of_seq_all_minors (f g : ℕ → ℚ) (const : ℝ) (G : NodeFamily) (depth : ℕ)
    {D c γ K : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ) (hK : 0 ≤ K)
    (hcount : ∀ r, ((G r).C.card : ℝ) ≤ γ * r + K)
    (hminor : SeqAllMinorDecay f g const G D c) :
    HasScaledDecay (seqFamily f g const G depth) (SeqFamily.scale G) D c := by
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
  have hfinite := seq_window_of_all_minors f g const G depth S (D - ε / 2) c t (hR1 r hr1) ht'
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
  dsimp [SeqFamily.scale]
  nlinarith only [hSk, hd, herr]

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.seq_deletion_window_finite
#print axioms CatalanCore.Uniform.Support.scaledDecay_of_seq_all_minors
