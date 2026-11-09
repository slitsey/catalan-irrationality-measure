module

public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily
public import CatalanCore.Uniform.Frame.NVAdapter
public import CatalanCore.Uniform.Content.Shape.Alt

@[expose] public section

/-!
# Nonvanishing for every support datum (lane H, wave H2; ledger S08, P211)

**Theorem N.**  For a support datum `D` with `d = ∑ w(s)`, every geometry whose common nodes are `[0, r)`
and whose full node set is the interval `[0, r + 2m)`, and every `r ≥ max(1, d - 2)`, every rational `x`
admits a deletion `I ⊂ C` with `|I| ≤ ⌊d/2⌋` such that the Löwner minor `P_{r, I}(x) ≠ 0`.

The proof is the step-component engine of `NV.*` with step `L = 1` and the pair
`𝖣 = ∏ (z + s)^{w(s)}`, `A = 𝖣 δ` of the datum: `StepData` (value and jet fields) is the identity
`𝖣 δ = A` and its derivative; `IsolatedStepPole` is `a = -s₀` for any shift `s₀`: `A(-s₀)` is
`a_{s₀}` (order 1) or `-b_{s₀}` (order 2) times `∏_{s ≠ s₀}(s - s₀)^{w(s)} ≠ 0`, and the translates
`-s₀ ± n` (`n ≥ 1`) are not roots of `𝖣` as shifts differ by less than `1`.  The hypotheses follow from the
definition of a datum, so nothing is assumed.  `datum_common_deletion` is the engine for an arbitrary
geometry (with the visibility count as a hypothesis), `support_nv0_even` the paper statement on the
interval geometry, `seqFamily_hasNV0_even` the adapter for the family `seqFamily D.f D.e`.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Uniform.Support

open CatalanCore CatalanCore.Rect

namespace Datum

variable (D : Datum)

/-! ### The pair `(𝖣, A)` -/

theorem Dpoly_eq_mul (i : Fin D.n) :
    D.Dpoly = (X + C (D.s i)) ^ D.w i * D.Dexc i := by
  unfold Dpoly Dexc
  exact (Finset.mul_prod_erase univ (fun j => (X + C (D.s j)) ^ D.w j) (mem_univ i)).symm

theorem eval_Dpoly (x : ℚ) : D.Dpoly.eval x = ∏ i, (x + D.s i) ^ D.w i := by
  simp [Dpoly, eval_prod]

theorem eval_Dexc (i : Fin D.n) (x : ℚ) :
    (D.Dexc i).eval x = ∏ j ∈ univ.erase i, (x + D.s j) ^ D.w j := by
  simp [Dexc, eval_prod]

theorem Dpoly_eval_ne (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) : D.Dpoly.eval x ≠ 0 := by
  rw [eval_Dpoly]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)

theorem Dpoly_eval_pole (i : Fin D.n) : D.Dpoly.eval (-D.s i) = 0 := by
  rw [eval_Dpoly]
  exact Finset.prod_eq_zero (mem_univ i) (by
    have : (-D.s i + D.s i) = 0 := by ring
    rw [this]; exact zero_pow (by have := D.w_pos i; omega))

theorem Dexc_eval_pole_ne (i : Fin D.n) : (D.Dexc i).eval (-D.s i) ≠ 0 := by
  rw [eval_Dexc]
  refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  intro h
  exact hji (D.hinj (by linarith))

theorem Dexc_eval_pole_other (i j : Fin D.n) (hij : i ≠ j) : (D.Dexc i).eval (-D.s j) = 0 := by
  rw [eval_Dexc]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij.symm, mem_univ j⟩) (by
    have : (-D.s j + D.s j) = 0 := by ring
    rw [this]; exact zero_pow (by have := D.w_pos j; omega))

/-! #### One term of `A` -/

/-- The case split on the order of a shift. -/
theorem w_cases (i : Fin D.n) : (D.w i = 1 ∧ D.b i = 0) ∨ (D.w i = 2 ∧ D.b i ≠ 0) := by
  unfold w
  by_cases h : D.b i = 0
  · left; simp [h]
  · right; simp [h]

/-- The term of `A` of the shift `i`. -/
noncomputable def Aterm (i : Fin D.n) : ℚ[X] :=
  C (D.a i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1)) -
    C (D.b i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 2))

theorem Apoly_eq_sum : D.Apoly = ∑ i, D.Aterm i := rfl

/-- The pointwise pole identity of one term: `A_i(x) = 𝖣(x)(a/(x+s) - b/(x+s)²)`. -/
theorem Aterm_eval (i : Fin D.n) (x : ℚ) (hx : x + D.s i ≠ 0) :
    (D.Aterm i).eval x = D.Dpoly.eval x *
      ((D.a i : ℚ) / (x + D.s i) - (D.b i : ℚ) / (x + D.s i) ^ 2) := by
  rw [Dpoly_eq_mul D i]
  rcases D.w_cases i with ⟨hw, hb⟩ | ⟨hw, hb⟩
  · simp only [Aterm, hw, hb]
    simp
    field_simp
  · simp only [Aterm, hw]
    simp
    field_simp
    try ring

/-- The derivative identity of one term. -/
theorem Aterm_deriv_eval (i : Fin D.n) (x : ℚ) (hx : x + D.s i ≠ 0) :
    (D.Aterm i).derivative.eval x =
      D.Dpoly.derivative.eval x *
        ((D.a i : ℚ) / (x + D.s i) - (D.b i : ℚ) / (x + D.s i) ^ 2) +
      D.Dpoly.eval x *
        (-(D.a i : ℚ) / (x + D.s i) ^ 2 + 2 * (D.b i : ℚ) / (x + D.s i) ^ 3) := by
  rw [Dpoly_eq_mul D i]
  rcases D.w_cases i with ⟨hw, hb⟩ | ⟨hw, hb⟩
  · simp only [Aterm, hw, hb]
    simp [derivative_mul]
    field_simp
    try ring
  · simp only [Aterm, hw]
    simp [derivative_mul, derivative_pow]
    field_simp
    try ring

theorem Apoly_eval (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) :
    D.Apoly.eval x = D.Dpoly.eval x * D.delta x := by
  rw [Apoly_eq_sum, eval_finsetSum, delta, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Aterm_eval D i x (hx i)

theorem Apoly_deriv_eval (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) :
    D.Apoly.derivative.eval x =
      D.Dpoly.derivative.eval x * D.delta x + D.Dpoly.eval x * D.delta1 x := by
  rw [Apoly_eq_sum, derivative_sum, eval_finsetSum, delta, delta1, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Aterm_deriv_eval D i x (hx i)

/-! #### Degrees -/

theorem Dexc_monic (i : Fin D.n) : (D.Dexc i).Monic :=
  monic_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _

theorem Dexc_natDegree (i : Fin D.n) : (D.Dexc i).natDegree = D.d - D.w i := by
  have h : (D.Dexc i).natDegree = ∑ j ∈ univ.erase i, D.w j := by
    unfold Dexc
    rw [natDegree_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _]
    exact Finset.sum_congr rfl fun j _ => by rw [natDegree_pow, natDegree_X_add_C, mul_one]
  rw [h]
  have := Finset.sum_erase_add univ D.w (mem_univ i)
  unfold d
  omega

theorem Dpoly_monic : D.Dpoly.Monic :=
  monic_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _

theorem Dpoly_natDegree : D.Dpoly.natDegree = D.d := by
  unfold Dpoly d
  rw [natDegree_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _]
  exact Finset.sum_congr rfl fun j _ => by rw [natDegree_pow, natDegree_X_add_C, mul_one]

theorem d_ge_two : 2 ≤ D.d := by
  by_cases h : ∃ i, D.w i = 2
  · obtain ⟨i, hi⟩ := h
    have := Finset.single_le_sum (f := D.w) (fun j _ => Nat.zero_le _) (mem_univ i)
    unfold d; omega
  · simp only [not_exists] at h
    have hw1 : ∀ i, D.w i = 1 := fun i => by
      have := D.w_pos i; have := D.w_le i; have := h i; omega
    have hb0 : ∀ i, D.b i = 0 := fun i => by
      rcases D.w_cases i with ⟨_, hb⟩ | ⟨hw2, _⟩
      · exact hb
      · have := hw1 i; omega
    have hd : D.d = D.n := by simp [d, hw1]
    rw [hd]
    by_contra hlt
    have hn1 : D.n = 1 := by have := D.hn; omega
    let i0 : Fin D.n := ⟨0, D.hn⟩
    have hall : ∀ j : Fin D.n, j = i0 := fun j => Fin.ext (by have := j.2; simp [i0]; omega)
    have hs : ∑ i, D.a i = D.a i0 :=
      Finset.sum_eq_single_of_mem i0 (mem_univ _) fun j _ hj => absurd (hall j) hj
    have := D.hbal
    rw [hs] at this
    rcases D.hab i0 with h1 | h1
    · exact h1 this
    · exact h1 (hb0 i0)

theorem Aterm1_natDegree (i : Fin D.n) :
    (C (D.a i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1))).natDegree ≤ D.d - 1 := by
  have hle : D.w i ≤ D.d := Finset.single_le_sum (f := D.w) (fun j _ => Nat.zero_le _) (mem_univ i)
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_mul_le).trans ?_
  rw [Dexc_natDegree, natDegree_pow, natDegree_X_add_C]
  have := D.w_pos i
  omega

theorem w_le_d (i : Fin D.n) : D.w i ≤ D.d :=
  Finset.single_le_sum (f := D.w) (fun j _ => Nat.zero_le _) (mem_univ i)

theorem T1_monic (i : Fin D.n) : (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1)).Monic :=
  (D.Dexc_monic i).mul ((monic_X_add_C _).pow _)

theorem T1_natDegree (i : Fin D.n) :
    (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1)).natDegree = D.d - 1 := by
  rw [(D.Dexc_monic i).natDegree_mul ((monic_X_add_C _).pow _), Dexc_natDegree, natDegree_pow,
    natDegree_X_add_C]
  have := D.w_pos i
  have := D.w_le_d i
  omega

theorem T2_natDegree_le (i : Fin D.n) (hb : D.b i ≠ 0) :
    (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 2)).natDegree ≤ D.d - 2 := by
  refine (natDegree_mul_le).trans ?_
  rw [Dexc_natDegree, natDegree_pow, natDegree_X_add_C]
  rcases D.w_cases i with ⟨_, h⟩ | ⟨hw, _⟩
  · exact absurd h hb
  · rw [hw]; omega

/-- Coefficients of one term of `A` above degree `d - 2`. -/
theorem Aterm_coeff (i : Fin D.n) (N : ℕ) (hN : D.d - 2 < N) :
    (D.Aterm i).coeff N = if N = D.d - 1 then (D.a i : ℚ) else 0 := by
  have hT1 : (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 1)).coeff N = if N = D.d - 1 then 1 else 0 := by
    split_ifs with h
    · rw [h, ← T1_natDegree D i]; exact (T1_monic D i).coeff_natDegree
    · apply coeff_eq_zero_of_natDegree_lt
      rw [T1_natDegree]
      have := d_ge_two D
      omega
  have hT2 : (C (D.b i : ℚ) * (D.Dexc i * (X + C (D.s i)) ^ (D.w i - 2))).coeff N = 0 := by
    by_cases hb : D.b i = 0
    · simp [hb]
    · apply coeff_eq_zero_of_natDegree_lt
      exact lt_of_le_of_lt ((natDegree_C_mul_le _ _).trans (T2_natDegree_le D i hb)) hN
  unfold Aterm
  rw [coeff_sub, coeff_C_mul, hT1, hT2]
  split_ifs <;> simp

theorem Apoly_natDegree_le : D.Apoly.natDegree ≤ D.d - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [Apoly_eq_sum, finsetSum_coeff]
  simp only [Aterm_coeff D _ N hN]
  split_ifs
  · have h := D.hbal
    have : ∑ i, (D.a i : ℚ) = 0 := by exact_mod_cast h
    exact this
  · simp

/-! #### Poles -/

theorem Aterm_eval_pole_other (i j : Fin D.n) (hij : i ≠ j) : (D.Aterm i).eval (-D.s j) = 0 := by
  simp [Aterm, Dexc_eval_pole_other D i j hij]

theorem Aterm_eval_pole_self (i : Fin D.n) : (D.Aterm i).eval (-D.s i) ≠ 0 := by
  have hE := Dexc_eval_pole_ne D i
  rcases D.w_cases i with ⟨hw, hb⟩ | ⟨hw, hb⟩
  · have ha : D.a i ≠ 0 := by
      rcases D.hab i with h | h
      · exact h
      · exact absurd hb h
    simp [Aterm, hw, hb]
    exact ⟨ha, hE⟩
  · simp [Aterm, hw]
    exact ⟨hb, hE⟩

theorem Apoly_eval_pole (i : Fin D.n) : D.Apoly.eval (-D.s i) ≠ 0 := by
  rw [Apoly_eq_sum, eval_finsetSum,
    Finset.sum_eq_single_of_mem i (mem_univ _) fun j _ hj =>
      Aterm_eval_pole_other D j i hj]
  exact Aterm_eval_pole_self D i

/-! #### The step data of the engine -/

theorem isolatedPole (i : Fin D.n) :
    NV.IsolatedStepPole ((1 : ℕ) : ℚ) (-D.s i) D.Dpoly D.Apoly where
  step_ne_zero := by simp
  pole := D.Dpoly_eval_pole i
  residue := D.Apoly_eval_pole i
  forward := by
    intro n
    apply D.Dpoly_eval_ne
    intro j
    have h1 := D.hs i
    have h2 := D.hs j
    have h3 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast
    intro h
    linarith
  backward := by
    intro n
    apply D.Dpoly_eval_ne
    intro j
    have h1 := D.hs i
    have h2 := D.hs j
    have h3 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast
    intro h
    linarith

theorem f_succ (t : ℕ) : D.f (t + 1) - D.f t = D.delta t := by
  unfold f; rw [Finset.sum_range_succ]; ring

theorem e_succ (t : ℕ) : D.e (t + 1) - D.e t = -D.delta1 t := by
  unfold e; rw [Finset.sum_range_succ]; ring

theorem shift_ne (a : ℕ) (i : Fin D.n) : (a : ℚ) + D.s i ≠ 0 := by
  have h1 := D.hs i
  have h3 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  intro h; linarith

/-- The cleared step equations of the datum, with step `L = 1`: the value field is `𝖣 δ = A` and the jet
field is its derivative. -/
theorem stepData (U : ℚ) :
    NV.StepData 1 D.Dpoly D.Apoly (NV.onNaturals D.f) (NV.onNaturals fun t => U - D.e t) where
  value a := by
    have hc : (a : ℚ) + ((1 : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hc, NV.onNaturals_nat, NV.onNaturals_nat, f_succ, D.Apoly_eval _ (D.shift_ne a)]
  jet a := by
    have hc : (a : ℚ) + ((1 : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hc, NV.onNaturals_nat, NV.onNaturals_nat, NV.onNaturals_nat, NV.onNaturals_nat, f_succ,
      D.Apoly_deriv_eval _ (D.shift_ne a)]
    have := e_succ D a
    have h2 : (U - D.e (a + 1)) - (U - D.e a) = D.delta1 a := by linarith
    rw [h2]

end Datum

namespace PoleDatum

variable (D : PoleDatum)

theorem Dpoly_eq_mul (i : Fin D.n) :
    D.Dpoly = (X + C (D.s i)) ^ D.w i * D.Dexc i := by
  unfold Dpoly Dexc
  exact (Finset.mul_prod_erase univ (fun j => (X + C (D.s j)) ^ D.w j) (mem_univ i)).symm

theorem eval_Dpoly (x : ℚ) : D.Dpoly.eval x = ∏ i, (x + D.s i) ^ D.w i := by
  simp [Dpoly, eval_prod]

theorem eval_Dexc (i : Fin D.n) (x : ℚ) :
    (D.Dexc i).eval x = ∏ j ∈ univ.erase i, (x + D.s j) ^ D.w j := by
  simp [Dexc, eval_prod]

theorem Dpoly_eval_ne (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) : D.Dpoly.eval x ≠ 0 := by
  rw [eval_Dpoly]
  exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hx i)

theorem Dpoly_eval_pole (i : Fin D.n) : D.Dpoly.eval (-D.s i) = 0 := by
  rw [eval_Dpoly]
  exact Finset.prod_eq_zero (mem_univ i) (by
    have : (-D.s i + D.s i) = 0 := by ring
    rw [this]; exact zero_pow (by have := D.hw i; omega))

theorem Dexc_eval_pole_ne (i : Fin D.n) : (D.Dexc i).eval (-D.s i) ≠ 0 := by
  rw [eval_Dexc]
  refine Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ ?_
  have hji : j ≠ i := (Finset.mem_erase.1 hj).1
  intro h
  exact hji (D.hinj (by linarith))

theorem Dexc_eval_pole_other (i j : Fin D.n) (hij : i ≠ j) : (D.Dexc i).eval (-D.s j) = 0 := by
  rw [eval_Dexc]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hij.symm, mem_univ j⟩) (by
    have : (-D.s j + D.s j) = 0 := by ring
    rw [this]; exact zero_pow (by have := D.hw j; omega))


noncomputable def Pterm (i : Fin D.n) (j : ℕ) : ℚ[X] :=
  D.Dexc i * (X + C (D.s i)) ^ (D.w i - j)

theorem Pterm_mul (i : Fin D.n) (j : ℕ) (hj : j ≤ D.w i) :
    D.Pterm i j * (X + C (D.s i)) ^ j = D.Dpoly := by
  rw [Dpoly_eq_mul D i, Pterm, mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  ring

theorem Pterm_eval (i : Fin D.n) (j : ℕ) (hj : j ≤ D.w i)
    (x : ℚ) (hx : x + D.s i ≠ 0) :
    (D.Pterm i j).eval x = D.Dpoly.eval x / (x + D.s i) ^ j := by
  apply (eq_div_iff (pow_ne_zero j hx)).2
  simpa using congrArg (fun P : ℚ[X] => P.eval x) (D.Pterm_mul i j hj)

theorem Pterm_deriv_eval (i : Fin D.n) (j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ D.w i)
    (x : ℚ) (hx : x + D.s i ≠ 0) :
    (D.Pterm i j).derivative.eval x =
      D.Dpoly.derivative.eval x / (x + D.s i) ^ j -
      (j : ℚ) * D.Dpoly.eval x / (x + D.s i) ^ (j + 1) := by
  have hd := congrArg (fun P : ℚ[X] => P.derivative.eval x) (D.Pterm_mul i j hj)
  simp only [derivative_mul, derivative_pow, derivative_X_add_C, mul_one,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_natCast] at hd
  have hv := D.Pterm_eval i j hj x hx
  have he : j - 1 + 1 = j := by omega
  have hp : (x + D.s i) ^ (j - 1) * (x + D.s i) = (x + D.s i) ^ j := by
    rw [← pow_succ, he]
  have hu : (x + D.s i) ^ (j + 1) = (x + D.s i) ^ j * (x + D.s i) := pow_succ _ _
  have hv' : (D.Pterm i j).eval x * (x + D.s i) ^ j = D.Dpoly.eval x :=
    (eq_div_iff (pow_ne_zero j hx)).mp hv
  have hd' : (D.Pterm i j).derivative.eval x *
      ((x + D.s i) ^ j * (x + D.s i)) =
      D.Dpoly.derivative.eval x * (x + D.s i) - (j : ℚ) * D.Dpoly.eval x := by
    calc
      _ = D.Dpoly.derivative.eval x * (x + D.s i) -
          (D.Pterm i j).eval x * (j : ℚ) *
            ((x + D.s i) ^ (j - 1) * (x + D.s i)) := by
        linear_combination (x + D.s i) * hd
      _ = _ := by rw [hp, ← hv']; ring
  rw [hu]
  have hdiv : D.Dpoly.derivative.eval x / (x + D.s i) ^ j =
      (D.Dpoly.derivative.eval x * (x + D.s i)) /
        ((x + D.s i) ^ j * (x + D.s i)) := by field_simp [hx]
  rw [hdiv, ← sub_div]
  exact (eq_div_iff (mul_ne_zero (pow_ne_zero j hx) hx)).2 hd'

theorem Apoly_eval (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) :
    D.Apoly.eval x = D.Dpoly.eval x * D.delta x := by
  simp only [Apoly, delta, eval_finsetSum, eval_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j hj
  rw [← eval_mul]
  change D.coeff i j * (D.Pterm i j).eval x = _
  rw [D.Pterm_eval i j (Finset.mem_Icc.mp hj).2 x (hx i)]
  ring

theorem Apoly_deriv_eval (x : ℚ) (hx : ∀ i, x + D.s i ≠ 0) :
    D.Apoly.derivative.eval x =
      D.Dpoly.derivative.eval x * D.delta x + D.Dpoly.eval x * D.delta1 x := by
  unfold Apoly delta delta1
  simp only [derivative_sum, derivative_C_mul, eval_finsetSum, eval_mul, eval_C]
  rw [mul_neg, ← sub_eq_add_neg, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  change D.coeff i j * (D.Pterm i j).derivative.eval x = _
  rw [D.Pterm_deriv_eval i j (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2 x (hx i)]
  ring

theorem Dexc_monic (i : Fin D.n) : (D.Dexc i).Monic :=
  monic_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _

theorem Dexc_natDegree (i : Fin D.n) : (D.Dexc i).natDegree = D.d - D.w i := by
  have h : (D.Dexc i).natDegree = ∑ j ∈ univ.erase i, D.w j := by
    unfold Dexc
    rw [natDegree_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _]
    exact Finset.sum_congr rfl fun j _ => by rw [natDegree_pow, natDegree_X_add_C, mul_one]
  rw [h]
  have := Finset.sum_erase_add univ D.w (mem_univ i)
  unfold d
  omega

theorem Dpoly_monic : D.Dpoly.Monic :=
  monic_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _

theorem Dpoly_natDegree : D.Dpoly.natDegree = D.d := by
  unfold Dpoly d
  rw [natDegree_prod_of_monic _ _ fun j _ => (monic_X_add_C (D.s j)).pow _]
  exact Finset.sum_congr rfl fun j _ => by rw [natDegree_pow, natDegree_X_add_C, mul_one]


theorem w_le_d (i : Fin D.n) : D.w i ≤ D.d :=
  Finset.single_le_sum (f := D.w) (fun _ _ => Nat.zero_le _) (mem_univ i)

theorem d_ge_two : 2 ≤ D.d := by
  by_contra h
  let i0 : Fin D.n := ⟨0, D.hn⟩
  have hwi : D.w i0 = 1 := by have := D.hw i0; have := D.w_le_d i0; omega
  have hn1 : D.n = 1 := by
    have hn : D.n ≤ D.d := by
      calc D.n = ∑ _ : Fin D.n, 1 := by simp
           _ ≤ ∑ i, D.w i := Finset.sum_le_sum (fun i _ => D.hw i)
    have := D.hn
    omega
  have hall : ∀ j : Fin D.n, j = i0 := fun j => Fin.ext (by have := j.2; simp [i0]; omega)
  have hs : ∑ i, D.coeff i 1 = D.coeff i0 1 :=
    Finset.sum_eq_single_of_mem i0 (mem_univ _) fun j _ hj => absurd (hall j) hj
  have hb := D.balance
  rw [hs] at hb
  apply D.top_ne i0
  simpa [hwi] using hb

theorem Pterm_monic (i : Fin D.n) (j : ℕ) : (D.Pterm i j).Monic :=
  (D.Dexc_monic i).mul ((monic_X_add_C _).pow _)

theorem Pterm_natDegree (i : Fin D.n) (j : ℕ) (hj : j ≤ D.w i) :
    (D.Pterm i j).natDegree = D.d - j := by
  unfold Pterm
  rw [(D.Dexc_monic i).natDegree_mul ((monic_X_add_C _).pow _),
    Dexc_natDegree, natDegree_pow, natDegree_X_add_C]
  have := D.w_le_d i
  omega

theorem Pterm_coeff (i : Fin D.n) (j N : ℕ)
    (hj : j ∈ Icc 1 (D.w i)) (hN : D.d - 2 < N) :
    (D.Pterm i j).coeff N = if j = 1 ∧ N = D.d - 1 then 1 else 0 := by
  obtain ⟨hj0, hjw⟩ := mem_Icc.mp hj
  by_cases he : j = 1 ∧ N = D.d - 1
  · rw [if_pos he]
    have hdeg : (D.Pterm i j).natDegree = N := by
      rw [D.Pterm_natDegree i j hjw, he.1, he.2]
    rw [← hdeg]
    exact (D.Pterm_monic i j).coeff_natDegree
  · rw [if_neg he]
    apply coeff_eq_zero_of_natDegree_lt
    rw [D.Pterm_natDegree i j hjw]
    have := D.d_ge_two
    omega

theorem Apoly_natDegree_le : D.Apoly.natDegree ≤ D.d - 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  unfold Apoly
  simp only [finsetSum_coeff, coeff_C_mul]
  have hs : ∀ i, (∑ j ∈ Icc 1 (D.w i),
      D.coeff i j * (D.Pterm i j).coeff N) =
      if N = D.d - 1 then D.coeff i 1 else 0 := by
    intro i
    have hexp : (∑ j ∈ Icc 1 (D.w i), D.coeff i j * (D.Pterm i j).coeff N) =
        ∑ j ∈ Icc 1 (D.w i), D.coeff i j * (if j = 1 ∧ N = D.d - 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [D.Pterm_coeff i j N hj hN]
    rw [hexp]
    by_cases he : N = D.d - 1
    · simp [he, D.hw i]
    · simp [he]
  change (∑ i, ∑ j ∈ Icc 1 (D.w i), D.coeff i j * (D.Pterm i j).coeff N) = 0
  simp_rw [hs]
  split_ifs
  · exact D.balance
  · simp

theorem Apoly_eval_pole_eq (i : Fin D.n) :
    D.Apoly.eval (-D.s i) = D.coeff i (D.w i) * (D.Dexc i).eval (-D.s i) := by
  unfold Apoly
  rw [eval_finsetSum, Finset.sum_eq_single_of_mem i (mem_univ _) ?_]
  · rw [eval_finsetSum,
      Finset.sum_eq_single_of_mem (D.w i) (mem_Icc.mpr ⟨D.hw i, le_rfl⟩) ?_]
    · simp
    · intro j hj hji
      have hjw := (mem_Icc.mp hj).2
      have hpos : 0 < D.w i - j := by omega
      simp [zero_pow hpos.ne']
  · intro k _ hki
    rw [eval_finsetSum]
    apply Finset.sum_eq_zero
    intro j _
    simp [D.Dexc_eval_pole_other k i hki]

theorem Apoly_eval_pole (i : Fin D.n) : D.Apoly.eval (-D.s i) ≠ 0 := by
  rw [D.Apoly_eval_pole_eq i]
  exact mul_ne_zero (D.top_ne i) (D.Dexc_eval_pole_ne i)

theorem isolatedPole (i : Fin D.n) :
    NV.IsolatedStepPole ((1 : ℕ) : ℚ) (-D.s i) D.Dpoly D.Apoly where
  step_ne_zero := by simp
  pole := D.Dpoly_eval_pole i
  residue := D.Apoly_eval_pole i
  forward := by
    intro n
    apply D.Dpoly_eval_ne
    intro j
    have h1 := D.hs i
    have h2 := D.hs j
    have h3 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast
    intro h
    linarith
  backward := by
    intro n
    apply D.Dpoly_eval_ne
    intro j
    have h1 := D.hs i
    have h2 := D.hs j
    have h3 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    push_cast
    intro h
    linarith

theorem f_succ (t : ℕ) : D.f (t + 1) - D.f t = D.delta t := by
  unfold f; rw [Finset.sum_range_succ]; ring

theorem e_succ (t : ℕ) : D.e (t + 1) - D.e t = -D.delta1 t := by
  unfold e; rw [Finset.sum_range_succ]; ring

theorem shift_ne (a : ℕ) (i : Fin D.n) : (a : ℚ) + D.s i ≠ 0 := by
  have h1 := D.hs i
  have h3 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  intro h; linarith

/-- The cleared step equations of the datum, with step `L = 1`: the value field is `𝖣 δ = A` and the jet
field is its derivative. -/
theorem stepData (U : ℚ) :
    NV.StepData 1 D.Dpoly D.Apoly (NV.onNaturals D.f) (NV.onNaturals fun t => U - D.e t) where
  value a := by
    have hc : (a : ℚ) + ((1 : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hc, NV.onNaturals_nat, NV.onNaturals_nat, f_succ, D.Apoly_eval _ (D.shift_ne a)]
  jet a := by
    have hc : (a : ℚ) + ((1 : ℕ) : ℚ) = ((a + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [hc, NV.onNaturals_nat, NV.onNaturals_nat, NV.onNaturals_nat, NV.onNaturals_nat, f_succ,
      D.Apoly_deriv_eval _ (D.shift_ne a)]
    have := e_succ D a
    have h2 : (U - D.e (a + 1)) - (U - D.e a) = D.delta1 a := by linarith
    rw [h2]

end PoleDatum

/-! ### Transport of the matrix to the field-node model -/

section Transport

open CatalanCore.Uniform.NVAdapter CatalanCore.Arith.Hybrid.FiniteFieldCorank CatalanCore.Rect.CharZeroNV

/-- The engine's scalar functions give exactly the entries of the Löwner pencil. -/
theorem loewnerEntry_nat_seq (f g : ℕ → ℚ) (U : ℚ) (a b : ℕ) :
    NV.loewnerEntry (NV.onNaturals f) (NV.onNaturals fun t => U - g t) (a : ℚ) (b : ℚ) =
      (if a = b then U else 0) + lw f g a b := by
  by_cases hab : a = b
  · subst b
    simp [NV.loewnerEntry, lw]
    ring
  · have hcast : (a : ℚ) ≠ b := by exact_mod_cast hab
    simp only [NV.loewnerEntry, if_neg hcast, NV.onNaturals_nat, if_neg hab, zero_add, lw]
    have : (b : ℚ) - a ≠ 0 := sub_ne_zero.2 (Ne.symm hcast)
    have h2 : (a : ℚ) - b ≠ 0 := sub_ne_zero.2 hcast
    field_simp
    ring

/-- The matrix of the family is the reindexed engine matrix, for arbitrary balanced finite node sets. -/
theorem seqFullN_eq_model (f g : ℕ → ℚ) (U : ℚ) (G : Rect.Geometry) :
    seqFullN f g (fun a : G.C => (a : ℕ)) G.xs G.ys U =
      ((model G).matrix (NV.onNaturals f) (NV.onNaturals fun t => U - g t)).submatrix
        (rowField G) (rowField G) := by
  rw [matrix_reindex]
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · simp only [Matrix.of_apply, rowField_inl, colField_inl]
    rw [loewnerEntry_nat_seq]
    by_cases hab : a = b
    · subst b
      simp [seqFullN, Blk, Matrix.one_apply]
      ring
    · have hne : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Subtype.ext h)
      simp [seqFullN, Blk, Matrix.one_apply, hab, hne]
  · have hy : G.ys b ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ b
    have hne : (a : ℕ) ≠ G.ys b := by
      intro h
      exact Finset.disjoint_left.mp G.disjCY a.property (h.symm ▸ hy)
    simp only [Matrix.of_apply, rowField_inl, colField_inr]
    rw [loewnerEntry_nat_seq]
    simp [hne, seqFullN, Blk]
  · have hx : G.xs a ∈ G.X' := Finset.orderEmbOfFin_mem _ _ a
    have hne : G.xs a ≠ (b : ℕ) := by
      intro h
      exact Finset.disjoint_left.mp G.disjCX b.property (h ▸ hx)
    simp only [Matrix.of_apply, rowField_inr, colField_inl]
    rw [loewnerEntry_nat_seq]
    simp [hne, seqFullN, Blk]
  · have hx : G.xs a ∈ G.X' := Finset.orderEmbOfFin_mem _ _ a
    have hy : G.ys b ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ b
    have hne : G.xs a ≠ G.ys b := by
      intro h
      exact Finset.disjoint_left.mp G.disjXY hx (h.symm ▸ hy)
    simp only [Matrix.of_apply, rowField_inr, colField_inr]
    rw [loewnerEntry_nat_seq]
    simp [hne, seqFullN, Blk]

private theorem restrict_seqFullN (f g : ℕ → ℚ) (U : ℚ) (G : Rect.Geometry) (D : Finset G.C) :
    (seqFullN f g (fun a : G.C => (a : ℕ)) G.xs G.ys U).submatrix
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id) =
    seqFullN f g (fun a : {i : G.C // i ∉ D} => ((a.val : G.C) : ℕ)) G.xs G.ys U := by
  ext a b
  rcases a with a | a <;> rcases b with b | b
  · by_cases hab : a = b
    · subst b
      simp [seqFullN, Blk]
    · have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
      simp [seqFullN, Blk, Matrix.one_apply, hab, hne]
  · rfl
  · rfl
  · rfl

private noncomputable def retainedEquiv' {I : Type} [Fintype I] [DecidableEq I]
    (D : Finset I) : {i // i ∉ D} ≃ ((univ : Finset I) \ D : Finset I) where
  toFun a := ⟨a.val, by simp [a.property]⟩
  invFun a := ⟨a.val, (Finset.mem_sdiff.mp a.property).2⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

private theorem det_seqFullN_reindex (f g : ℕ → ℚ)
    {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [DecidableEq K] (e : I ≃ J) (common : J → ℕ)
    (rows cols : K → ℕ) (U : ℚ) :
    (seqFullN f g (common ∘ e) rows cols U).det = (seqFullN f g common rows cols U).det := by
  rw [← Matrix.det_submatrix_equiv_self (Equiv.sumCongr e (Equiv.refl K))]
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply, Function.comp_def]

/-- The engine's nonzero same-index complement is a nonzero retained-common-node minor of the family. -/
theorem seq_retained_of_model_deletion (f g : ℕ → ℚ) (U : ℚ) (G : Rect.Geometry)
    (s : Finset ((model G).rows ∩ (model G).cols : Finset ℚ))
    (hnonzero : (((model G).matrix (NV.onNaturals f) (NV.onNaturals fun t => U - g t)).submatrix
      (Subtype.val : {i // i ∉ s.image (model G).common} → (model G).rows) Subtype.val).det ≠ 0) :
    ∃ S : Finset G.C, G.C.card - S.card = s.card ∧
      (seqFullN f g (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  classical
  let D : Finset G.C := s.image (commonField G).symm
  let S : Finset G.C := univ \ D
  have hDcard : D.card = s.card := Finset.card_image_of_injective _ (commonField G).symm.injective
  have hdel : s.image (model G).common = D.image (fun a => rowField G (.inl a)) := by
    dsimp [D]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro a ha
    simpa only [Equiv.apply_symm_apply, Function.comp_def] using common_compat G ((commonField G).symm a)
  rw [hdel] at hnonzero
  have hc := Rect.CharZeroNV.det_common_complement
    ((model G).matrix (NV.onNaturals f) (NV.onNaturals fun t => U - g t)) (rowField G) D
  rw [hc] at hnonzero
  have hm := (seqFullN_eq_model f g U G).symm
  have hr := congrArg (fun M : Matrix (Index G) (Index G) ℚ =>
    M.submatrix (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)
      (Sum.map (Subtype.val : {i : G.C // i ∉ D} → G.C) id)) hm
  rw [Matrix.submatrix_submatrix, restrict_seqFullN] at hr
  have hkeep : (seqFullN f g (fun a : {i : G.C // i ∉ D} => ((a.1 : G.C) : ℕ))
      G.xs G.ys U).det ≠ 0 := by
    rw [← hr]
    exact hnonzero
  let e := retainedEquiv' D
  change (seqFullN f g ((fun a : S => ((a.1 : G.C) : ℕ)) ∘ e) G.xs G.ys U).det ≠ 0 at hkeep
  rw [det_seqFullN_reindex] at hkeep
  refine ⟨S, ?_, hkeep⟩
  have hle : D.card ≤ G.C.card := by simpa using Finset.card_le_univ D
  have hS : S.card = G.C.card - D.card := by
    simp only [S, Finset.card_sdiff_of_subset (Finset.subset_univ D),
      Finset.card_univ, Fintype.card_coe]
  omega

end Transport

/-! ### Theorem N -/

section TheoremN

open CatalanCore.Uniform.NVAdapter

private theorem empty_corank' {I : Type} [Fintype I] [DecidableEq I] [IsEmpty I]
    (M : Matrix I I ℚ) : Module.finrank ℚ (LinearMap.ker M.mulVecLin) = 0 := by
  have h := Submodule.finrank_le (LinearMap.ker M.mulVecLin)
  have hdim : Module.finrank ℚ (I → ℚ) = 0 := by simp
  omega

/-- **Theorem N on an arbitrary balanced geometry** (the visibility count is a hypothesis).  For every
datum `D` and every rational `U` there is a set `S` of retained common nodes, with at most
`(d + #components(Z) + #components(C) - 2)/2` deleted, whose Löwner minor does not vanish at `U`. -/
theorem datum_common_deletion (D : Datum) (U : ℚ) (G : Rect.Geometry)
    (hvis : NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 + D.d ≤ G.C.card + 3) :
    ∃ S : Finset G.C,
      G.C.card - S.card ≤ (D.d + NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 +
        NV.componentCount G.C 1 - 2) / 2 ∧
      (seqFullN D.f D.e (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  by_cases hn : 1 ≤ G.C.card + G.k
  · let i0 : Fin D.n := ⟨0, D.hn⟩
    obtain ⟨s, hs, hdet⟩ := NV.step_component_nv (model G) 1 D.d G.C.card G.k D.Dpoly D.Apoly
      (NV.onNaturals D.f) (NV.onNaturals fun t => U - D.e t) (D.stepData U) (-D.s i0)
      (D.isolatedPole i0) D.d_ge_two D.Dpoly_natDegree.le D.Apoly_natDegree_le
      (G.C ∪ G.X' ∪ G.Y') G.C (fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha)) rfl
      (full_nodes_card G) (model_union G) (model_inter G) (model_rows_card G) hn hvis
    obtain ⟨S, hS, hdetS⟩ := seq_retained_of_model_deletion D.f D.e U G s hdet
    exact ⟨S, hS ▸ hs, hdetS⟩
  · have hc : G.C.card = 0 := by omega
    have hk : G.k = 0 := by omega
    let _ : IsEmpty G.C := Fintype.card_eq_zero_iff.mp (by simpa using hc)
    let _ : IsEmpty (Fin G.k) := Fintype.card_eq_zero_iff.mp (by simpa using hk)
    refine ⟨univ, ?_, ?_⟩
    · exact le_trans (Nat.sub_le _ _) (by rw [hc]; exact Nat.zero_le _)
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero

theorem pole_common_deletion (D : PoleDatum) (U : ℚ) (G : Rect.Geometry)
    (hvis : NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 + D.d ≤ G.C.card + 3) :
    ∃ S : Finset G.C,
      G.C.card - S.card ≤ (D.d + NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 +
        NV.componentCount G.C 1 - 2) / 2 ∧
      (seqFullN D.f D.e (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  by_cases hn : 1 ≤ G.C.card + G.k
  · let i0 : Fin D.n := ⟨0, D.hn⟩
    obtain ⟨s, hs, hdet⟩ := NV.step_component_nv (model G) 1 D.d G.C.card G.k D.Dpoly D.Apoly
      (NV.onNaturals D.f) (NV.onNaturals fun t => U - D.e t) (D.stepData U) (-D.s i0)
      (D.isolatedPole i0) D.d_ge_two D.Dpoly_natDegree.le D.Apoly_natDegree_le
      (G.C ∪ G.X' ∪ G.Y') G.C (fun a ha => Finset.mem_union_left _ (Finset.mem_union_left _ ha)) rfl
      (full_nodes_card G) (model_union G) (model_inter G) (model_rows_card G) hn hvis
    obtain ⟨S, hS, hdetS⟩ := seq_retained_of_model_deletion D.f D.e U G s hdet
    exact ⟨S, hS ▸ hs, hdetS⟩
  · have hc : G.C.card = 0 := by omega
    have hk : G.k = 0 := by omega
    let _ : IsEmpty G.C := Fintype.card_eq_zero_iff.mp (by simpa using hc)
    let _ : IsEmpty (Fin G.k) := Fintype.card_eq_zero_iff.mp (by simpa using hk)
    refine ⟨univ, ?_, ?_⟩
    · exact le_trans (Nat.sub_le _ _) (by rw [hc]; exact Nat.zero_le _)
    · rw [Matrix.det_isEmpty]
      exact one_ne_zero

theorem componentCount_range (n : ℕ) (hn : 0 < n) : NV.componentCount (Finset.range n) 1 = 1 := by
  unfold NV.componentCount
  rw [Finset.card_eq_one]
  refine ⟨n - 1, ?_⟩
  ext a
  simp only [NV.mem_stepEnds, Finset.mem_range, Finset.mem_singleton]
  omega

/-- The node set of a hybrid-shaped geometry is the interval `[0, r + 2k)`. -/
theorem hybrid_nodes_eq (G : Rect.Geometry) (r : ℕ) (hC : G.C = Finset.range r)
    (hx : ∀ i : Fin G.k, G.xs i = r + 2 * (i : ℕ)) (hy : ∀ i : Fin G.k, G.ys i = r + 2 * (i : ℕ) + 1) :
    G.C ∪ G.X' ∪ G.Y' = Finset.range (r + 2 * G.k) := by
  ext j
  simp only [Finset.mem_union, Finset.mem_range]
  constructor
  · rintro ((h | h) | h)
    · rw [hC, Finset.mem_range] at h; omega
    · have hmem : j ∈ Set.range G.xs := by
        have := Finset.range_orderEmbOfFin G.X' (rfl : G.X'.card = G.k)
        change j ∈ Set.range (G.X'.orderEmbOfFin rfl)
        rw [this]; exact h
      obtain ⟨i, rfl⟩ := hmem
      rw [hx]; have := i.2; omega
    · have hmem : j ∈ Set.range G.ys := by
        have := Finset.range_orderEmbOfFin G.Y' G.card_eq.symm
        change j ∈ Set.range (G.Y'.orderEmbOfFin G.card_eq.symm)
        rw [this]; exact h
      obtain ⟨i, rfl⟩ := hmem
      rw [hy]; have := i.2; omega
  · intro h
    by_cases hj : j < r
    · left; left; rw [hC, Finset.mem_range]; exact hj
    · by_cases hpar : (j - r) % 2 = 0
      · left; right
        have hi : (j - r) / 2 < G.k := by omega
        have := Finset.orderEmbOfFin_mem G.X' (rfl : G.X'.card = G.k) ⟨(j - r) / 2, hi⟩
        have e : G.xs ⟨(j - r) / 2, hi⟩ = j := by rw [hx]; simp; omega
        rw [← e]; exact this
      · right
        have hi : (j - r) / 2 < G.k := by omega
        have := Finset.orderEmbOfFin_mem G.Y' G.card_eq.symm ⟨(j - r) / 2, hi⟩
        have e : G.ys ⟨(j - r) / 2, hi⟩ = j := by rw [hy]; simp; omega
        rw [← e]; exact this

/-- **Theorem N** (S08): for the hybrid geometry (common nodes `[0, r)`, border nodes `r + 2i`, `r + 2i + 1`),
every `r ≥ max(1, d - 2)` and every rational `x`, some deletion of at most `⌊d/2⌋` common nodes leaves a
nonvanishing minor. -/
theorem support_nv0_even (D : Datum) (G : Rect.Geometry) (r : ℕ) (hr : max 1 (D.d - 2) ≤ r)
    (hC : G.C = Finset.range r)
    (hx : ∀ i : Fin G.k, G.xs i = r + 2 * (i : ℕ)) (hy : ∀ i : Fin G.k, G.ys i = r + 2 * (i : ℕ) + 1)
    (U : ℚ) :
    ∃ S : Finset G.C, G.C.card - S.card ≤ D.d / 2 ∧
      (seqFullN D.f D.e (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  have hZ := hybrid_nodes_eq G r hC hx hy
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr2 : D.d - 2 ≤ r := (le_max_right _ _).trans hr
  have hcard : G.C.card = r := by rw [hC, Finset.card_range]
  have hc1 : NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 = 1 := by
    rw [hZ]; exact componentCount_range _ (by omega)
  have hc2 : NV.componentCount G.C 1 = 1 := by
    rw [hC]; exact componentCount_range _ (by omega)
  obtain ⟨S, hS, hdet⟩ := datum_common_deletion D U G (by rw [hc1, hcard]; omega)
  refine ⟨S, ?_, hdet⟩
  rw [hc1, hc2] at hS
  have : (D.d + 1 + 1 - 2) / 2 = D.d / 2 := by congr 1
  omega

theorem pole_support_nv0_even (D : PoleDatum) (G : Rect.Geometry) (r : ℕ) (hr : max 1 (D.d - 2) ≤ r)
    (hC : G.C = Finset.range r)
    (hx : ∀ i : Fin G.k, G.xs i = r + 2 * (i : ℕ)) (hy : ∀ i : Fin G.k, G.ys i = r + 2 * (i : ℕ) + 1)
    (U : ℚ) :
    ∃ S : Finset G.C, G.C.card - S.card ≤ D.d / 2 ∧
      (seqFullN D.f D.e (fun a : S => ((a.1 : G.C) : ℕ)) G.xs G.ys U).det ≠ 0 := by
  have hZ := hybrid_nodes_eq G r hC hx hy
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr2 : D.d - 2 ≤ r := (le_max_right _ _).trans hr
  have hcard : G.C.card = r := by rw [hC, Finset.card_range]
  have hc1 : NV.componentCount (G.C ∪ G.X' ∪ G.Y') 1 = 1 := by
    rw [hZ]; exact componentCount_range _ (by omega)
  have hc2 : NV.componentCount G.C 1 = 1 := by
    rw [hC]; exact componentCount_range _ (by omega)
  obtain ⟨S, hS, hdet⟩ := pole_common_deletion D U G (by rw [hc1, hcard]; omega)
  refine ⟨S, ?_, hdet⟩
  rw [hc1, hc2] at hS
  have : (D.d + 1 + 1 - 2) / 2 = D.d / 2 := by congr 1
  omega

end TheoremN

/-! ### The adapter for the family (P211) -/

section Adapter

open CatalanCore.Uniform.Content.Wire

/-- **Nonvanishing at every even scale** (P211).  For a block geometry that is hybrid-shaped at every even
scale (such as `altGeom c`), the family `seqFamily D.f D.e` has, for every rational `x` and every
`s ≥ max(1, d)`, a member of scale `2s` with `Q(x) ≠ 0`, as soon as the depth budget is at least `⌊d/2⌋`. -/
theorem seqFamily_nv0_even (D : Datum) (B : BlockGeom) (const : ℝ) (depth : ℕ) (hdepth : D.d / 2 ≤ depth)
    (hyb : ∀ r, r % 2 = 0 → HybShape B r) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, (B.seqFamily D.f D.e const depth).Adm n ∧ SeqFamily.scale B.geometry n = 2 * s ∧
        (B.seqFamily D.f D.e const depth).evalQ n x ≠ 0 := by
  refine ⟨max 1 D.d, fun s hs x => ?_⟩
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsd : D.d ≤ s := (le_max_right _ _).trans hs
  have hh := hyb (2 * s) (by omega)
  obtain ⟨S, hS, hdet⟩ := support_nv0_even D (B.geometry (2 * s)) (2 * s)
    (by omega) hh.C_eq hh.xs_eq hh.ys_eq x
  refine ⟨⟨2 * s, S⟩, hS.trans hdepth, rfl, ?_⟩
  rw [SeqFamily.evalQ_poly]
  exact hdet

/-- The alternating geometry `altGeom c` is hybrid-shaped at every even scale, so the family
`seqFamily D.f D.e` of any datum has nonvanishing members at every large even scale. -/
theorem altGeom_seqFamily_nv0_even (D : Datum) (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (hdepth : D.d / 2 ≤ depth) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, ((Content.Shape.altGeom c hc).seqFamily D.f D.e const depth).Adm n ∧
        SeqFamily.scale (Content.Shape.altGeom c hc).geometry n = 2 * s ∧
        ((Content.Shape.altGeom c hc).seqFamily D.f D.e const depth).evalQ n x ≠ 0 :=
  seqFamily_nv0_even D (Content.Shape.altGeom c hc) const depth hdepth
    fun _ hr => Content.Shape.altGeom_hybShape c hc hr

theorem pole_seqFamily_nv0_even (D : PoleDatum) (B : BlockGeom) (const : ℝ) (depth : ℕ) (hdepth : D.d / 2 ≤ depth)
    (hyb : ∀ r, r % 2 = 0 → HybShape B r) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, (B.seqFamily D.f D.e const depth).Adm n ∧ SeqFamily.scale B.geometry n = 2 * s ∧
        (B.seqFamily D.f D.e const depth).evalQ n x ≠ 0 := by
  refine ⟨max 1 D.d, fun s hs x => ?_⟩
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsd : D.d ≤ s := (le_max_right _ _).trans hs
  have hh := hyb (2 * s) (by omega)
  obtain ⟨S, hS, hdet⟩ := pole_support_nv0_even D (B.geometry (2 * s)) (2 * s)
    (by omega) hh.C_eq hh.xs_eq hh.ys_eq x
  refine ⟨⟨2 * s, S⟩, hS.trans hdepth, rfl, ?_⟩
  rw [SeqFamily.evalQ_poly]
  exact hdet

/-- The alternating geometry `altGeom c` is hybrid-shaped at every even scale, so the family
`seqFamily D.f D.e` of any datum has nonvanishing members at every large even scale. -/
theorem pole_altGeom_seqFamily_nv0_even (D : PoleDatum) (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ)
    (hdepth : D.d / 2 ≤ depth) :
    ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, ((Content.Shape.altGeom c hc).seqFamily D.f D.e const depth).Adm n ∧
        SeqFamily.scale (Content.Shape.altGeom c hc).geometry n = 2 * s ∧
        ((Content.Shape.altGeom c hc).seqFamily D.f D.e const depth).evalQ n x ≠ 0 :=
  pole_seqFamily_nv0_even D (Content.Shape.altGeom c hc) const depth hdepth
    fun _ hr => Content.Shape.altGeom_hybShape c hc hr

end Adapter

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.support_nv0_even
#print axioms CatalanCore.Uniform.Support.altGeom_seqFamily_nv0_even
#print axioms CatalanCore.Uniform.Support.Datum.plane2_Apoly

#print axioms CatalanCore.Uniform.Support.PoleDatum.Apoly_natDegree_le
#print axioms CatalanCore.Uniform.Support.pole_altGeom_seqFamily_nv0_even
