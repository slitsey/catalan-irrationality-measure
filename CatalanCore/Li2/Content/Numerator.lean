module

public import CatalanCore.Li2.Content.Moments
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P042
public import CatalanCore.Li2.Port.Unified.Modular.Base.DecayExpand
public import CatalanCore.Li2.Port.Unified.Modular.Positive.Packed.P002

@[expose] public section

/-! Numerator-prime simple-pole factorization, valuation bounds and rate, A1-A6. -/
open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port
open CatalanCore.Li2.Port.Unified

namespace CatalanCore.Li2.Content
open Port.Unified.Proofs.Arithmetic

abbrev simpleSlot (n : ℕ) := Fin (2 * n) ⊕ Fin (4 * n)
instance simpleSlotFintype (n : ℕ) : Fintype (simpleSlot n) :=
  inferInstanceAs (Fintype (Fin (2 * n) ⊕ Fin (4 * n)))
instance simpleSlotDecidableEq (n : ℕ) : DecidableEq (simpleSlot n) :=
  inferInstanceAs (DecidableEq (Fin (2 * n) ⊕ Fin (4 * n)))

noncomputable def simpleW (z : ℚ) (n : ℕ) : Matrix (Fin (2 * n)) (simpleSlot n) ℚ[X]
  | a, Sum.inl i => C (Li2.parameterU z (Li2.gramNum n a.val i.val /ₘ Li2.D (4 * n)))
  | a, Sum.inr j =>
    C (Li2.gramRes n 0 0 (j.val + 1) *
      (Li2.binomPoly a.val).eval (-((j.val + 1 : ℕ) : ℚ)) *
      ((j.val + 1 : ℕ) : ℚ) * z⁻¹ ^ (j.val + 1)) *
      (X - C (Li2.parameterTau z (j.val + 1)))

noncomputable def simpleC (n : ℕ) : Matrix (simpleSlot n) (Fin (2 * n)) ℚ[X]
  | Sum.inl i, b => if i = b then 1 else 0
  | Sum.inr j, b => C ((Li2.binomPoly b.val).eval (-((j.val + 1 : ℕ) : ℚ)))

def simpleRank (n : ℕ) : simpleSlot n → ℕ
  | Sum.inl i => 4 * n + i.val
  | Sum.inr j => 4 * n - (j.val + 1)

def thetaA (p n : ℕ) (a : ℚ) (t : ℕ) : ℚ :=
  -2 * L p n - a * ((4 * n - t : ℕ) : ℚ)

def omegaA (p n : ℕ) (a : ℚ) : simpleSlot n → ℚ
  | Sum.inl _ => -2 * L p n
  | Sum.inr j => -2 * L p n - a * ((j.val + 1 : ℕ) : ℚ)


private theorem sum_even_rat (k : ℕ) :
    (∑ i ∈ Finset.range k, 2 * (i : ℚ)) = (k : ℚ) * ((k : ℚ) - 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private lemma gramResFactorDraft (n a b j : ℕ) :
    Port.Li2.gramRes n a b j = Port.Li2.gramRes n 0 0 j *
      (Port.Li2.binomPoly a).eval (-(j : ℚ)) * (Port.Li2.binomPoly b).eval (-(j : ℚ)) := by
  simp only [Port.Li2.gramRes, Port.Li2.gramNum, Port.Li2.binomPoly_zero,
    eval_mul, eval_C, eval_one]
  ring

theorem gramRes_factor (p : ℕ) [Fact p.Prime] (n a b j : ℕ)
    (hj : 1 ≤ j) (hjn : j ≤ 4 * n) :
    Port.Li2.gramRes n a b j = Port.Li2.gramRes n 0 0 j *
      (Port.Li2.binomPoly a).eval (-(j : ℚ)) * (Port.Li2.binomPoly b).eval (-(j : ℚ)) ∧
    Port.Li2.VG p (Port.Li2.gramRes n 0 0 j) 0 := by
  exact ⟨gramResFactorDraft n a b j, Port.Li2.gramRes_VG p n 0 0 hj hjn⟩

theorem binomGram_eq_mul_simple (z : ℚ) (n : ℕ) :
    ParameterFamily.binomGram z n = simpleW z n * simpleC n := by
  classical
  apply Matrix.ext
  intro i j
  change ParameterFamily.numeratorFunctional z (4*n) (Port.Li2.gramNum n i.val j.val) = _
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [simpleW, simpleC, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold ParameterFamily.numeratorFunctional
  congr 1
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  rw [Fin.sum_univ_eq_sum_range (fun k =>
    C (Port.Li2.gramRes n 0 0 (k+1) * (Port.Li2.binomPoly i.val).eval (-((k+1:ℕ):ℚ)) *
      ((k+1:ℕ):ℚ) * z⁻¹ ^ (k+1)) *
      (X - C (Port.Li2.parameterTau z (k+1))) *
      C ((Port.Li2.binomPoly j.val).eval (-((k+1:ℕ):ℚ))))]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Nat.add_comm 1 k]
  change C (Port.Li2.gramRes n i.val j.val (k+1)) *
    (C (((k+1:ℕ):ℚ) * z⁻¹ ^ (k+1)) * (X - C (Port.Li2.parameterTau z (k+1)))) = _
  rw [gramResFactorDraft]
  simp only [map_mul]
  ring

theorem simpleSlot_bounds (p : ℕ) [Fact p.Prime] (z a : ℚ)
    (ha : 0 ≤ a) (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hr : Port.Li2.VG p (z / (1 - z)) 0) (hz : Port.Li2.VG p z 0)
    (hzinv : Port.Li2.VG p z⁻¹ (-a)) {n : ℕ} (hn : 1 ≤ n) :
    (∀ i x, Port.Li2.GV p (simpleW z n i x) (omegaA p n a x)) ∧
    (∀ x j, Port.Li2.GV p (simpleC n x j) 0) := by
  have hL0 : 0 ≤ L p n := Nat.cast_nonneg _
  constructor
  · intro i x
    rcases x with k | j
    · apply Apery.GV.C
      simpa only [omegaA, zero_mul, mul_zero, sub_zero] using
        gramU_entry_VG_f p z 0 h1 (le_refl 0) hr hn i.isLt k.isLt
    · change Apery.GV p
        (C (Port.Li2.gramRes n 0 0 (j.val + 1) *
          (Port.Li2.binomPoly i.val).eval (-((j.val + 1 : ℕ) : ℚ)) *
          ((j.val + 1 : ℕ) : ℚ) * z⁻¹ ^ (j.val + 1)) *
          (X - C (Port.Li2.parameterTau z (j.val + 1)))) _
      have hres := Port.Li2.gramRes_VG p n 0 0 (by omega : 1 ≤ j.val+1)
        (by have h := j.isLt; omega : j.val+1 ≤ 4*n)
      have hbin : Apery.VG p ((Port.Li2.binomPoly i.val).eval (-((j.val+1:ℕ):ℚ))) 0 := by
        simpa only [Int.cast_neg, Int.cast_natCast] using
          Port.Li2.binomPoly_eval_int_VG p i.val (-((j.val+1:ℕ):ℤ))
      have hc := ((hres.mul hbin).mul (Apery.VG.natCast (p := p) (j.val+1))).mul
        (hzinv.pow (j.val+1))
      have ht : Apery.VG p (Port.Li2.parameterTau z (j.val+1)) (-2 * L p n) :=
        parameterTau_VG_log p z hz (by have h := j.isLt; omega : j.val+1 ≤ 7*n-2)
      have hlin : Apery.GV p (X - C (Port.Li2.parameterTau z (j.val+1))) (-2 * L p n) :=
        (Apery.GV.X.mono (by linarith)).sub (Apery.GV.C ht)
      refine ((Apery.GV.C hc).mul hlin).mono (le_of_eq ?_)
      dsimp [omegaA]
      ring
  · intro x j
    rcases x with i | k
    · dsimp [simpleC]
      split_ifs
      · exact Apery.GV.C Apery.VG.one
      · exact Apery.GV.zero _
    · apply Apery.GV.C
      simpa only [Int.cast_neg, Int.cast_natCast] using
        Port.Li2.binomPoly_eval_int_VG p j.val (-((k.val+1:ℕ):ℤ))

theorem simpleRank_weights (p n : ℕ) (a : ℚ) (ha : 0 ≤ a) :
    Function.Injective (simpleRank n) ∧ Monotone (thetaA p n a) ∧
    (∀ x, thetaA p n a (simpleRank n x) ≤ omegaA p n a x) ∧
    (∑ t ∈ Finset.range (2 * n), thetaA p n a t) =
      -4 * n * L p n - a * (6 * (n : ℚ) ^ 2 + n) := by
  have hinj : Function.Injective (simpleRank n) := by
    intro x y h
    rcases x with i | k <;> rcases y with j | l <;> simp only [simpleRank] at h
    · exact congrArg Sum.inl (Fin.ext (by omega))
    · have hl := l.isLt
      omega
    · have hk := k.isLt
      omega
    · have hk := k.isLt
      have hl := l.isLt
      exact congrArg Sum.inr (Fin.ext (by omega))
  have hmono : Monotone (thetaA p n a) := by
    intro i j hij
    have hd : 4*n-j ≤ 4*n-i := by omega
    have hdq : ((4*n-j : ℕ) : ℚ) ≤ ((4*n-i : ℕ) : ℚ) := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_left hdq ha
    dsimp [thetaA]
    linarith
  have hweights : ∀ x, thetaA p n a (simpleRank n x) ≤ omegaA p n a x := by
    intro x
    rcases x with i | j
    · have hs : 4*n-(4*n+i.val) = 0 := by omega
      simp only [simpleRank, thetaA, omegaA, hs, Nat.cast_zero, mul_zero, sub_zero]
      exact le_rfl
    · have hs : 4*n-(4*n-(j.val+1)) = j.val+1 := by have h := j.isLt; omega
      simp only [simpleRank, thetaA, omegaA, hs]
      exact le_rfl
  refine ⟨hinj, hmono, hweights, ?_⟩
  have hterm : ∀ t ∈ Finset.range (2*n), thetaA p n a t =
      -2 * L p n - a * (4 * (n : ℚ) - t) := by
    intro t ht
    dsimp [thetaA]
    rw [Nat.cast_sub (by have h := Finset.mem_range.mp ht; omega)]
    push_cast
    rfl
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have h2 := sum_even_rat (2*n)
  rw [← Finset.mul_sum] at h2
  push_cast at h2 ⊢
  have hid : (∑ t ∈ Finset.range (2*n), (t : ℚ)) = 2 * (n : ℚ) ^ 2 - n := by nlinarith
  rw [hid]
  ring

theorem Qtilde_GV_num (p : ℕ) [Fact p.Prime] (z a : ℚ)
    (ha : 0 ≤ a) (h0 : z ≠ 0) (h1 : z ≠ 1)
    (hr : Port.Li2.VG p (z / (1 - z)) 0) (hz : Port.Li2.VG p z 0)
    (hzinv : Port.Li2.VG p z⁻¹ (-a)) {n : ℕ} (hn : 1 ≤ n) :
    Port.Li2.GV p (ParameterFamily.Qtilde z n)
      (-a * (6 * (n : ℚ) ^ 2 + n) - 4 * n * L p n) := by
  obtain ⟨hW, hC⟩ := simpleSlot_bounds p z a ha h0 h1 hr hz hzinv hn
  obtain ⟨hinj, hmono, hweights, hsum⟩ := simpleRank_weights p n a ha
  have heq : -a * (6 * (n : ℚ) ^ 2 + n) - 4 * n * L p n =
      ∑ t ∈ Finset.range (2*n), thetaA p n a t := by rw [hsum]; ring
  rw [heq, ParameterFamily.Qtilde_eq_binomGram_det, binomGram_eq_mul_simple]
  apply Port.Li2.det_mul_GV p (simpleW z n) (simpleC n)
    (omegaA p n a) (fun _ => 0) hW hC
  intro f hf
  calc
    ∑ t ∈ Finset.range (2*n), thetaA p n a t
        ≤ ∑ b, thetaA p n a (simpleRank n (f b)) :=
      Port.Li2.sum_range_le_of_injective (thetaA p n a) hmono
        (fun b => simpleRank n (f b)) (hinj.comp hf)
    _ ≤ ∑ b, (omegaA p n a (f b) + 0) :=
      Finset.sum_le_sum fun b _ => by simpa using hweights (f b)

theorem numerator_rate (a : ℝ) :
    Tendsto (fun n : ℕ => -a * (6 * (n : ℝ) ^ 2 + n) / (n : ℝ) ^ 2)
      atTop (𝓝 (-6 * a)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => -a * (6 + (n : ℝ)⁻¹))
      atTop (𝓝 (-6 * a)) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.add hi) using 1 <;> ring
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  <;> ring

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.gramRes_factor
#print axioms CatalanCore.Li2.Content.binomGram_eq_mul_simple
#print axioms CatalanCore.Li2.Content.simpleSlot_bounds
#print axioms CatalanCore.Li2.Content.simpleRank_weights
#print axioms CatalanCore.Li2.Content.Qtilde_GV_num
#print axioms CatalanCore.Li2.Content.numerator_rate
