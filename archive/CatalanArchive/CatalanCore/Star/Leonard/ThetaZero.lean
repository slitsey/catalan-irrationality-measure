module

public import CatalanCore.Star.Defs
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The `θ → 0` specialisation (continuity route)

Every identity of the Leonard theory holds for generic `θ` (here: all non-integer rationals).
`kgenCore` is continuous at `θ = 0` over `ℚ` as soon as all columns are `w_j` with `j ≥ 1`
and `det(W_Xᵀ W_Y)(0) ≠ 0`; hence an identity `kgen θ = F θ` valid for all non-integer `θ`
with `F` continuous at `0` also holds at `θ = 0`.
-/

@[expose] public section

open Finset Matrix Filter Topology

namespace CatalanCore.Star

variable {K m : ℕ}

lemma cA_wcol (j : ℤ) (hj : 1 ≤ j) : ContinuousAt (fun θ : ℚ => wcol K θ j) 0 := by
  refine continuousAt_pi.2 fun a => ?_
  unfold wcol
  have h1 : (1 : ℚ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℚ) ≤ ((a : ℕ) : ℚ) := Nat.cast_nonneg _
  exact continuousAt_const.div (by fun_prop) (ne_of_gt (by show (0 : ℚ) < 0 + ((a : ℕ) : ℚ) + (j : ℚ); linarith))

lemma cA_Wb (b : Fin m → ℤ) (hb : ∀ i, 1 ≤ b i) : ContinuousAt (fun θ : ℚ => Wb K θ b) 0 := by
  refine continuousAt_pi.2 fun a => continuousAt_pi.2 fun i => ?_
  exact (continuousAt_pi.1 (cA_wcol (K := K) (b i) (hb i))) a

section Cont

variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]

lemma cA_mmul {f : ℚ → Matrix n p ℚ} {g : ℚ → Matrix p q ℚ} {x : ℚ}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun y => f y * g y) x :=
  (((continuous_fst.matrix_mul continuous_snd :
    Continuous fun r : Matrix n p ℚ × Matrix p q ℚ => r.1 * r.2)).continuousAt).comp
      (hf.prodMk hg)

lemma cA_transpose {f : ℚ → Matrix n p ℚ} {x : ℚ} (hf : ContinuousAt f x) :
    ContinuousAt (fun y => (f y)ᵀ) x :=
  ((continuous_id.matrix_transpose : Continuous fun A : Matrix n p ℚ => Aᵀ).continuousAt).comp hf

lemma cA_vecMul {f : ℚ → n → ℚ} {g : ℚ → Matrix n p ℚ} {x : ℚ}
    (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun y => f y ᵥ* g y) x :=
  (((continuous_fst.matrix_vecMul continuous_snd :
    Continuous fun r : (n → ℚ) × Matrix n p ℚ => r.1 ᵥ* r.2)).continuousAt).comp (hf.prodMk hg)

lemma cA_inv {f : ℚ → Matrix n n ℚ} {x : ℚ} (hf : ContinuousAt f x) (hd : (f x).det ≠ 0) :
    ContinuousAt (fun y => (f y)⁻¹) x := by
  have h1 : ContinuousAt (fun A : Matrix n n ℚ => A⁻¹) (f x) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hd
  exact h1.comp hf

lemma cA_det {f : ℚ → Matrix n n ℚ} {x : ℚ} (hf : ContinuousAt f x) :
    ContinuousAt (fun y => (f y).det) x :=
  ((continuous_id.matrix_det : Continuous fun A : Matrix n n ℚ => A.det).continuousAt).comp hf

end Cont

lemma cA_Nmat (J : Finset ℤ) (hJ : ∀ j ∈ J, 1 ≤ j) :
    ContinuousAt (fun θ : ℚ => Nmat K θ J) 0 := by
  unfold Nmat
  have : ContinuousAt (fun θ : ℚ => ∑ j ∈ J, Matrix.vecMulVec (wcol K θ j) (wcol K θ j)) 0 := by
    apply tendsto_finset_sum
    intro j hj
    have hw := cA_wcol (K := K) j (hJ j hj)
    exact (continuousAt_pi.2 fun a => continuousAt_pi.2 fun b =>
      (continuousAt_pi.1 hw a).mul (continuousAt_pi.1 hw b))
  exact this

lemma cA_projB (bx by' : Fin m → ℤ) (hbx : ∀ i, 1 ≤ bx i) (hby : ∀ i, 1 ≤ by' i)
    (hΔ : ((Wb K (0 : ℚ) bx)ᵀ * Wb K (0 : ℚ) by').det ≠ 0) :
    ContinuousAt (fun θ : ℚ => projB K θ bx by') 0 := by
  unfold projB
  have hX := cA_Wb (K := K) bx hbx
  have hY := cA_Wb (K := K) by' hby
  have hG := cA_mmul (cA_transpose hX) hY
  have hI := cA_inv hG hΔ
  have := cA_mmul (cA_mmul hY hI) (cA_transpose hX)
  exact continuousAt_const.sub this

lemma c_ubasis (n : ℕ) (bx : Fin m → ℤ) : Continuous (fun θ : ℚ => ubasis K n θ bx) := by
  refine continuous_pi fun a => continuous_pi fun i => ?_
  unfold ubasis piB
  fun_prop

/-- `kgenCore` is continuous at `θ = 0` (over `ℚ`) when all columns have index `≥ 1` and the
border determinant does not vanish at `0`. -/
theorem cA_kgenCore (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) (hS : 1 ≤ S)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hbx : ∀ i, 1 ≤ bx i) (hby : ∀ i, 1 ≤ by' i)
    (hΔ : ((Wb K (0 : ℚ) bx)ᵀ * Wb K (0 : ℚ) by').det ≠ 0) :
    ContinuousAt (fun θ : ℚ => kgenCore K m θ J S bx by') 0 := by
  unfold kgenCore
  apply cA_det
  refine continuousAt_pi.2 fun k => continuousAt_pi.2 fun i => ?_
  have hw := cA_wcol (K := K) S hS
  have hPN := cA_mmul (cA_projB bx by' hbx hby hΔ) (cA_Nmat J hJ)
  have hpow : ContinuousAt (fun θ : ℚ => (projB K θ bx by' * Nmat K θ J) ^ (k : ℕ)) 0 :=
    hPN.pow (k : ℕ)
  have := cA_vecMul (cA_vecMul hw hpow) (c_ubasis (K - m) bx).continuousAt
  exact continuousAt_pi.1 this i

/-- rationals `0 < θ < 1` are generic -/
lemma gen_of_small {θ : ℚ} (h0 : 0 < θ) (h1 : θ < 1) (z : ℤ) : θ + (z : ℚ) ≠ 0 := by
  intro h
  have h2 : (z : ℚ) < 0 := by linarith
  have h3 : (-1 : ℚ) < (z : ℚ) := by linarith
  have h2' : z < 0 := by exact_mod_cast h2
  have h3' : (-1 : ℤ) < z := by exact_mod_cast h3
  omega

lemma tendsto_inv_succ_Q : Tendsto (fun n : ℕ => (1 : ℚ) / ((n : ℚ) + 1)) atTop (𝓝 0) := by
  rw [Rat.isEmbedding_coe_real.tendsto_nhds_iff]
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa [Function.comp_def] using this

/-- **`θ → 0`.**  An identity `kgenCore θ = Fn θ` valid for all rationals `0 < θ < 1`, with `Fn`
continuous at `0`, holds at `θ = 0`. -/
theorem kgenCore_zero_of_generic (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) (hS : 1 ≤ S)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hbx : ∀ i, 1 ≤ bx i) (hby : ∀ i, 1 ≤ by' i)
    (hΔ : ((Wb K (0 : ℚ) bx)ᵀ * Wb K (0 : ℚ) by').det ≠ 0)
    (Fn : ℚ → ℚ) (hF : ContinuousAt Fn 0)
    (heq : ∀ θ : ℚ, 0 < θ → θ < 1 → kgenCore K m θ J S bx by' = Fn θ) :
    kgenCore K m (0 : ℚ) J S bx by' = Fn 0 := by
  have hc := cA_kgenCore (K := K) (m := m) J S bx by' hS hJ hbx hby hΔ
  have hu := tendsto_inv_succ_Q
  have t1 : Tendsto (fun n : ℕ => kgenCore K m ((1 : ℚ) / ((n : ℚ) + 1)) J S bx by') atTop
      (𝓝 (kgenCore K m (0 : ℚ) J S bx by')) := hc.tendsto.comp hu
  have t2 : Tendsto (fun n : ℕ => Fn ((1 : ℚ) / ((n : ℚ) + 1))) atTop (𝓝 (Fn 0)) :=
    hF.tendsto.comp hu
  have hev : (fun n : ℕ => kgenCore K m ((1 : ℚ) / ((n : ℚ) + 1)) J S bx by') =ᶠ[atTop]
      (fun n : ℕ => Fn ((1 : ℚ) / ((n : ℚ) + 1))) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    apply heq
    · positivity
    · rw [div_lt_one (by positivity)]
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      linarith
  exact tendsto_nhds_unique (t1.congr' hev) t2

end CatalanCore.Star
