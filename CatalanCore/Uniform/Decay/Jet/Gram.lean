module

public import CatalanCore.Uniform.Decay.Polygon.Source
public import CatalanCore.Uniform.Support.Datum
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Fin.Rev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent

@[expose] public section

/-!
# The Gram formula for jets: double heads (lane H, wave H2; ledger S14)

`F(z) = ∑_s [a_s ψ(z+s) + b_s ψ'(z+s)]`, `∑ a_s = 0` (`SUPPORT-THEOREM` §6).  A `JetFrame` is a `Frame`
(the simple part `a = w`) with integer double weights `b`.

* `TentJ x y = Tent x y + TentB x y` is the Loewner entry `Φ(ξ)[x,y]/norm`, with `f_t = ∑_{k<t} δ(k)`,
  `e_t = -∑_{k<t} δ'(k)`, `ξ = F'(0)`; the double part has `δ_b(z) = -b/(z+s)²` (`DeltaB`),
  `ξ_b = -2 b ζ(3, s)` (`constB`).
* `EJ = E_a + E_b`, `E_a = -π ∑ a cot π(z+s)` (the `Frame` one), `E_b = π² ∑ b / sin² π(z+s)`.
* **Lemma 6.2** (`gram_formula`): for `k(z) = 1/((z-x)(z-y))`, `x, y ∈ ℕ`, every upper polygon `Γ`,
  `norm · Φ[x,y] = ∑_{heads} (a k - b k')(x_{s,n}) + (2πi)⁻¹ ∫_Γ k E dz`, with the heads the poles
  `-s-n` right of the vertex `x*`.
* **Lemma 6.3** (`rank_one_split`): at a double head the term `-b (ac)' + a_s a c` is a difference of
  two rank-one terms.

**Proof, no new contour calculus.**  The simple part is the `Frame` identity (`Frame.contour_identity`).
For `E_b = ∑_n ∑_i b_i/(z+n+s_i)²` the reference-ray identity is proved as for `E_a`, termwise: the ray
integral of one double pole against `k` is `-2πi k'(p)` for `p` left of `x*` (`contL_dbl`, from the
existing `contL_S21`, two simple poles `a ≠ b` or one double node `a = b`), the sum over `n` is
interchanged by dominated convergence, and the two reference rays are deformed to the polygon by the
generic `Polygon.deform` for the sum `E_a + E_b` (holomorphic off the poles, `K/(Im z)²` decay).
-/

open MeasureTheory Set Filter Topology Complex Finset
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos norm_inv_rayPt_le integrableOn_ray2
  integrableOn_ray3 integrableOn_invsq rayPt_sub_ne contL_S21 contL_logsum rayI_pow2 rayI_add_smul)

namespace CatalanCore.Uniform.Decay.Jet

/-- A jet frame: a `Frame` (simple weights `a = w`, balance `∑ a = 0`) with integer double weights `b`. -/
structure JetFrame extends CatalanCore.Frame where
  /-- double-pole weights -/
  b : Fin d → ℤ

namespace JetFrame

variable (JF : JetFrame)

/-! ### The double part of the Loewner matrix -/

/-- `F_b(k) - F_b(k-1) = -∑ b_i / (k-1+μ_i)²`. -/
def DeltaB (k : ℕ) : ℚ := -∑ i, (JF.b i : ℚ) / ((k : ℚ) - 1 + JF.μ i) ^ 2

/-- `F_b'(k-1) - F_b'(k) = -2 ∑ b_i / (k-1+μ_i)³`. -/
def DsqB (k : ℕ) : ℚ := -2 * ∑ i, (JF.b i : ℚ) / ((k : ℚ) - 1 + JF.μ i) ^ 3

/-- The Loewner entry of `F_b` on natural nodes (as `Frame.Mn`). -/
def MnB (x y : ℕ) : ℚ :=
  if x = y then -(1 / JF.norm) * ∑ k ∈ Icc 1 x, JF.DsqB k
  else (1 / JF.norm) * (1 / (((max x y : ℕ) : ℚ) - ((min x y : ℕ) : ℚ))) *
    ∑ k ∈ Ioc (min x y) (max x y), JF.DeltaB k

/-- `∑_{n ≥ 0} 1/(n+μ)³`. -/
noncomputable def hurwitzTail3 (μ : ℚ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + (μ : ℝ)) ^ 3

/-- `F_b'(0)/norm = -2 ∑ b_i ζ(3, μ_i) / norm`. -/
noncomputable def constB : ℝ :=
  (∑ i, (JF.b i : ℝ) * (-2 * hurwitzTail3 (JF.μ i))) / (JF.norm : ℝ)

noncomputable def TentB (x y : ℕ) : ℝ := (if x = y then JF.constB else 0) + (JF.MnB x y : ℝ)

/-- The Loewner entry of the whole jet, `Φ(ξ)[x,y] / norm`. -/
noncomputable def TentJ (x y : ℕ) : ℝ := JF.toFrame.Tent x y + JF.TentB x y

/-! ### Atoms, heads and tails of the double part -/

/-- The atom of the double part at `t`: `-b_i k'(-t-μ_i)` with `k = 1/((z-x)(z-y))`. -/
noncomputable def atomB (i : Fin JF.d) (x y : ℕ) (t : ℝ) : ℝ :=
  -(JF.b i : ℝ) * ((x : ℝ) + y + 2 * t + 2 * (JF.μ i : ℝ)) /
    (((x : ℝ) + t + JF.μ i) ^ 2 * ((y : ℝ) + t + JF.μ i) ^ 2)

noncomputable def atomBSum (x y m : ℕ) : ℝ := ∑ i, JF.atomB i x y (m : ℝ)

noncomputable def tailTermB (N0 x y : ℕ) (t : ℝ) : ℝ :=
  ∑ i, if (N0 : ℝ) + (JF.xs : ℝ) < t + (JF.μ i : ℝ) then JF.atomB i x y t else 0

noncomputable def headTermB (N0 x y : ℕ) (t : ℝ) : ℝ :=
  ∑ i, if (N0 : ℝ) + (JF.xs : ℝ) < t + (JF.μ i : ℝ) then 0 else JF.atomB i x y t

noncomputable def atomHeadB (N0 x y : ℕ) : ℝ :=
  ∑ m ∈ range (N0 + ⌈(JF.xs : ℝ)⌉₊), JF.headTermB N0 x y (m : ℝ)

lemma mu_pos (i : Fin JF.d) : (0 : ℝ) < (JF.μ i : ℝ) := JF.toFrame.mu_pos i

lemma summable_inv_cube_add (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + c) ^ 3 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((CatalanCore.Frame.summable_inv_sq_add' c hc).mul_left (1 / c))
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : c ≤ (n : ℝ) + c := by linarith
  have h2 : 0 < (n : ℝ) + c := by linarith
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (n + c) ^ 3 = (n + c) * (n + c) ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg ((n : ℝ) + c)]


/-! ### Part B1: `norm · TentB = ∑' atomBSum` -/

lemma atomB_comm (i : Fin JF.d) (x y : ℕ) (t : ℝ) : JF.atomB i x y t = JF.atomB i y x t := by
  unfold atomB; ring

lemma atomBSum_comm (x y m : ℕ) : JF.atomBSum x y m = JF.atomBSum y x m := by
  unfold atomBSum; exact Finset.sum_congr rfl (fun i _ => atomB_comm JF i x y _)

lemma MnB_comm (x y : ℕ) : JF.MnB x y = JF.MnB y x := by
  unfold MnB
  by_cases h : x = y
  · subst h; rfl
  · have h' : y ≠ x := Ne.symm h
    rw [if_neg h, if_neg h', max_comm, min_comm]

lemma sum_Icc_shift' {M : Type*} [AddCommMonoid M] (g : ℕ → M) (a : ℕ) :
    ∑ k ∈ Icc 1 a, g k = ∑ n ∈ range a, g (n + 1) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_Ioc_shift' {M : Type*} [AddCommMonoid M] (a : ℕ) (g : ℕ → M) (n : ℕ) :
    ∑ k ∈ Ioc a (a + n), g k = ∑ j ∈ range n, g (a + j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `g_b(w) = ∑ b_i / (w + μ_i)²`. -/
noncomputable def gB2 (w : ℝ) : ℝ := ∑ i, (JF.b i : ℝ) / (w + (JF.μ i : ℝ)) ^ 2

lemma summable_gB2 (x : ℕ) : Summable (fun m : ℕ => JF.gB2 ((x : ℝ) + m)) := by
  unfold gB2
  refine summable_sum (fun i _ => ?_)
  have hS := (CatalanCore.Frame.summable_inv_sq_add' ((x : ℝ) + JF.μ i)
    (by have := JF.mu_pos i; positivity)).mul_left (JF.b i : ℝ)
  refine hS.congr (fun m => ?_)
  rw [show ((m : ℝ) + ((x : ℝ) + JF.μ i)) = (x : ℝ) + m + JF.μ i by ring]
  ring

lemma atomBSum_offdiag (x c m : ℕ) (hc : 0 < c) :
    JF.atomBSum x (x + c) m =
      -(1 / (c : ℝ)) * (JF.gB2 ((x : ℝ) + m) - JF.gB2 ((x : ℝ) + m + c)) := by
  unfold atomBSum atomB gB2
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hμ := JF.mu_pos i
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have p1 : (x : ℝ) + m + JF.μ i ≠ 0 := by positivity
  have p2 : (x : ℝ) + m + c + JF.μ i ≠ 0 := by positivity
  push_cast
  rw [show ((x : ℝ) + c + m + JF.μ i) = (x : ℝ) + m + c + JF.μ i by ring]
  field_simp
  ring

theorem norm_mul_TentB (x y : ℕ) :
    (JF.norm : ℝ) * JF.TentB x y = ∑' m : ℕ, JF.atomBSum x y m := by
  have hn : (JF.norm : ℝ) ≠ 0 := by exact_mod_cast JF.hnorm.ne'
  by_cases hxy : x = y
  · subst hxy
    unfold TentB
    rw [if_pos rfl]
    have hMnQ : JF.MnB x x = -(1 / JF.norm) *
        ∑ n ∈ range x, -2 * ∑ i, (JF.b i : ℚ) / ((n : ℚ) + JF.μ i) ^ 3 := by
      unfold MnB
      rw [if_pos rfl, sum_Icc_shift']
      congr 1
      refine Finset.sum_congr rfl (fun n _ => ?_)
      unfold DsqB
      push_cast
      simp
    have hMn : (JF.MnB x x : ℝ) = -(1 / (JF.norm : ℝ)) *
        ∑ n ∈ range x, -2 * ∑ i, (JF.b i : ℝ) / ((n : ℝ) + JF.μ i) ^ 3 := by
      rw [hMnQ]; push_cast; rfl
    rw [hMn]
    have hS : ∀ i : Fin JF.d, Summable (fun m : ℕ => 1 / ((m : ℝ) + ((x : ℝ) + JF.μ i)) ^ 3) :=
      fun i => summable_inv_cube_add _ (by have := JF.mu_pos i; positivity)
    have hat : ∑' m : ℕ, JF.atomBSum x x m =
        ∑ i, (JF.b i : ℝ) * (-2 * ∑' m : ℕ, 1 / ((m : ℝ) + ((x : ℝ) + JF.μ i)) ^ 3) := by
      unfold atomBSum atomB
      rw [Summable.tsum_finsetSum (fun i _ => by
        have := ((hS i).mul_left ((JF.b i : ℝ) * (-2)))
        refine this.congr (fun m => ?_)
        have hμ := JF.mu_pos i
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
        have p1 : (x : ℝ) + m + JF.μ i ≠ 0 := by positivity
        rw [show ((m : ℝ) + ((x : ℝ) + JF.μ i)) = (x : ℝ) + m + JF.μ i by ring]
        field_simp
        ring)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← tsum_mul_left, ← tsum_mul_left]
      refine tsum_congr (fun m => ?_)
      have hμ := JF.mu_pos i
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
      have p1 : (x : ℝ) + m + JF.μ i ≠ 0 := by positivity
      rw [show ((m : ℝ) + ((x : ℝ) + JF.μ i)) = (x : ℝ) + m + JF.μ i by ring]
      field_simp
      ring
    rw [hat]
    have hz : ∀ i : Fin JF.d, hurwitzTail3 (JF.μ i) =
        ∑ n ∈ range x, 1 / ((n : ℝ) + (JF.μ i : ℝ)) ^ 3
          + ∑' m : ℕ, 1 / ((m : ℝ) + ((x : ℝ) + JF.μ i)) ^ 3 := by
      intro i
      have h := (summable_inv_cube_add (JF.μ i : ℝ) (JF.mu_pos i)).sum_add_tsum_nat_add x
      unfold hurwitzTail3
      rw [← h]
      congr 1
      refine tsum_congr (fun m => ?_)
      push_cast; ring_nf
    unfold constB
    have e1 : (JF.norm : ℝ) * ((∑ i, (JF.b i : ℝ) * (-2 * hurwitzTail3 (JF.μ i))) / (JF.norm : ℝ)
        + -(1 / (JF.norm : ℝ)) * ∑ n ∈ range x, -2 * ∑ i, (JF.b i : ℝ) / ((n : ℝ) + JF.μ i) ^ 3)
        = (∑ i, (JF.b i : ℝ) * (-2 * hurwitzTail3 (JF.μ i)))
          + 2 * ∑ n ∈ range x, ∑ i, (JF.b i : ℝ) / ((n : ℝ) + JF.μ i) ^ 3 := by
      field_simp
      rw [Finset.mul_sum]
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring
    rw [e1, Finset.sum_comm]
    have e2 : ∑ i, (JF.b i : ℝ) * (-2 * hurwitzTail3 (JF.μ i)) =
        ∑ i, (JF.b i : ℝ) * (-2 * ∑ n ∈ range x, 1 / ((n : ℝ) + (JF.μ i : ℝ)) ^ 3)
        + ∑ i, (JF.b i : ℝ) * (-2 * ∑' m : ℕ, 1 / ((m : ℝ) + ((x : ℝ) + JF.μ i)) ^ 3) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hz i]; ring
    rw [e2]
    have e3 : ∑ i, ∑ n ∈ range x, (JF.b i : ℝ) / ((n : ℝ) + JF.μ i) ^ 3 =
        ∑ i, (JF.b i : ℝ) * ∑ n ∈ range x, 1 / ((n : ℝ) + (JF.μ i : ℝ)) ^ 3 := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      ring
    rw [e3]
    have e4 : ∑ i, (JF.b i : ℝ) * (-2 * ∑ n ∈ range x, 1 / ((n : ℝ) + (JF.μ i : ℝ)) ^ 3)
        = -(2 * ∑ i, (JF.b i : ℝ) * ∑ n ∈ range x, 1 / ((n : ℝ) + (JF.μ i : ℝ)) ^ 3) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [e4]; ring
  · wlog hlt : x < y generalizing x y
    · have hyx : y < x := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hxy)
      have := this y x (Ne.symm hxy) hyx
      unfold TentB at this ⊢
      rw [if_neg hxy, JF.MnB_comm x y]
      rw [if_neg (Ne.symm hxy)] at this
      simp only [atomBSum_comm JF x y] at *
      exact this
    · unfold TentB
      rw [if_neg hxy, zero_add]
      obtain ⟨c, hy⟩ : ∃ c : ℕ, y = x + c := ⟨y - x, by omega⟩
      have hcpos : 0 < c := by omega
      have hc' : (0 : ℝ) < c := by exact_mod_cast hcpos
      subst hy
      have hsum : Summable (fun m : ℕ => JF.gB2 ((x : ℝ) + m)) := summable_gB2 JF x
      have hsum' : Summable (fun m : ℕ => JF.gB2 ((x : ℝ) + m + c)) := by
        have := (summable_nat_add_iff c).2 hsum
        refine this.congr (fun m => ?_)
        push_cast; ring_nf
      have hts : ∑' m : ℕ, JF.atomBSum x (x + c) m =
          -(1 / (c : ℝ)) * ∑ j ∈ range c, JF.gB2 ((x : ℝ) + j) := by
        have e : ∀ m : ℕ, JF.atomBSum x (x + c) m =
            -(1 / (c : ℝ)) * (JF.gB2 ((x : ℝ) + m) - JF.gB2 ((x : ℝ) + m + c)) :=
          fun m => atomBSum_offdiag JF x c m hcpos
        simp only [e]
        rw [tsum_mul_left, hsum.tsum_sub hsum']
        have h := hsum.sum_add_tsum_nat_add c
        have h2 : ∑' m : ℕ, JF.gB2 ((x : ℝ) + ((m + c : ℕ) : ℝ)) = ∑' m : ℕ, JF.gB2 ((x : ℝ) + m + c) :=
          tsum_congr (fun m => by push_cast; ring_nf)
        rw [h2] at h
        have h3 : ∑' m : ℕ, JF.gB2 ((x : ℝ) + m) - ∑' m : ℕ, JF.gB2 ((x : ℝ) + m + c) =
            ∑ j ∈ range c, JF.gB2 ((x : ℝ) + j) := by linarith
        rw [h3]
      rw [hts]
      have hmin : min x (x + c) = x := min_eq_left (by omega)
      have hmax : max x (x + c) = x + c := max_eq_right (by omega)
      have hMnQ : JF.MnB x (x + c) = (1 / JF.norm) * (1 / (c : ℚ)) *
          ∑ j ∈ range c, -∑ i, (JF.b i : ℚ) / (((x : ℚ) + j) + JF.μ i) ^ 2 := by
        unfold MnB
        rw [if_neg hxy, hmin, hmax]
        have hcc : (((x + c : ℕ) : ℚ) - ((x : ℕ) : ℚ)) = (c : ℚ) := by push_cast; ring
        rw [hcc, sum_Ioc_shift']
        congr 1
        refine Finset.sum_congr rfl (fun j _ => ?_)
        unfold DeltaB
        push_cast
        ring_nf
      have hMnR := congrArg (Rat.cast : ℚ → ℝ) hMnQ
      push_cast at hMnR
      rw [hMnR]
      unfold gB2
      rw [show ∑ j ∈ range c, -∑ i, (JF.b i : ℝ) / (((x : ℝ) + j) + JF.μ i) ^ 2 =
        -∑ j ∈ range c, ∑ i, (JF.b i : ℝ) / (((x : ℝ) + j) + JF.μ i) ^ 2 by
          rw [Finset.sum_neg_distrib]]
      field_simp

/-! ### Part B2: the double reflection term `E_b` -/

/-- The `n`-th term of the double reflection series: `∑_i b_i / (z+n+μ_i)²`. -/
noncomputable def eterm2 (z : ℂ) (n : ℤ) : ℂ := ∑ i, (JF.b i : ℂ) / (z + n + (JF.μ i : ℂ)) ^ 2

/-- `E_b(z) = ∑_{n ∈ ℤ} eterm2 z n`. -/
noncomputable def E2 (z : ℂ) : ℂ := ∑' n : ℤ, JF.eterm2 z n

/-- The closed form `E_b(z) = π² ∑_i b_i / sin² π(z+μ_i)`. -/
noncomputable def E2cf (z : ℂ) : ℂ :=
  ∑ i, (JF.b i : ℂ) * ((Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ))) ^ 2)

lemma summable_inv_sq_int (w : ℂ) : Summable fun n : ℤ => 1 / (w + n) ^ 2 := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 2) (by norm_num)
  refine h.congr (fun n => ?_)
  simp [one_div]

theorem summable_eterm2 (z : ℂ) : Summable (JF.eterm2 z) := by
  unfold eterm2
  refine summable_sum (fun i _ => ?_)
  have := (summable_inv_sq_int (z + (JF.μ i : ℂ))).mul_left (JF.b i : ℂ)
  refine this.congr (fun n => ?_)
  rw [mul_one_div, show z + (JF.μ i : ℂ) + n = z + n + (JF.μ i : ℂ) by ring]

lemma hasDerivAt_pi_cot {w : ℂ} (hw : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    HasDerivAt (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))
      (-((Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * w) ^ 2)) w := by
  have hc : HasDerivAt (fun x : ℂ => Complex.cos ((Real.pi : ℂ) * x))
      (-(Real.pi : ℂ) * Complex.sin ((Real.pi : ℂ) * w)) w := by
    exact (((hasDerivAt_id w).const_mul (Real.pi : ℂ)).ccos).congr_deriv (by simp only [id]; ring)
  have hs : HasDerivAt (fun x : ℂ => Complex.sin ((Real.pi : ℂ) * x))
      (Complex.cos ((Real.pi : ℂ) * w) * (Real.pi : ℂ)) w := by
    exact (((hasDerivAt_id w).const_mul (Real.pi : ℂ)).csin).congr_deriv (by simp only [id]; ring)
  have hq := (hc.div hs hw).const_mul (Real.pi : ℂ)
  have e : (fun x : ℂ => (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * x))
      = fun x => (Real.pi : ℂ) * (Complex.cos ((Real.pi : ℂ) * x) / Complex.sin ((Real.pi : ℂ) * x)) := by
    funext x; rw [Complex.cot_eq_cos_div_sin]
  rw [e]
  convert hq using 1
  have h1 := Complex.sin_sq_add_cos_sq ((Real.pi : ℂ) * w)
  field_simp
  linear_combination h1

/-- `∑_{n ∈ ℤ} (w+n)⁻² = π² / sin² πw` in the upper half-plane (second derivative of the cotangent
series, Mathlib's `iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow`). -/
theorem tsum_inv_sq_int {w : ℂ} (hw : 0 < w.im) :
    ∑' n : ℤ, 1 / (w + n) ^ 2 = (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * w) ^ 2 := by
  have hwmem : w ∈ UpperHalfPlane.upperHalfPlaneSet := hw
  have h1 := iteratedDerivWithin_cot_pi_mul_eq_mul_tsum_div_pow (k := 1) le_rfl hwmem
  have hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    have hz : w ∈ Complex.integerComplement := UpperHalfPlane.coe_mem_integerComplement ⟨w, hw⟩
    intro h0
    obtain ⟨n, hn⟩ := (Complex.sin_eq_zero_iff.1 h0)
    apply hz
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  rw [iteratedDerivWithin_one,
    derivWithin_of_isOpen UpperHalfPlane.isOpen_upperHalfPlaneSet hwmem,
    (hasDerivAt_pi_cot hsin).deriv] at h1
  simp only [Nat.factorial_one, pow_one, Nat.cast_one, mul_one, one_mul] at h1
  have : ∑' n : ℤ, 1 / (w + n) ^ 2 = (Real.pi : ℂ) ^ 2 / Complex.sin ((Real.pi : ℂ) * w) ^ 2 := by
    have h2 : ∑' n : ℤ, 1 / (w + (n : ℂ)) ^ (1 + 1) = ∑' n : ℤ, 1 / (w + n) ^ 2 := rfl
    rw [h2] at h1
    linear_combination h1
  exact this

theorem E2_eq_E2cf_of_im_pos {z : ℂ} (hz : 0 < z.im) : JF.E2 z = JF.E2cf z := by
  unfold E2 E2cf eterm2
  rw [Summable.tsum_finsetSum (fun i _ => by
    have := (summable_inv_sq_int (z + (JF.μ i : ℂ))).mul_left (JF.b i : ℂ)
    refine this.congr (fun n => ?_)
    rw [mul_one_div, show z + (JF.μ i : ℂ) + n = z + n + (JF.μ i : ℂ) by ring])]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi : 0 < (z + (JF.μ i : ℂ)).im := by simpa using hz
  rw [← tsum_inv_sq_int hi, ← tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  rw [show z + (JF.μ i : ℂ) + n = z + n + (JF.μ i : ℂ) by ring, mul_one_div]

lemma eterm2_conj (z : ℂ) (n : ℤ) : JF.eterm2 ((starRingEnd ℂ) z) n = (starRingEnd ℂ) (JF.eterm2 z n) := by
  unfold eterm2
  simp [map_sum, map_div₀, map_pow]

lemma E2_conj (z : ℂ) : JF.E2 ((starRingEnd ℂ) z) = (starRingEnd ℂ) (JF.E2 z) := by
  unfold E2
  rw [Complex.conj_tsum]
  exact tsum_congr (fun n => eterm2_conj JF z n)

lemma E2cf_conj (z : ℂ) : JF.E2cf ((starRingEnd ℂ) z) = (starRingEnd ℂ) (JF.E2cf z) := by
  unfold E2cf
  simp only [map_sum, map_mul, map_div₀, map_pow, map_add, Complex.conj_ofReal, map_intCast]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (starRingEnd ℂ) (Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))) =
    Complex.sin ((Real.pi : ℂ) * ((starRingEnd ℂ) z + (JF.μ i : ℂ))) by
      rw [← Complex.sin_conj]; simp]

/-- The series and the closed form agree off the real axis. -/
theorem E2_eq_E2cf {z : ℂ} (hz : z.im ≠ 0) : JF.E2 z = JF.E2cf z := by
  rcases lt_or_gt_of_ne hz with h | h
  · have hc : 0 < ((starRingEnd ℂ) z).im := by simpa using h
    have := E2_eq_E2cf_of_im_pos JF hc
    rw [E2_conj, E2cf_conj] at this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2
  · exact E2_eq_E2cf_of_im_pos JF h

/-- The closed form is holomorphic off the real poles. -/
theorem E2cf_differentiableAt {z : ℂ} (hz : z ∈ Polygon.poleFree JF.toFrame) :
    DifferentiableAt ℂ JF.E2cf z := by
  unfold E2cf
  refine DifferentiableAt.fun_sum (fun i _ => ?_)
  have hs := hz i
  refine DifferentiableAt.const_mul ?_ _
  refine DifferentiableAt.div (by fun_prop) (by fun_prop) ?_
  exact pow_ne_zero 2 hs

/-- High-edge bound for `E_b`: `‖E_b z‖ ≤ 16π² ∑|b_i| e^{-2π|Im z|}` for `|Im z| ≥ 1/8`. -/
theorem norm_E2cf_high {z : ℂ} (hz : 1 / 8 ≤ |z.im|) :
    ‖JF.E2cf z‖ ≤ 16 * Real.pi ^ 2 * (∑ i, |(JF.b i : ℝ)|) * Real.exp (-(2 * Real.pi * |z.im|)) := by
  have hpi := Real.pi_gt_three
  unfold E2cf
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [norm_mul, norm_div, norm_pow, norm_pow]
  have hw : ((Real.pi : ℂ) * (z + (JF.μ i : ℂ))).im = Real.pi * z.im := by simp
  have hge : 3 / 8 ≤ |((Real.pi : ℂ) * (z + (JF.μ i : ℂ))).im| := by
    rw [hw, abs_mul, abs_of_pos Real.pi_pos]; nlinarith
  have hsin := CatalanCore.Decay.norm_sin_ge _ hge
  rw [hw, abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hb : ‖((JF.b i : ℤ) : ℂ)‖ = |(JF.b i : ℝ)| := by simp
  have hpn : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hb, hpn]
  have hE : 0 < Real.exp (Real.pi * |z.im|) := Real.exp_pos _
  have hs0 : 0 < Real.exp (Real.pi * |z.im|) / 4 := by positivity
  have h2 : (Real.exp (Real.pi * |z.im|) / 4) ^ 2 ≤
      ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2 := pow_le_pow_left₀ hs0.le hsin 2
  have h2x : Real.exp (Real.pi * |z.im|) ^ 2 = Real.exp (2 * Real.pi * |z.im|) := by
    rw [sq, ← Real.exp_add]; ring_nf
  have hdiv : Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2 ≤
      16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * |z.im|)) := by
    have hpos : 0 < (Real.exp (Real.pi * |z.im|) / 4) ^ 2 := by positivity
    calc Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2
        ≤ Real.pi ^ 2 / (Real.exp (Real.pi * |z.im|) / 4) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) hpos h2
      _ = 16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * |z.im|)) := by
          have : Real.exp (-(2 * Real.pi * |z.im|)) = (Real.exp (Real.pi * |z.im|) ^ 2)⁻¹ := by
            rw [h2x, ← Real.exp_neg]
          rw [this]; field_simp; norm_num
  calc |(JF.b i : ℝ)| * (Real.pi ^ 2 / ‖Complex.sin ((Real.pi : ℂ) * (z + (JF.μ i : ℂ)))‖ ^ 2)
      ≤ |(JF.b i : ℝ)| * (16 * Real.pi ^ 2 * Real.exp (-(2 * Real.pi * |z.im|))) :=
        mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)
    _ = _ := by ring

/-! ### Part B3a: the ray integral of one double pole against `k` -/

end JetFrame

open CatalanCore.Frame (g3F)
open CatalanLambda.Decay (contL_tri_west contL_tri_east norm_exp_ofReal_mul_I)

/-- `∂_p g3F`: a double pole at `p` and simple poles at `a`, `b`. -/
noncomputable def g4F (p a b : ℝ) (z : ℂ) : ℂ := (z - p)⁻¹ * (z - p)⁻¹ * ((z - a)⁻¹ * (z - b)⁻¹)

lemma hasDerivAt_inv_sub (z : ℂ) {p : ℝ} (h : z - (p : ℂ) ≠ 0) :
    HasDerivAt (fun q : ℝ => (z - (q : ℂ))⁻¹) ((z - (p : ℂ))⁻¹ * (z - (p : ℂ))⁻¹) p := by
  have hc : HasDerivAt (fun q : ℝ => z - (q : ℂ)) (-1) p :=
    ((hasDerivAt_const p z).sub (hasDerivAt_id p).ofReal_comp).congr_deriv (by simp)
  have := hc.inv h
  exact this.congr_deriv (by field_simp)

/-- The ray integral of `g3F p a b` is differentiable in the position `p` of the pole, with derivative
the ray integral of `g4F`. -/
theorem rayI_g3_deriv {x θ a b p₀ : ℝ} (hp : p₀ ≠ x) (ha : a ≠ x) (hb : b ≠ x)
    (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => g4F p₀ a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) ∧
    HasDerivAt (fun p : ℝ => rayI x θ (g3F p a b)) (rayI x θ (g4F p₀ a b)) p₀ := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ) with hKdef
  set ε : ℝ := |x - p₀| / 2 with hε
  have hε0 : 0 < ε := by
    have : 0 < |x - p₀| := abs_pos.2 (sub_ne_zero.2 hp.symm)
    positivity
  have ha0 : 0 < |x - a| := abs_pos.2 (sub_ne_zero.2 ha.symm)
  have hb0 : 0 < |x - b| := abs_pos.2 (sub_ne_zero.2 hb.symm)
  set m := min ε (min |x - a| |x - b|) with hm
  have hm0 : 0 < m := lt_min hε0 (lt_min ha0 hb0)
  have hmε : m ≤ ε := min_le_left _ _
  have hma : m ≤ |x - a| := (min_le_right _ _).trans (min_le_left _ _)
  have hmb : m ≤ |x - b| := (min_le_right _ _).trans (min_le_right _ _)
  have hball : ∀ p ∈ Metric.ball p₀ ε, ε ≤ |x - p| := by
    intro p hpb
    rw [Metric.mem_ball, Real.dist_eq] at hpb
    have h1 : |x - p₀| ≤ |x - p| + |p - p₀| := by
      calc |x - p₀| = |(x - p) + (p - p₀)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : |x - p₀| = 2 * ε := by rw [hε]; ring
    linarith
  have hne : ∀ p ∈ Metric.ball p₀ ε, p ≠ x := by
    intro p hpb hpx
    have := hball p hpb
    rw [hpx, sub_self, abs_zero] at this
    linarith
  set e := exp ((θ : ℂ) * I) with he
  let F : ℝ → ℝ → ℂ := fun p r => g3F p a b (rayPt x θ r) * e
  let F' : ℝ → ℝ → ℂ := fun p r => g4F p a b (rayPt x θ r) * e
  let bound : ℝ → ℝ := fun r => (1 / K ^ 4 * (1 / m ^ 2)) * (1 / (m + r) ^ 2)
  have hmeasF : ∀ p : ℝ, AEStronglyMeasurable (F p) (volume.restrict (Ioi 0)) := by
    intro p
    refine Measurable.aestronglyMeasurable ?_
    simp only [F, g3F, rayPt]
    fun_prop
  have hmeasF' : AEStronglyMeasurable (F' p₀) (volume.restrict (Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [F', g4F, rayPt]
    fun_prop
  have hint : Integrable (F p₀) (volume.restrict (Ioi 0)) :=
    integrableOn_ray3 p₀ a b hp ha hb hs
  have hbd : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ p ∈ Metric.ball p₀ ε, ‖F' p r‖ ≤ bound r := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr p hpb => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    simp only [F', g4F]
    have hen : ‖e‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    simp only [norm_mul, hen, mul_one]
    have h1 := norm_inv_rayPt_le (x := x) (θ := θ) p (hne p hpb) hs hr'
    have h2 := norm_inv_rayPt_le (x := x) (θ := θ) a ha hs hr'
    have h3 := norm_inv_rayPt_le (x := x) (θ := θ) b hb hs hr'
    have hmr : 0 < m + r := by linarith
    have hmp : m + r ≤ |x - p| + r := by have := hball p hpb; linarith
    have hma' : m + r ≤ |x - a| + r := by linarith
    have hmb' : m + r ≤ |x - b| + r := by linarith
    have h1' : 1 / (K * (|x - p| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have h2' : 1 / (K * (|x - a| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have h3' : 1 / (K * (|x - b| + r)) ≤ 1 / (K * (m + r)) :=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have hq : ‖(rayPt x θ r - p)⁻¹‖ ≤ 1 / (K * (m + r)) := h1.trans h1'
    have ha1 : ‖(rayPt x θ r - a)⁻¹‖ ≤ 1 / (K * (m + r)) := h2.trans h2'
    have hb1 : ‖(rayPt x θ r - b)⁻¹‖ ≤ 1 / (K * (m + r)) := h3.trans h3'
    calc ‖(rayPt x θ r - p)⁻¹‖ * ‖(rayPt x θ r - p)⁻¹‖ *
          (‖(rayPt x θ r - a)⁻¹‖ * ‖(rayPt x θ r - b)⁻¹‖)
        ≤ (1 / (K * (m + r))) * (1 / (K * (m + r))) *
            ((1 / (K * (m + r))) * (1 / (K * (m + r)))) :=
          mul_le_mul (mul_le_mul hq hq (norm_nonneg _) (by positivity))
            (mul_le_mul ha1 hb1 (norm_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = 1 / K ^ 4 * (1 / (m + r) ^ 4) := by field_simp
      _ ≤ 1 / K ^ 4 * (1 / m ^ 2 * (1 / (m + r) ^ 2)) := by
          gcongr
          rw [div_mul_div_comm, one_mul]
          apply one_div_le_one_div_of_le (by positivity)
          have : m ^ 2 * (m + r) ^ 2 ≤ (m + r) ^ 4 := by
            have h5 : m ^ 2 ≤ (m + r) ^ 2 := pow_le_pow_left₀ hm0.le (by linarith) 2
            calc m ^ 2 * (m + r) ^ 2 ≤ (m + r) ^ 2 * (m + r) ^ 2 :=
                  mul_le_mul_of_nonneg_right h5 (by positivity)
              _ = (m + r) ^ 4 := by ring
          exact this
      _ = bound r := by simp only [bound]; ring
  have hbint : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_invsq m hm0).const_mul _
  have hdiff : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), ∀ p ∈ Metric.ball p₀ ε,
      HasDerivAt (fun q => F q r) (F' p r) p := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr p hpb => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    have hz : rayPt x θ r - (p : ℂ) ≠ 0 := by
      have := rayPt_sub_ne (x := x) (θ := θ) (hne p hpb) hs hr'
      exact_mod_cast this
    have h := ((hasDerivAt_inv_sub (rayPt x θ r) hz).mul_const ((rayPt x θ r - (a : ℂ))⁻¹)).mul_const
      ((rayPt x θ r - (b : ℂ))⁻¹) |>.mul_const e
    exact h.congr_deriv (by simp only [F', g4F]; ring)
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := F) (F' := F') (x₀ := p₀) (s := Metric.ball p₀ ε) (bound := bound)
    (Metric.ball_mem_nhds p₀ hε0) (Eventually.of_forall hmeasF) hint hmeasF' hbd hbint hdiff

theorem integrableOn_ray4 {x θ a b p : ℝ} (hp : p ≠ x) (ha : a ≠ x) (hb : b ≠ x)
    (hs : Real.sin θ ≠ 0) :
    IntegrableOn (fun r : ℝ => g4F p a b (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0) :=
  (rayI_g3_deriv hp ha hb hs).1

theorem hasDerivAt_rayI_g3 {x θ a b p₀ : ℝ} (hp : p₀ ≠ x) (ha : a ≠ x) (hb : b ≠ x)
    (hs : Real.sin θ ≠ 0) :
    HasDerivAt (fun p : ℝ => rayI x θ (g3F p a b)) (rayI x θ (g4F p₀ a b)) p₀ :=
  (rayI_g3_deriv hp ha hb hs).2

/-- The contour integral of `g3F` is a known function of `p`; its derivative gives the double pole. -/
theorem contL_g4 (p a b x φ : ℝ) (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : p ≠ x) (ha : x < a) (hb : x < b) :
    contL x φ (g4F p a b)
      = -(2 * Real.pi * I) *
        (if p < x then ((a : ℂ) + b - 2 * p) / ((((p : ℂ) - a) * ((p : ℂ) - b)) ^ 2) else 0) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hD : HasDerivAt (fun q : ℝ => contL x φ (g3F q a b)) (contL x φ (g4F p a b)) p := by
    unfold contL
    exact (hasDerivAt_rayI_g3 hp ha.ne' hb.ne' hsφ').sub (hasDerivAt_rayI_g3 hp ha.ne' hb.ne' hsφ)
  have hpa : ((p : ℂ) - a) ≠ 0 ∨ True := Or.inr trivial
  rcases lt_or_gt_of_ne hp with hlt | hgt
  · -- the pole is to the left of `x`: the known value `-2πi / ((p-a)(p-b))`
    have hev : (fun q : ℝ => contL x φ (g3F q a b)) =ᶠ[nhds p]
        fun q : ℝ => -(2 * Real.pi * I) * (1 / (((q : ℂ) - a) * ((q : ℂ) - b))) := by
      filter_upwards [Iio_mem_nhds hlt] with q hq
      exact contL_tri_west q a b x φ h1 h2 hq ha hb
    have hpa : (p : ℂ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by linarith : p ≠ a))
    have hpb : (p : ℂ) - b ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (by linarith : p ≠ b))
    have hd2 : HasDerivAt (fun q : ℝ => -(2 * Real.pi * I) * (1 / (((q : ℂ) - a) * ((q : ℂ) - b))))
        (-(2 * Real.pi * I) * (((a : ℂ) + b - 2 * p) / ((((p : ℂ) - a) * ((p : ℂ) - b)) ^ 2))) p := by
      have hq1 : HasDerivAt (fun q : ℝ => (q : ℂ) - a) 1 p :=
        ((hasDerivAt_id p).ofReal_comp).sub_const (a : ℂ) |>.congr_deriv (by simp)
      have hq2 : HasDerivAt (fun q : ℝ => (q : ℂ) - b) 1 p :=
        ((hasDerivAt_id p).ofReal_comp).sub_const (b : ℂ) |>.congr_deriv (by simp)
      have hpr := hq1.mul hq2
      have hdv := ((hasDerivAt_const p (1 : ℂ)).div hpr (mul_ne_zero hpa hpb)).const_mul (-(2 * Real.pi * I))
      exact hdv.congr_deriv (by simp only [Pi.mul_apply]; ring)
    have hD' : HasDerivAt (fun q : ℝ => contL x φ (g3F q a b))
        (-(2 * Real.pi * I) * (((a : ℂ) + b - 2 * p) / ((((p : ℂ) - a) * ((p : ℂ) - b)) ^ 2))) p :=
      hd2.congr_of_eventuallyEq hev
    rw [hD.unique hD', if_pos hlt]
  · have hev : (fun q : ℝ => contL x φ (g3F q a b)) =ᶠ[nhds p] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hgt] with q hq
      exact contL_tri_east q a b x φ h1 h2 hq ha hb
    have hD' : HasDerivAt (fun q : ℝ => contL x φ (g3F q a b)) 0 p :=
      (hasDerivAt_const p (0 : ℂ)).congr_of_eventuallyEq hev
    rw [hD.unique hD', if_neg (not_lt.2 hgt.le)]
    simp

namespace JetFrame
variable (JF : JetFrame)

/-! ### Part B3b: the contour identity of `E_b` on the reference rays -/

lemma rayI_sum_g4 {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ι → ℝ) {x θ : ℝ} (a b : ℝ)
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0) :
    rayI x θ (fun z => ∑ i ∈ s, c i * g4F (p i) a b z)
      = ∑ i ∈ s, c i * rayI x θ (g4F (p i) a b) := by
  unfold rayI
  have hint : ∀ i ∈ s, Integrable
      (fun r : ℝ => c i * (g4F (p i) a b (rayPt x θ r) * exp ((θ : ℂ) * I)))
      (volume.restrict (Ioi 0)) := fun i hi =>
    (integrableOn_ray4 (hp i hi) ha hb hs).const_mul (c i)
  have e : ∀ r : ℝ, (∑ i ∈ s, c i * g4F (p i) a b (rayPt x θ r)) * exp ((θ : ℂ) * I)
      = ∑ i ∈ s, c i * (g4F (p i) a b (rayPt x θ r) * exp ((θ : ℂ) * I)) := by
    intro r; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [e]
  rw [integral_finset_sum s hint]
  exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

lemma contL_sum_g4 {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ι → ℝ) {x φ : ℝ} (a b : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) :
    contL x φ (fun z => ∑ i ∈ s, c i * g4F (p i) a b z)
      = ∑ i ∈ s, c i * contL x φ (g4F (p i) a b) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  unfold contL
  rw [rayI_sum_g4 s c p a b hp ha hb hsφ, rayI_sum_g4 s c p a b hp ha hb hsφ',
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

open CatalanCore.Frame (xstar xstar_lt_nat pole_ne xs_le_dist)
open CatalanCore.Frame (ContourOK)

lemma eterm2_mul_eq (z : ℂ) (n : ℤ) (a b : ℕ) :
    JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹)
      = ∑ i, (JF.b i : ℂ) * g4F (-(n : ℝ) - (JF.μ i : ℝ)) a b z := by
  unfold eterm2 g4F
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  rw [show z - (-(n : ℂ) - (JF.μ i : ℂ)) = z + n + (JF.μ i : ℂ) by ring]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- **Value of the contour integral of one double term.** -/
theorem contL_eterm2 (hC : JF.toFrame.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (N0 a b : ℕ) (n : ℤ) :
    contL (JF.toFrame.xstar N0) φ (fun z => JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = 2 * Real.pi * I * ((JF.tailTermB N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) := by
  have hfun : (fun z : ℂ => JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => ∑ i, (JF.b i : ℂ) * g4F (-(n : ℝ) - (JF.μ i : ℝ)) a b z := by
    funext z; exact eterm2_mul_eq JF z n a b
  have hxa := xstar_lt_nat hC N0 a
  have hxb := xstar_lt_nat hC N0 b
  rw [hfun, contL_sum_g4 Finset.univ (fun i => (JF.b i : ℂ)) (fun i => -(n : ℝ) - (JF.μ i : ℝ))
    (a : ℝ) (b : ℝ) h1 h2 (fun i _ => pole_ne hC N0 n i) hxa.ne' hxb.ne']
  unfold tailTermB atomB
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hlt : (N0 : ℝ) + (JF.xs : ℝ) < (n : ℝ) + (JF.μ i : ℝ)
  · have hp : (-(n : ℝ) - (JF.μ i : ℝ)) < JF.toFrame.xstar N0 := by unfold xstar; linarith
    rw [contL_g4 _ _ _ _ _ h1 h2 hp.ne hxa hxb, if_pos hp, if_pos (by exact_mod_cast hlt)]
    push_cast
    have hpa : (-(n : ℂ) - (JF.μ i : ℂ) - (a : ℂ)) = -((a : ℂ) + n + (JF.μ i : ℂ)) := by ring
    have hpb : (-(n : ℂ) - (JF.μ i : ℂ) - (b : ℂ)) = -((b : ℂ) + n + (JF.μ i : ℂ)) := by ring
    rw [hpa, hpb]
    have hA : ((a : ℂ) + n + (JF.μ i : ℂ)) ≠ 0 := by
      have : (a : ℝ) + n + JF.μ i ≠ 0 := by
        have := hxa; unfold xstar at this; intro h0; linarith
      exact_mod_cast this
    have hB : ((b : ℂ) + n + (JF.μ i : ℂ)) ≠ 0 := by
      have : (b : ℝ) + n + JF.μ i ≠ 0 := by
        have := hxb; unfold xstar at this; intro h0; linarith
      exact_mod_cast this
    field_simp
    ring
  · have hp : JF.toFrame.xstar N0 < (-(n : ℝ) - (JF.μ i : ℝ)) := by
      unfold xstar; push_neg at hlt
      have := pole_ne hC N0 n i
      have h3 : (-(n : ℝ) - (JF.μ i : ℝ)) ≠ -(N0 : ℝ) - (JF.xs : ℝ) := this
      rcases lt_or_gt_of_ne h3 with h4 | h4
      · linarith
      · exact h4
    rw [contL_g4 _ _ _ _ _ h1 h2 hp.ne' hxa hxb, if_neg (not_lt.2 hp.le), if_neg (by exact_mod_cast hlt)]
    simp

/-- Uniform domination of the terms `eterm2` along a ray from `x*`. -/
noncomputable def Bn2 (N0 : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  ∑ i, |(JF.b i : ℝ)| * (1 / (Real.sqrt (kap2 θ) ^ 2) *
    (1 / |JF.toFrame.xstar N0 - (-(n : ℝ) - (JF.μ i : ℝ))| ^ 2))

lemma summable_inv_sq_real (c : ℝ) : Summable fun n : ℤ => 1 / |(n : ℝ) + c| ^ 2 := by
  have h := (summable_inv_sq_int (c : ℂ)).norm
  refine h.congr (fun n => ?_)
  rw [norm_div, norm_one, norm_pow]
  rw [show (c : ℂ) + (n : ℂ) = (((c + n : ℝ)) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, add_comm]

lemma summable_Bn2 (N0 : ℕ) (θ : ℝ) : Summable (JF.Bn2 N0 θ) := by
  unfold Bn2
  refine summable_sum (fun i _ => ?_)
  refine Summable.mul_left _ ?_
  refine Summable.mul_left _ ?_
  have := summable_inv_sq_real (JF.toFrame.xstar N0 + (JF.μ i : ℝ))
  refine this.congr (fun n => ?_)
  rw [show ((n : ℝ) + (JF.toFrame.xstar N0 + (JF.μ i : ℝ))) =
    JF.toFrame.xstar N0 - (-(n : ℝ) - (JF.μ i : ℝ)) by ring]

lemma norm_eterm2_ray_le (hC : JF.toFrame.ContourOK) (N0 : ℕ) (n : ℤ) {θ r : ℝ}
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖JF.eterm2 (rayPt (JF.toFrame.xstar N0) θ r) n‖ ≤ JF.Bn2 N0 θ n := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  unfold eterm2 Bn2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_div, norm_pow]
  have hz : (rayPt (JF.toFrame.xstar N0) θ r + (n : ℂ) + (JF.μ i : ℂ)) =
      rayPt (JF.toFrame.xstar N0) θ r - ((-(n : ℝ) - (JF.μ i : ℝ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hz]
  have hb : ‖(JF.b i : ℂ)‖ = |(JF.b i : ℝ)| := by simp
  set p : ℝ := -(n : ℝ) - (JF.μ i : ℝ) with hp
  have hge := CatalanLambda.Decay.norm_rayPt_sub_ge (x := JF.toFrame.xstar N0) (θ := θ) p hs hr
  have hxp : 0 < |JF.toFrame.xstar N0 - p| :=
    abs_pos.2 (sub_ne_zero.2 (pole_ne hC N0 n i).symm)
  set K := Real.sqrt (kap2 θ) with hKdef
  have h2 : K ^ 2 * |JF.toFrame.xstar N0 - p| ^ 2 ≤
      ‖rayPt (JF.toFrame.xstar N0) θ r - (p : ℂ)‖ ^ 2 := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    nlinarith
  rw [hb]
  calc |(JF.b i : ℝ)| / ‖rayPt (JF.toFrame.xstar N0) θ r - (p : ℂ)‖ ^ 2
      ≤ |(JF.b i : ℝ)| / (K ^ 2 * |JF.toFrame.xstar N0 - p| ^ 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) h2
    _ = |(JF.b i : ℝ)| * (1 / K ^ 2 * (1 / |JF.toFrame.xstar N0 - p| ^ 2)) := by
        field_simp

open CatalanCore.Frame (norm_inv_ray_nat_le)

/-- **Interchange of sum and ray integral for `E_b`**: `∑_n ∫_ray e_n k = ∫_ray E_b k`. -/
theorem rayI_E2_hasSum (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (JF.toFrame.xstar N0) θ
        (fun z => JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (JF.toFrame.xstar N0) θ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  have hxs : (0 : ℝ) < JF.xs := by exact_mod_cast hC.xs_pos
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := JF.toFrame.xstar N0 with hxdef
  unfold rayI
  refine hasSum_integral_of_dominated_convergence
    (fun n r => JF.Bn2 N0 θ n * ((1 / K ^ 2) * (1 / ((JF.xs : ℝ) + r) ^ 2))) ?_ ?_ ?_ ?_ ?_
  · intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold rayPt eterm2
    refine Measurable.mul (Measurable.mul ?_ (by fun_prop)) (by fun_prop)
    refine Finset.measurable_sum _ (fun i _ => ?_)
    fun_prop
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_eterm2_ray_le JF hC N0 n hs hr'
    have h2 := norm_inv_ray_nat_le (Fr := JF.toFrame) hC N0 a hs hr'
    have h3 := norm_inv_ray_nat_le (Fr := JF.toFrame) hC N0 b hs hr'
    have hpos : 0 < K * ((JF.xs : ℝ) + r) := by positivity
    have hB : 0 ≤ JF.Bn2 N0 θ n := by unfold Bn2; positivity
    calc ‖JF.eterm2 (rayPt x θ r) n‖ * (‖(rayPt x θ r - (a : ℂ))⁻¹‖ * ‖(rayPt x θ r - (b : ℂ))⁻¹‖)
        ≤ JF.Bn2 N0 θ n * ((1 / (K * ((JF.xs : ℝ) + r))) * (1 / (K * ((JF.xs : ℝ) + r)))) := by
          apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
            (by positivity) hB
      _ = _ := by field_simp
  · exact Eventually.of_forall fun r => (summable_Bn2 JF N0 θ).mul_right _
  · have hI := (integrableOn_invsq (JF.xs : ℝ) hxs).const_mul (1 / K ^ 2)
    have : (fun r : ℝ => ∑' n : ℤ, JF.Bn2 N0 θ n * ((1 / K ^ 2) * (1 / ((JF.xs : ℝ) + r) ^ 2)))
        = fun r => (∑' n : ℤ, JF.Bn2 N0 θ n) * ((1 / K ^ 2) * (1 / ((JF.xs : ℝ) + r) ^ 2)) := by
      funext r; exact tsum_mul_right
    rw [this]
    exact hI.const_mul _
  · refine Eventually.of_forall fun r => ?_
    exact ((JF.summable_eterm2 _).hasSum.mul_right _).mul_right _

/-- The tail of the atoms of `E_b`: only the poles left of `x*` contribute. -/
theorem hasSum_tailB (hC : JF.toFrame.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (N0 a b : ℕ) :
    HasSum (fun m : ℕ => ((JF.tailTermB N0 a b (m : ℝ) : ℝ) : ℂ))
      ((2 * Real.pi * I)⁻¹ *
        contL (JF.toFrame.xstar N0) φ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hU := rayI_E2_hasSum JF hC N0 a b hsφ
  have hL := rayI_E2_hasSum JF hC N0 a b hsφ'
  have hCt := hL.sub hU
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hT : HasSum (fun n : ℤ => ((JF.tailTermB N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ))
      ((2 * Real.pi * I)⁻¹ *
        contL (JF.toFrame.xstar N0) φ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
    have h3 := hCt.mul_left ((2 * Real.pi * I)⁻¹)
    have h4 : (fun n : ℤ => (2 * Real.pi * I)⁻¹ * (rayI (JF.toFrame.xstar N0) (-φ)
          (fun z => JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹))
        - rayI (JF.toFrame.xstar N0) φ (fun z => JF.eterm2 z n * ((z - a)⁻¹ * (z - b)⁻¹))))
        = fun n : ℤ => ((JF.tailTermB N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) := by
      funext n
      have := contL_eterm2 JF hC h1 h2 N0 a b n
      unfold contL at this
      rw [this]
      field_simp
    rw [h4] at h3
    exact h3
  have hi : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
  have hzero : ∀ n : ℤ, n ∉ Set.range (Nat.cast : ℕ → ℤ) →
      ((JF.tailTermB N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) = 0 := by
    intro n hn
    have hneg : n < 0 := by
      by_contra h
      push_neg at h
      exact hn ⟨n.toNat, by simp [Int.toNat_of_nonneg h]⟩
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    have hxs : (0 : ℝ) < JF.xs := by exact_mod_cast hC.xs_pos
    have hμ : ∀ i, (JF.μ i : ℝ) ≤ 1 := fun i => by exact_mod_cast (JF.hμ i).2
    have h0 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
    unfold tailTermB
    push_cast
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg (by have := hμ i; intro h; linarith)]
    simp
  have := (hi.hasSum_iff hzero).2 hT
  simpa [Function.comp_def] using this

/-- **The contour identity of `E_b`** on the two reference rays:
`∑' m, atomBSum a b m = atomHeadB N0 a b + (1/2πi) ∫_Γ E_b v_a v_b dz`. -/
theorem contour_identityB (hC : JF.toFrame.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ)
    (h2 : φ < Real.pi) (N0 a b : ℕ) :
    ((∑' m : ℕ, JF.atomBSum a b m : ℝ) : ℂ)
      = ((JF.atomHeadB N0 a b : ℝ) : ℂ) + (2 * Real.pi * I)⁻¹ *
          contL (JF.toFrame.xstar N0) φ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
  have hT := hasSum_tailB JF hC h1 h2 N0 a b
  set M := N0 + ⌈(JF.xs : ℝ)⌉₊ with hM
  have hH : HasSum (fun m : ℕ => ((JF.headTermB N0 a b (m : ℝ) : ℝ) : ℂ))
      (∑ m ∈ range M, ((JF.headTermB N0 a b (m : ℝ) : ℝ) : ℂ)) := by
    refine hasSum_sum_of_ne_finset_zero (fun m hm => ?_)
    have hm' : M ≤ m := by simpa using hm
    have hc : (JF.xs : ℝ) ≤ ⌈(JF.xs : ℝ)⌉₊ := Nat.le_ceil _
    have hmM : ((N0 + ⌈(JF.xs : ℝ)⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast hm'
    push_cast at hmM
    have hμ : ∀ i, (0 : ℝ) < (JF.μ i : ℝ) := fun i => by exact_mod_cast (JF.hμ i).1
    unfold headTermB
    push_cast
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_pos (by have := hμ i; linarith)]
    simp
  have hsum := hT.add hH
  have hpt : ∀ m : ℕ, ((JF.tailTermB N0 a b (m : ℝ) : ℝ) : ℂ) + ((JF.headTermB N0 a b (m : ℝ) : ℝ) : ℂ)
      = ((JF.atomBSum a b m : ℝ) : ℂ) := by
    intro m
    unfold tailTermB headTermB atomBSum
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  simp only [hpt] at hsum
  rw [Complex.ofReal_tsum, hsum.tsum_eq, add_comm]
  unfold atomHeadB
  push_cast
  rfl

/-! ### Part B4: the jet source, its deformation to a polygon -/

open CatalanLambda.Decay (rayPt_im)
open CatalanCore.Uniform.Decay.Polygon (srcF poleFree halfP diskR diskR_pos poleFree_of_im_ne
  poleFree_of_ball node_ne_of_ball sub_nat_ne_of_im im_ne_of_halfP Khi Khi_nonneg polyI rayInt
  phiRef phiRef_gt phiRef_lt sin_phiRef_pos rayI_eq_rayInt norm_inv_sub_nat_le deform
  integrableOn_ray diffAt_of_mem ray_mem)

/-- The source of the `b`-part, `E_b(z)/((z-a)(z-b))`, with the closed form of `E_b`. -/
noncomputable def srcB (a b : ℕ) (z : ℂ) : ℂ := JF.E2cf z * ((z - a)⁻¹ * (z - b)⁻¹)

/-- The source of the jet: `(E_a + E_b)(z) / ((z-a)(z-b))`. -/
noncomputable def srcJ (a b : ℕ) (z : ℂ) : ℂ := srcF JF.toFrame a b z + JF.srcB a b z

theorem srcB_differentiableAt {a b : ℕ} {z : ℂ} (hz : z ∈ poleFree JF.toFrame)
    (ha : z - (a : ℂ) ≠ 0) (hb : z - (b : ℂ) ≠ 0) : DifferentiableAt ℂ (JF.srcB a b) z := by
  unfold srcB
  refine (E2cf_differentiableAt JF hz).mul (DifferentiableAt.mul ?_ ?_)
  · exact ((differentiableAt_id.sub_const _).inv ha)
  · exact ((differentiableAt_id.sub_const _).inv hb)

theorem srcJ_differentiableOn_halfP (σ : ℝ) (a b : ℕ) :
    DifferentiableOn ℂ (JF.srcJ a b) (halfP σ) := fun z hz => by
  have hz' := im_ne_of_halfP hz
  have h1 := Polygon.srcF_differentiableAt (Fr := JF.toFrame) (poleFree_of_im_ne hz')
    (sub_nat_ne_of_im hz' a) (sub_nat_ne_of_im hz' b)
  have h2 := srcB_differentiableAt JF (poleFree_of_im_ne hz') (sub_nat_ne_of_im hz' a)
    (sub_nat_ne_of_im hz' b)
  exact (h1.add h2).differentiableWithinAt

theorem srcB_differentiableOn_halfP (σ : ℝ) (a b : ℕ) :
    DifferentiableOn ℂ (JF.srcB a b) (halfP σ) := fun z hz => by
  have hz' := im_ne_of_halfP hz
  exact (srcB_differentiableAt JF (poleFree_of_im_ne hz') (sub_nat_ne_of_im hz' a)
    (sub_nat_ne_of_im hz' b)).differentiableWithinAt

theorem srcJ_differentiableOn_ball (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) :
    DifferentiableOn ℂ (JF.srcJ a b) (Metric.ball ((JF.toFrame.xstar N0 : ℝ) : ℂ) (diskR JF.toFrame)) := by
  intro z hz
  have hz0 : z ∈ Metric.ball ((JF.toFrame.xstar N0 : ℝ) : ℂ) (JF.δ0 : ℝ) :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hpf := poleFree_of_ball hC N0 hz0
  have h1 := Polygon.srcF_differentiableAt (Fr := JF.toFrame) hpf (node_ne_of_ball hC N0 a hz)
    (node_ne_of_ball hC N0 b hz)
  have h2 := srcB_differentiableAt JF hpf (node_ne_of_ball hC N0 a hz) (node_ne_of_ball hC N0 b hz)
  exact (h1.add h2).differentiableWithinAt

theorem srcB_differentiableOn_ball (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) :
    DifferentiableOn ℂ (JF.srcB a b) (Metric.ball ((JF.toFrame.xstar N0 : ℝ) : ℂ) (diskR JF.toFrame)) := by
  intro z hz
  have hz0 : z ∈ Metric.ball ((JF.toFrame.xstar N0 : ℝ) : ℂ) (JF.δ0 : ℝ) :=
    Metric.ball_subset_ball (min_le_left _ _) hz
  have hpf := poleFree_of_ball hC N0 hz0
  exact (srcB_differentiableAt JF hpf (node_ne_of_ball hC N0 a hz)
    (node_ne_of_ball hC N0 b hz)).differentiableWithinAt

/-- The constant of the decay hypothesis for the `b`-part. -/
noncomputable def KhiB : ℝ := 16 * Real.pi ^ 2 * ∑ i, |(JF.b i : ℝ)|

theorem KhiB_nonneg : 0 ≤ JF.KhiB := by unfold KhiB; positivity

theorem srcB_decay {σ : ℝ} (hσ : |σ| = 1) (a b : ℕ) :
    ∀ z : ℂ, 1 ≤ σ * z.im → ‖JF.srcB a b z‖ ≤ JF.KhiB / (σ * z.im) ^ 2 := by
  intro z hz
  have habs : |z.im| = σ * z.im := by
    rw [← one_mul |z.im|, ← hσ, ← abs_mul]; exact abs_of_pos (by linarith)
  have hne : z.im ≠ 0 := by intro h; rw [h, mul_zero] at hz; linarith
  have hE := norm_E2cf_high JF (z := z) (by rw [habs]; linarith)
  have hex : Real.exp (-(2 * Real.pi * |z.im|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := Real.pi_pos; nlinarith [abs_nonneg z.im]
  have hE' : ‖JF.E2cf z‖ ≤ JF.KhiB := by
    refine hE.trans ?_
    have : 0 ≤ 16 * Real.pi ^ 2 * ∑ i, |(JF.b i : ℝ)| := by positivity
    unfold KhiB; nlinarith
  unfold srcB
  rw [norm_mul, norm_mul]
  have h1 := norm_inv_sub_nat_le hne a
  have h2 := norm_inv_sub_nat_le hne b
  rw [habs] at h1 h2
  have hpos : 0 < σ * z.im := by linarith
  calc ‖JF.E2cf z‖ * (‖(z - (a : ℂ))⁻¹‖ * ‖(z - (b : ℂ))⁻¹‖)
      ≤ JF.KhiB * ((1 / (σ * z.im)) * (1 / (σ * z.im))) :=
        mul_le_mul hE' (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
          (by positivity) (KhiB_nonneg JF)
    _ = JF.KhiB / (σ * z.im) ^ 2 := by field_simp

theorem srcJ_decay {σ : ℝ} (hσ : |σ| = 1) (a b : ℕ) :
    ∀ z : ℂ, 1 ≤ σ * z.im → ‖JF.srcJ a b z‖ ≤ (Khi JF.toFrame + JF.KhiB) / (σ * z.im) ^ 2 := by
  intro z hz
  have h1 := Polygon.srcF_decay (Fr := JF.toFrame) hσ a b z hz
  have h2 := srcB_decay JF hσ a b z hz
  unfold srcJ
  calc ‖srcF JF.toFrame a b z + JF.srcB a b z‖
      ≤ ‖srcF JF.toFrame a b z‖ + ‖JF.srcB a b z‖ := norm_add_le _ _
    _ ≤ Khi JF.toFrame / (σ * z.im) ^ 2 + JF.KhiB / (σ * z.im) ^ 2 := add_le_add h1 h2
    _ = _ := by ring

/-- **Upper deformation** of the jet source. -/
theorem upper_deformJ (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    polyI (JF.srcJ a b) ((JF.toFrame.xstar N0 : ℝ) : ℂ) pts d
      = rayI (JF.toFrame.xstar N0) phiRef (JF.srcJ a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := 1) (δ := diskR JF.toFrame) (by simp) (diskR_pos hC)
    (srcJ_differentiableOn_halfP JF 1 a b) (srcJ_differentiableOn_ball JF hC N0 a b) pts
    (fun z hz => by simpa using hpts z hz) (by simpa using hd) ?_
    (add_nonneg Khi_nonneg (KhiB_nonneg JF)) (srcJ_decay JF (by simp) a b)
  rw [one_mul, Complex.exp_ofReal_mul_I_im]; exact sin_phiRef_pos

/-- **Lower deformation** of the jet source. -/
theorem lower_deformJ (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    polyI (JF.srcJ a b) ((JF.toFrame.xstar N0 : ℝ) : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d)
      = rayI (JF.toFrame.xstar N0) (-phiRef) (JF.srcJ a b) := by
  rw [rayI_eq_rayInt]
  refine deform (σ := -1) (δ := diskR JF.toFrame) (by simp) (diskR_pos hC)
    (srcJ_differentiableOn_halfP JF (-1) a b) (srcJ_differentiableOn_ball JF hC N0 a b) _
    (fun z hz => ?_) (by simpa using hd) ?_
    (add_nonneg Khi_nonneg (KhiB_nonneg JF)) (srcJ_decay JF (by simp) a b)
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
    simpa using hpts w hw
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]; linarith [sin_phiRef_pos]

/-! #### The ray integrals split over `E_a` and `E_b` -/

theorem integrableOn_src_ray (hC : JF.toFrame.ContourOK) (N0 : ℕ) {f : ℂ → ℂ} {σ θ : ℝ}
    (hfH : DifferentiableOn ℂ f (halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball ((JF.toFrame.xstar N0 : ℝ) : ℂ) (diskR JF.toFrame)))
    (hsin : 0 < σ * Real.sin θ) {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ z : ℂ, 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    IntegrableOn (fun r : ℝ => f (rayPt (JF.toFrame.xstar N0) θ r) * exp ((θ : ℂ) * I)) (Ioi 0) := by
  have hd : 0 < σ * (Complex.exp ((θ : ℂ) * I)).im := by
    rw [Complex.exp_ofReal_mul_I_im]; exact hsin
  have hv : (((JF.toFrame.xstar N0 : ℝ) : ℂ)).im = 0 := by simp
  have := integrableOn_ray (σ := σ) (f := f) (p := ((JF.toFrame.xstar N0 : ℝ) : ℂ))
    (d := Complex.exp ((θ : ℂ) * I)) (by rw [hv, mul_zero]) hd hK hdec
    (fun u hu => (diffAt_of_mem (diskR_pos hC) hfH hfB
      (ray_mem (diskR_pos hC) (Or.inl rfl) hd hv hu)).continuousAt)
  exact this

lemma rayI_add_of {x θ : ℝ} (f g : ℂ → ℂ)
    (hf : IntegrableOn (fun r : ℝ => f (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0))
    (hg : IntegrableOn (fun r : ℝ => g (rayPt x θ r) * exp ((θ : ℂ) * I)) (Ioi 0)) :
    rayI x θ (fun z => f z + g z) = rayI x θ f + rayI x θ g := by
  unfold rayI
  rw [← integral_add hf hg]
  congr 1
  funext r
  ring

lemma rayI_congr_pos {x θ : ℝ} {f g : ℂ → ℂ} (h : ∀ r : ℝ, 0 < r → f (rayPt x θ r) = g (rayPt x θ r)) :
    rayI x θ f = rayI x θ g := by
  unfold rayI
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  simp only [h r hr]

/-- The ray integral of `E_b v_a v_b` with the series equals the one with the closed form. -/
theorem rayI_E2_eq_srcB (x θ : ℝ) (hs : Real.sin θ ≠ 0) (a b : ℕ) :
    rayI x θ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹)) = rayI x θ (JF.srcB a b) := by
  refine rayI_congr_pos (fun r hr => ?_)
  have him : (rayPt x θ r).im ≠ 0 := by
    rw [rayPt_im]; exact mul_ne_zero hr.ne' hs
  simp only [srcB, E2_eq_E2cf JF him]

/-- **The jet contour identity on the two reference rays**:
`∑' m, (atomSum + atomBSum) = head + (1/2πi) ∫_Γ (E_a + E_b) v_a v_b dz`. -/
theorem contour_identityJ (hC : JF.toFrame.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ)
    (h2 : φ < Real.pi) (N0 a b : ℕ) :
    ((∑' m : ℕ, JF.toFrame.atomSum a b m : ℝ) : ℂ) + ((∑' m : ℕ, JF.atomBSum a b m : ℝ) : ℂ)
      = ((JF.toFrame.atomHead N0 a b : ℝ) : ℂ) + ((JF.atomHeadB N0 a b : ℝ) : ℂ) +
        (2 * Real.pi * I)⁻¹ * contL (JF.toFrame.xstar N0) φ (JF.srcJ a b) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hA := CatalanCore.Frame.contour_identity hC h1 h2 N0 a b
  have hB := contour_identityB JF hC h1 h2 N0 a b
  have hBc : contL (JF.toFrame.xstar N0) φ (fun z => JF.E2 z * ((z - a)⁻¹ * (z - b)⁻¹))
      = contL (JF.toFrame.xstar N0) φ (JF.srcB a b) := by
    unfold contL
    rw [rayI_E2_eq_srcB JF _ _ hsφ', rayI_E2_eq_srcB JF _ _ hsφ]
  rw [hBc] at hB
  -- integrability of the two summands on both rays
  have hsin1 : 0 < (1 : ℝ) * Real.sin φ := by rw [one_mul]; exact Real.sin_pos_of_pos_of_lt_pi (by linarith) h2
  have hsin2 : 0 < (-1 : ℝ) * Real.sin (-φ) := by
    rw [Real.sin_neg]; nlinarith [Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < φ) h2]
  have iA1 := integrableOn_src_ray JF hC N0 (f := srcF JF.toFrame a b) (σ := 1) (θ := φ)
    (Polygon.srcF_differentiableOn_halfP 1 a b) (Polygon.srcF_differentiableOn_ball hC N0 a b)
    hsin1 Khi_nonneg (Polygon.srcF_decay (by simp) a b)
  have iA2 := integrableOn_src_ray JF hC N0 (f := srcF JF.toFrame a b) (σ := -1) (θ := -φ)
    (Polygon.srcF_differentiableOn_halfP (-1) a b) (Polygon.srcF_differentiableOn_ball hC N0 a b)
    hsin2 Khi_nonneg (Polygon.srcF_decay (by simp) a b)
  have iB1 := integrableOn_src_ray JF hC N0 (f := JF.srcB a b) (σ := 1) (θ := φ)
    (srcB_differentiableOn_halfP JF 1 a b) (srcB_differentiableOn_ball JF hC N0 a b)
    hsin1 (KhiB_nonneg JF) (srcB_decay JF (by simp) a b)
  have iB2 := integrableOn_src_ray JF hC N0 (f := JF.srcB a b) (σ := -1) (θ := -φ)
    (srcB_differentiableOn_halfP JF (-1) a b) (srcB_differentiableOn_ball JF hC N0 a b)
    hsin2 (KhiB_nonneg JF) (srcB_decay JF (by simp) a b)
  have hlin : contL (JF.toFrame.xstar N0) φ (JF.srcJ a b)
      = contL (JF.toFrame.xstar N0) φ (srcF JF.toFrame a b)
        + contL (JF.toFrame.xstar N0) φ (JF.srcB a b) := by
    unfold contL srcJ
    rw [rayI_add_of _ _ iA1 iB1, rayI_add_of _ _ iA2 iB2]
    ring
  rw [hlin, mul_add]
  have hA' : ((∑' m : ℕ, JF.toFrame.atomSum a b m : ℝ) : ℂ) = ((JF.toFrame.atomHead N0 a b : ℝ) : ℂ) +
      (2 * Real.pi * I)⁻¹ * contL (JF.toFrame.xstar N0) φ (srcF JF.toFrame a b) := hA
  rw [hA', hB]
  ring

/-- The closed form of the jet reflection term: `E_a + E_b = -π ∑ a_i cot π(z+s_i) + π² ∑ b_i / sin² π(z+s_i)`
(off the real poles; `Polygon.ecot` is the cotangent form of `E_a`). -/
theorem EJ_closed {z : ℂ} (hz : z ∈ poleFree JF.toFrame) :
    JF.toFrame.EC z + JF.E2cf z = Polygon.ecot JF.toFrame z + JF.E2cf z := by
  rw [Polygon.EC_eq_ecot hz]

/-! ### The polygon identity -/

/-- **Polygon contour identity for jets.**  For every upper polygon `x* → pts → tail d` and all natural
nodes `a, b` (including `a = b`):
`norm · Φ[a,b]/norm = head + (1/2πi) (∫_{lower polygon} - ∫_{upper polygon}) (E_a + E_b) v_a v_b dz`,
where the head is the sum of `atomR + atomB` over the poles right of `x*`. -/
theorem polygon_contour_identityJ (hC : JF.toFrame.ContourOK) (N0 a b : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    (((JF.norm : ℝ) * JF.TentJ a b : ℝ) : ℂ)
      = ((JF.toFrame.atomHead N0 a b + JF.atomHeadB N0 a b : ℝ) : ℂ) + (2 * Real.pi * I)⁻¹ *
          (polyI (JF.srcJ a b) ((JF.toFrame.xstar N0 : ℝ) : ℂ) (pts.map (starRingEnd ℂ))
              (starRingEnd ℂ d)
            - polyI (JF.srcJ a b) ((JF.toFrame.xstar N0 : ℝ) : ℂ) pts d) := by
  rw [upper_deformJ JF hC N0 a b pts hpts hd, lower_deformJ JF hC N0 a b pts hpts hd]
  have h := contour_identityJ JF hC phiRef_gt phiRef_lt N0 a b
  have hN : (((JF.norm : ℝ) * JF.TentJ a b : ℝ) : ℂ) = ((∑' m : ℕ, JF.toFrame.atomSum a b m : ℝ) : ℂ)
      + ((∑' m : ℕ, JF.atomBSum a b m : ℝ) : ℂ) := by
    unfold TentJ
    rw [mul_add, CatalanCore.Frame.norm_mul_Tent, norm_mul_TentB, Complex.ofReal_add]
  rw [hN, h, Complex.ofReal_add]
  simp only [contL]

end JetFrame

open CatalanCore.Uniform.Decay.Polygon (polyI srcF)

/-! ### Lemma 6.2: the Gram formula in the paper's form -/

/-- `k(z) = 1 / ((z-x)(z-y))`. -/
noncomputable def kk (x y : ℕ) (z : ℂ) : ℂ := (z - x)⁻¹ * (z - y)⁻¹

/-- `k'(z) = (x + y - 2z) / ((z-x)²(z-y)²)`. -/
noncomputable def dkk (x y : ℕ) (z : ℂ) : ℂ := ((x : ℂ) + y - 2 * z) / ((z - x) ^ 2 * (z - y) ^ 2)

theorem hasDerivAt_kk (x y : ℕ) {z : ℂ} (hx : z - (x : ℂ) ≠ 0) (hy : z - (y : ℂ) ≠ 0) :
    HasDerivAt (kk x y) (dkk x y z) z := by
  have h1 : HasDerivAt (fun w : ℂ => w - (x : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
  have h2 : HasDerivAt (fun w : ℂ => w - (y : ℂ)) 1 z := (hasDerivAt_id z).sub_const _
  refine ((h1.inv hx).mul (h2.inv hy)).congr_deriv ?_
  simp only [Pi.inv_apply]
  unfold dkk
  field_simp
  ring

namespace JetFrame

variable (JF : JetFrame)

/-- The head sum of Lemma 6.2: `∑ (a_s k - b_s k')(x_{s,n})` over the poles `x_{s,n} = -s-n` right of
the vertex `x* = -N0 - xs`. -/
noncomputable def headSum (N0 x y : ℕ) : ℂ :=
  ∑ m ∈ range (N0 + ⌈(JF.xs : ℝ)⌉₊), ∑ i,
    if (N0 : ℝ) + (JF.xs : ℝ) < (m : ℝ) + (JF.μ i : ℝ) then 0
    else (JF.w i : ℂ) * kk x y (-(m : ℂ) - (JF.μ i : ℂ)) - (JF.b i : ℂ) * dkk x y (-(m : ℂ) - (JF.μ i : ℂ))

theorem headSum_eq (N0 x y : ℕ) :
    JF.headSum N0 x y = ((JF.toFrame.atomHead N0 x y + JF.atomHeadB N0 x y : ℝ) : ℂ) := by
  unfold headSum CatalanCore.Frame.atomHead atomHeadB CatalanCore.Frame.headTerm headTermB
  push_cast
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hlt : (N0 : ℝ) + (JF.xs : ℝ) < (m : ℝ) + (JF.μ i : ℝ)
  · simp [hlt]
  · simp only [hlt, if_false]
    have hμ := JF.mu_pos i
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hx : (0 : ℝ) ≤ x := Nat.cast_nonneg x
    have hy : (0 : ℝ) ≤ y := Nat.cast_nonneg y
    have p1 : (x : ℝ) + m + JF.μ i ≠ 0 := by positivity
    have p2 : (y : ℝ) + m + JF.μ i ≠ 0 := by positivity
    have c1 : (x : ℂ) + m + (JF.μ i : ℂ) ≠ 0 := by exact_mod_cast p1
    have c2 : (y : ℂ) + m + (JF.μ i : ℂ) ≠ 0 := by exact_mod_cast p2
    unfold CatalanCore.Frame.atomR atomB kk dkk
    push_cast
    have e1 : (-(m : ℂ) - (JF.μ i : ℂ) - (x : ℂ)) = -((x : ℂ) + m + (JF.μ i : ℂ)) := by ring
    have e2 : (-(m : ℂ) - (JF.μ i : ℂ) - (y : ℂ)) = -((y : ℂ) + m + (JF.μ i : ℂ)) := by ring
    rw [e1, e2]
    field_simp
    ring

/-- **Lemma 6.2 (Gram formula for jets).**  Let `F = ∑_s [a_s ψ(z+s) + b_s ψ'(z+s)]`, `∑ a_s = 0`,
`E = -π ∑ a_s cot π(z+s) + π² ∑ b_s / sin² π(z+s)`, `Φ(ξ)` its Loewner matrix on `ℕ` (`norm · TentJ`), and
`Γ` an upper polygon `x* → pts → tail d` with its conjugate.  For `k(z) = 1/((z-x)(z-y))`, `x, y ∈ ℕ`,

  `Φ(ξ)[x,y] = (2πi)⁻¹ ∫_Γ k E dz - ∑_{s,n} (b_s k'(x_{s,n}) - a_s k(x_{s,n}))`,

the heads `x_{s,n} = -s-n` being the poles right of `x*`.  The orientation of `Γ` is the one of
`Frame.contour_identity`: `∫_Γ = ∫_{lower} - ∫_{upper}`. -/
theorem gram_formula (hC : JF.toFrame.ContourOK) (N0 x y : ℕ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < z.im) {d : ℂ} (hd : 0 < d.im) :
    (((JF.norm : ℝ) * JF.TentJ x y : ℝ) : ℂ)
      = JF.headSum N0 x y + (2 * Real.pi * I)⁻¹ *
          (polyI (fun z => (JF.toFrame.EC z + JF.E2cf z) * kk x y z)
              ((JF.toFrame.xstar N0 : ℝ) : ℂ) (pts.map (starRingEnd ℂ)) (starRingEnd ℂ d)
            - polyI (fun z => (JF.toFrame.EC z + JF.E2cf z) * kk x y z)
              ((JF.toFrame.xstar N0 : ℝ) : ℂ) pts d) := by
  rw [headSum_eq, polygon_contour_identityJ JF hC N0 x y pts hpts hd]
  have e : (fun z : ℂ => (JF.toFrame.EC z + JF.E2cf z) * kk x y z) = JF.srcJ x y := by
    funext z; unfold srcJ srcB kk srcF; ring
  rw [e]

/-- `norm · TentJ` is the Loewner entry `Φ(ξ)[x,y]` of the jet: for `x ≠ y` it is
`(f_y - f_x)/(y - x)` with `f_t = ∑_{k<t} δ(k)`, and on the diagonal `F'(x) = ξ - e_x`. -/
theorem norm_mul_TentJ_offdiag {x y : ℕ} (hxy : x ≠ y) :
    ((JF.norm : ℝ) * JF.TentJ x y : ℝ) =
      (1 / (((max x y : ℕ) : ℝ) - ((min x y : ℕ) : ℝ))) *
        ∑ k ∈ Ioc (min x y) (max x y), (((JF.toFrame.Delta k + JF.DeltaB k : ℚ)) : ℝ) := by
  have hn : (JF.norm : ℝ) ≠ 0 := by exact_mod_cast JF.hnorm.ne'
  unfold TentJ TentB CatalanCore.Frame.Tent CatalanCore.Frame.Mn MnB
  simp only [if_neg hxy, zero_add]
  have hne : (max (x : ℝ) y - min (x : ℝ) y) ≠ 0 := by
    rcases lt_or_gt_of_ne hxy with h | h
    · have h' : (x : ℝ) < y := by exact_mod_cast h
      rw [max_eq_right h'.le, min_eq_left h'.le]; linarith
    · have h' : (y : ℝ) < x := by exact_mod_cast h
      rw [max_eq_left h'.le, min_eq_right h'.le]; linarith
  push_cast
  rw [Finset.sum_add_distrib]
  field_simp

theorem norm_mul_TentJ_diag (x : ℕ) :
    ((JF.norm : ℝ) * JF.TentJ x x : ℝ) =
      ((JF.norm : ℝ) * (JF.toFrame.const + JF.constB))
        - ∑ k ∈ Icc 1 x, (((JF.toFrame.Dsq k + JF.DsqB k : ℚ)) : ℝ) := by
  have hn : (JF.norm : ℝ) ≠ 0 := by exact_mod_cast JF.hnorm.ne'
  unfold TentJ TentB CatalanCore.Frame.Tent CatalanCore.Frame.Mn MnB
  simp only [↓reduceIte]
  push_cast
  rw [Finset.sum_add_distrib]
  field_simp
  ring

end JetFrame

/-! ### Lemma 6.3: the rank-one split at a double head -/

/-- **Lemma 6.3 (rank-one split), algebraic form.**  With `â = a' - (a_s/2b) a`, `ĉ = c' - (a_s/2b) c`:
`-b (a c)' + a_s a c = -(b/2) [(a + â)(c + ĉ) - (a - â)(c - ĉ)]`, `(a c)' = a c' + a' c`. -/
theorem rank_one_split {K : Type*} [Field K] (a c a' c' as b : K) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0) :
    -b * (a * c' + a' * c) + as * (a * c)
      = -(b / 2) * ((a + (a' - as / (2 * b) * a)) * (c + (c' - as / (2 * b) * c))
          - (a - (a' - as / (2 * b) * a)) * (c - (c' - as / (2 * b) * c))) := by
  field_simp
  ring

/-- The one-point factor `u_x(p) = 1/(p - x)` of `k = u_x u_y`, and its derivative. -/
noncomputable def ux (x : ℕ) (p : ℂ) : ℂ := (p - x)⁻¹

noncomputable def dux (x : ℕ) (p : ℂ) : ℂ := -((p - x)⁻¹ * (p - x)⁻¹)

theorem dkk_eq (x y : ℕ) {p : ℂ} (hx : p - (x : ℂ) ≠ 0) (hy : p - (y : ℂ) ≠ 0) :
    dkk x y p = ux x p * dux y p + dux x p * ux y p := by
  unfold dkk ux dux
  field_simp
  ring

theorem kk_eq (x y : ℕ) (p : ℂ) : kk x y p = ux x p * ux y p := rfl

/-- At a double head `p = -s-n` (simple weight `a_s`, double weight `b_s ≠ 0`) the head term of Lemma 6.2
is a difference of two rank-one terms: with `û_x = u_x' - (a_s/2b_s) u_x`,

`a_s k(p) - b_s k'(p) = -(b_s/2) [(u_x + û_x)(u_y + û_y) - (u_x - û_x)(u_y - û_y)]`.

So the form of Lemma 6.2 is a sum, over the parameter space of the jet, of rank-one terms: a double head
gives the two labels `(s,n)`, `(s*,n)` with weights `∓ b_s/2`, a simple head one. -/
theorem head_term_split (x y : ℕ) {p : ℂ} (hx : p - (x : ℂ) ≠ 0) (hy : p - (y : ℂ) ≠ 0)
    (as bs : ℂ) (hb : bs ≠ 0) :
    as * kk x y p - bs * dkk x y p
      = -(bs / 2) *
        ((ux x p + (dux x p - as / (2 * bs) * ux x p)) * (ux y p + (dux y p - as / (2 * bs) * ux y p))
          - (ux x p - (dux x p - as / (2 * bs) * ux x p)) *
            (ux y p - (dux y p - as / (2 * bs) * ux y p))) := by
  have h := rank_one_split (ux x p) (ux y p) (dux x p) (dux y p) as bs hb (two_ne_zero)
  rw [kk_eq, dkk_eq x y hx hy]
  linear_combination h

end CatalanCore.Uniform.Decay.Jet

#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.norm_mul_TentB
#print axioms CatalanCore.Uniform.Decay.Jet.contL_g4
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.contour_identityJ
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.polygon_contour_identityJ
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.gram_formula
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.headSum_eq
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.norm_mul_TentJ_offdiag
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.norm_mul_TentJ_diag
#print axioms CatalanCore.Uniform.Decay.Jet.rank_one_split
#print axioms CatalanCore.Uniform.Decay.Jet.head_term_split
#print axioms CatalanCore.Uniform.Decay.Jet.hasDerivAt_kk
#print axioms CatalanCore.Uniform.Decay.Jet.JetFrame.EJ_closed



/-! ### Arbitrary-order rational head forms (Q03, frozen shared layer) -/

namespace CatalanCore.Uniform.Support

open Finset Matrix

/-- A rational rank-one split, allowing arbitrary overcomplete/zero-weight padding. -/
structure PoleGramSplit (D : PoleDatum) where
  J : ℕ
  order_le : ∀ i, D.w i ≤ J + 1
  count : Fin D.n → ℕ
  weight : ((i : Fin D.n) × Fin (count i)) → ℚ
  coeff : ((i : Fin D.n) × Fin (count i)) → Fin (J + 1) → ℚ
  split : ∀ (i : Fin D.n) (j k : Fin (J + 1)),
    D.coeff i ((j : ℕ) + (k : ℕ) + 1) /
        ((j : ℕ).factorial * (k : ℕ).factorial : ℚ) =
      ∑ q : Fin (count i), weight ⟨i, q⟩ * coeff ⟨i, q⟩ j * coeff ⟨i, q⟩ k

abbrev PoleGramSplit.Role {D : PoleDatum} (S : PoleGramSplit D) :=
  (i : Fin D.n) × Fin (S.count i)

structure PoleRefMatch (D : PoleDatum) (S : PoleGramSplit D) (Fr : Frame) where
  role : Fin Fr.d ≃ S.Role
  side : ∀ (N0 m : ℕ) (q : Fin Fr.d), S.weight (role q) ≠ 0 →
    (((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ q : ℝ)) ↔
      ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (D.s (role q).1 : ℝ)))

/-- The head form in unnormalized derivative rows. -/
def PoleDatum.headMatrix (D : PoleDatum) (i : Fin D.n) :
    Matrix (Fin (D.w i)) (Fin (D.w i)) ℚ :=
  fun j k => D.coeff i ((j : ℕ) + (k : ℕ) + 1) /
    ((j : ℕ).factorial * (k : ℕ).factorial : ℚ)

theorem PoleDatum.headMatrix_symm (D : PoleDatum) (i : Fin D.n) :
    (D.headMatrix i).IsSymm := by
  ext j k
  simp [PoleDatum.headMatrix, Nat.add_comm, mul_comm]

theorem PoleDatum.headMatrix_det_ne (D : PoleDatum) (i : Fin D.n) :
    (D.headMatrix i).det ≠ 0 := by
  classical
  let M := D.headMatrix i
  have ht : (M.submatrix id Fin.revPerm).IsUpperTriangular := by
    intro j k hkj
    have hj := j.isLt
    have hk := k.isLt
    have hcoeff : D.w i < (j : ℕ) + ((Fin.revPerm k : Fin (D.w i)) : ℕ) + 1 := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have hkj' : (k : ℕ) < j := hkj
      omega
    simp only [Matrix.submatrix_apply, id_eq, M, PoleDatum.headMatrix,
      D.coeff_above i _ hcoeff, zero_div]
  have hn : (M.submatrix id Fin.revPerm).det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular ht]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have he : (j : ℕ) + ((Fin.revPerm j : Fin (D.w i)) : ℕ) + 1 = D.w i := by
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have := j.isLt
      omega
    change D.coeff i _ / _ ≠ 0
    simp only [id_eq]
    rw [he]
    exact div_ne_zero (D.top_ne i) (mul_ne_zero
      (by exact_mod_cast Nat.factorial_ne_zero (j : ℕ))
      (by exact_mod_cast Nat.factorial_ne_zero ((Fin.revPerm j : Fin (D.w i)) : ℕ)))
  intro h
  apply hn
  rw [Matrix.det_permute', h, mul_zero]

/-- Every nondegenerate rational symmetric form has a split with exactly its dimension
many nonzero rational weights. The orthogonal basis is independent of the source/certificate. -/
theorem rational_rank_one_split {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (hs : M.IsSymm) (hd : M.det ≠ 0) :
    ∃ w : Fin n → ℚ, ∃ a : Fin n → Fin n → ℚ,
      (∀ q, w q ≠ 0) ∧ ∀ j k, M j k = ∑ q, w q * a q j * a q k := by
  classical
  let B := M.toBilin'
  letI : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  have hBs : B.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hs
  have hBd : B.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hd
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin n) ℚ (Fin n → ℚ), B.IsOrthoᵢ b := by
    obtain ⟨b0, hb0⟩ := LinearMap.BilinForm.exists_orthogonal_basis
      (LinearMap.BilinForm.isSymm_iff.mp hBs)
    have hn : Module.finrank ℚ (Fin n → ℚ) = n :=
      Module.finrank_fin_fun (R := ℚ)
    let e : Fin (Module.finrank ℚ (Fin n → ℚ)) ≃ Fin n := finCongr hn
    refine ⟨b0.reindex e, ?_⟩
    apply LinearMap.BilinForm.iIsOrtho_def.mpr
    intro i j hij
    simp only [Module.Basis.reindex_apply]
    exact (LinearMap.BilinForm.iIsOrtho_def.mp hb0) (e.symm i) (e.symm j)
      (fun he => hij (e.symm.injective he))
  have horth : ∀ q v, q ≠ v → B (b q) (b v) = 0 :=
    LinearMap.BilinForm.iIsOrtho_def.mp hb
  refine ⟨fun q => B (b q) (b q), fun q j => b.repr (Pi.single j 1) q, ?_, ?_⟩
  · exact LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate hb hBd
  · intro j k
    calc
      M j k = B (Pi.single j 1) (Pi.single k 1) := (Matrix.toBilin'_single M j k).symm
      _ = B (∑ q, b.repr (Pi.single j 1) q • b q)
          (∑ v, b.repr (Pi.single k 1) v • b v) := by rw [b.sum_repr, b.sum_repr]
      _ = _ := by
        rw [LinearMap.BilinForm.sum_left]
        apply Finset.sum_congr rfl
        intro q _
        rw [LinearMap.BilinForm.sum_right]
        simp only [LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
        rw [Finset.sum_eq_single q]
        · ring
        · intro v _ hv
          rw [horth q v hv.symm]
          ring
        · intro hq
          exact False.elim (hq (mem_univ q))

/-- Minimal label count exists; other source adapters may still use padded splits. -/
theorem pole_gram_split_minimal (D : PoleDatum) :
    ∃ S : PoleGramSplit D, (∀ i, S.count i = D.w i) ∧ (∀ q, S.weight q ≠ 0) := by
  classical
  choose w a hw ha using fun i =>
    rational_rank_one_split (D.headMatrix i) (D.headMatrix_symm i) (D.headMatrix_det_ne i)
  let S : PoleGramSplit D := {
    J := D.d
    order_le := fun i => (Finset.single_le_sum (f := D.w)
      (fun _ _ => Nat.zero_le _) (mem_univ i)).trans (Nat.le_succ D.d)
    count := D.w
    weight := fun q => w q.1 q.2
    coeff := fun q j => if hj : (j : ℕ) < D.w q.1 then a q.1 q.2 ⟨j, hj⟩ else 0
    split := by
      intro i j k
      by_cases hj : (j : ℕ) < D.w i
      · by_cases hk : (k : ℕ) < D.w i
        · simpa only [PoleDatum.headMatrix, dif_pos hj, dif_pos hk] using ha i ⟨j, hj⟩ ⟨k, hk⟩
        · rw [D.coeff_above i _ (by omega)]
          simp [hk]
      · rw [D.coeff_above i _ (by omega)]
        simp [hj]
  }
  exact ⟨S, fun _ => rfl, fun q => hw q.1 q.2⟩

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.pole_gram_split_minimal
