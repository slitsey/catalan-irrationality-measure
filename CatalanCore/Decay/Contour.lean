module

public import CatalanCore.Decay.Reflect
public import CatalanLambda.Decay.RayFTC

@[expose] public section

/-!
# The contour identity for a general Loewner frame (WP2a)

**Contour convention (fixed here; resolves WP0 deviation 2).**  The contour vertex is
`x* = -N0 - xs` with `xs = Fr.xs`.  The real poles of `E` (= atoms of `F`) are
`-(n + μ_i)`, `n ∈ ℤ`; the distance from `x*` to the pole `-(n + μ_i)` is
`|(N0 - n) + μ_i - xs|`, so `Frame.ContourGap` (`δ0 ≤ |k + μ_i - xs|` for all `k ∈ ℤ`)
says exactly that `x*` keeps distance `δ0` from every real pole, whatever `N0` is.  Instances:

| frame        | μ                | xs   | x*          | δ0  |
|--------------|------------------|------|-------------|-----|
| λ (legacy)   | `![3/4, 1]`      | 3/8  | `-N0 - 3/8` | 3/8 |
| λ' (mirror)  | `![1/4, 1]`      | 5/8  | `-N0 - 5/8` | 3/8 |
| P6           | `![1, 1/3, 1/2]` | 3/4  | `-N0 - 3/4` | 1/4 |

(The legacy mirror code uses `x* = -N0' + 3/8`; this is `xs = 5/8` with `N0 = N0' - 1`.
The value `xs = 5/8` for λ in design 2.2 is the mirror's.)  We also assume `0 < xs`; no other
property of `xs` is needed.  `ContourOK` bundles the two hypotheses.

**Atoms.**  `atomR i a b t = w_i / ((a + t + μ_i)(b + t + μ_i))`,
`atomSum a b m = ∑_i atomR i a b m`.  (For λ, `atomSum = -atomTerm` of the legacy code, and
`16 T_{ab} = ∑' atomSum`, which is `T_eq_atoms` of WP2b.)  The atoms split at `x*` into the
`head` (poles to the right of `x*`) and the `tail` (poles to the left, enclosed by the contour):
```
∑' m, atomSum a b m = atomHead N0 a b + (1/2πi) ∫_Γ E(z) (z-a)⁻¹ (z-b)⁻¹ dz.
```
For λ and mirror, `atomHead = ∑_{m < N0} atomSum` (resp. `N0 + 1`); for P6 the head has the extra
terms of the `μ_i ≤ xs` families, which `atomHead` handles uniformly.

**Imports.**  The ray-integral calculus (`rayPt`, `rayI`, `contL`, `contL_tri_west/east`,
distance bounds) is imported from the legacy `CatalanLambda.Decay.RayFTC` (frame-free; it is
moved to `CatalanCore/Analysis/Potential` at cut-over, WP15).
-/

open Complex MeasureTheory Filter Topology Set Finset
open CatalanLambda.Decay (rayPt rayI contL kap2 kap2_pos norm_inv_rayPt_le integrableOn_ray3
  integrableOn_invsq rayPt_sub_ne contL_tri_west contL_tri_east)

namespace CatalanCore
namespace Frame

variable (Fr : Frame)

/-- The two convention hypotheses on the contour abscissa. -/
structure ContourOK : Prop where
  xs_pos : (0 : ℚ) < Fr.xs
  gap : Fr.ContourGap

/-- The contour vertex `x* = -N0 - xs`. -/
noncomputable def xstar (N0 : ℕ) : ℝ := -(N0 : ℝ) - (Fr.xs : ℝ)

/-- Reference shift used only to bound `eterm` uniformly on rays (a fake pole at distance ≥ 1/2). -/
noncomputable def cref : ℝ := (Fr.xs : ℝ) + 1 / 2

/-- Atom of family `i`, evaluated at the real index `t`. -/
noncomputable def atomR (i : Fin Fr.d) (a b : ℕ) (t : ℝ) : ℝ :=
  (Fr.w i : ℝ) / (((a : ℝ) + t + (Fr.μ i : ℝ)) * ((b : ℝ) + t + (Fr.μ i : ℝ)))

/-- `atomSum a b m = ∑_i w_i / ((a+m+μ_i)(b+m+μ_i))`. -/
noncomputable def atomSum (a b m : ℕ) : ℝ := ∑ i, Fr.atomR i a b (m : ℝ)

/-- The atoms at index `t` whose pole lies to the left of `x*` (enclosed). -/
noncomputable def tailTerm (N0 a b : ℕ) (t : ℝ) : ℝ :=
  ∑ i, if (N0 : ℝ) + (Fr.xs : ℝ) < t + (Fr.μ i : ℝ) then Fr.atomR i a b t else 0

/-- The atoms at index `t` whose pole lies to the right of `x*` (not enclosed). -/
noncomputable def headTerm (N0 a b : ℕ) (t : ℝ) : ℝ :=
  ∑ i, if (N0 : ℝ) + (Fr.xs : ℝ) < t + (Fr.μ i : ℝ) then 0 else Fr.atomR i a b t

/-- The finite head: all atoms with a pole to the right of `x*`. -/
noncomputable def atomHead (N0 a b : ℕ) : ℝ :=
  ∑ m ∈ range (N0 + ⌈(Fr.xs : ℝ)⌉₊), Fr.headTerm N0 a b (m : ℝ)

variable {Fr}

lemma xstar_lt_nat (hC : Fr.ContourOK) (N0 a : ℕ) : Fr.xstar N0 < a := by
  have : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have := Nat.cast_nonneg (α := ℝ) a
  have := Nat.cast_nonneg (α := ℝ) N0
  unfold xstar; linarith

lemma xs_le_dist (hC : Fr.ContourOK) (N0 a : ℕ) : (Fr.xs : ℝ) ≤ |Fr.xstar N0 - a| := by
  have := Nat.cast_nonneg (α := ℝ) a
  have := Nat.cast_nonneg (α := ℝ) N0
  have hx := xstar_lt_nat hC N0 a
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  unfold xstar; linarith

lemma pole_ne (hC : Fr.ContourOK) (N0 : ℕ) (n : ℤ) (i : Fin Fr.d) :
    (-(n : ℝ) - (Fr.μ i : ℝ)) ≠ Fr.xstar N0 := by
  intro h
  have hg := hC.gap.2 i (n - N0)
  have hpos := hC.gap.1
  have h0 : (((n - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs) = 0 := by
    have : ((((n - (N0 : ℤ) : ℤ) : ℚ) + Fr.μ i - Fr.xs : ℚ) : ℝ) = 0 := by
      push_cast; unfold xstar at h; linarith
    exact_mod_cast this
  rw [h0, abs_zero] at hg
  exact absurd hg (not_le.2 hpos)

lemma cref_ne (N0 : ℕ) (n : ℤ) : (-(n : ℝ) - Fr.cref) ≠ Fr.xstar N0 := by
  intro h
  unfold xstar cref at h
  have h2 : (2 * n + 1 : ℤ) = 2 * N0 := by
    have : (2 * (n : ℝ) + 1) = 2 * (N0 : ℝ) := by linarith
    exact_mod_cast this
  omega

/-! ### The integrand as a sum of simple-pole cubics -/

/-- `g3F p a b z = (z-p)⁻¹ (z-a)⁻¹ (z-b)⁻¹`. -/
noncomputable def g3F (p a b : ℝ) (z : ℂ) : ℂ := (z - p)⁻¹ * (z - a)⁻¹ * (z - b)⁻¹

lemma eterm_mul_eq (z : ℂ) (n : ℤ) (a b : ℕ) :
    Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)
      = ∑ i, (-(Fr.w i : ℂ)) * g3F (-(n : ℝ) - (Fr.μ i : ℝ)) a b z := by
  unfold eterm g3F
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring

lemma rayI_sum_g3 {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ι → ℝ) {x θ : ℝ} (a b : ℝ)
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) (hs : Real.sin θ ≠ 0) :
    rayI x θ (fun z => ∑ i ∈ s, c i * g3F (p i) a b z)
      = ∑ i ∈ s, c i * rayI x θ (g3F (p i) a b) := by
  unfold rayI
  have hint : ∀ i ∈ s, Integrable
      (fun r : ℝ => c i * (g3F (p i) a b (rayPt x θ r) * exp ((θ : ℂ) * I)))
      (volume.restrict (Ioi 0)) := fun i hi =>
    (integrableOn_ray3 (p i) a b (hp i hi) ha hb hs).const_mul (c i)
  have e : ∀ r : ℝ, (∑ i ∈ s, c i * g3F (p i) a b (rayPt x θ r)) * exp ((θ : ℂ) * I)
      = ∑ i ∈ s, c i * (g3F (p i) a b (rayPt x θ r) * exp ((θ : ℂ) * I)) := by
    intro r; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [e]
  rw [integral_finset_sum s hint]
  exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

lemma contL_sum_g3 {ι : Type*} (s : Finset ι) (c : ι → ℂ) (p : ι → ℝ) {x φ : ℝ} (a b : ℝ)
    (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (hp : ∀ i ∈ s, p i ≠ x) (ha : a ≠ x) (hb : b ≠ x) :
    contL x φ (fun z => ∑ i ∈ s, c i * g3F (p i) a b z)
      = ∑ i ∈ s, c i * contL x φ (g3F (p i) a b) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  unfold contL
  rw [rayI_sum_g3 s c p a b hp ha hb hsφ, rayI_sum_g3 s c p a b hp ha hb hsφ',
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **Value of the contour integral of one term.**  Only poles to the left of `x*` contribute:
`contL (e_n v_a v_b) = 2πi ∑_i [pole_i left of x*] w_i / ((a+n+μ_i)(b+n+μ_i))`. -/
theorem contL_eterm (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (N0 a b : ℕ) (n : ℤ) :
    contL (Fr.xstar N0) φ (fun z => Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = 2 * Real.pi * I * ((Fr.tailTerm N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) := by
  have hfun : (fun z : ℂ => Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))
      = fun z => ∑ i, (-(Fr.w i : ℂ)) * g3F (-(n : ℝ) - (Fr.μ i : ℝ)) a b z := by
    funext z; exact eterm_mul_eq z n a b
  rw [hfun, contL_sum_g3 Finset.univ (fun i => -(Fr.w i : ℂ)) (fun i => -(n : ℝ) - (Fr.μ i : ℝ))
    (a : ℝ) (b : ℝ) h1 h2 (fun i _ => pole_ne hC N0 n i)
    (xstar_lt_nat hC N0 a).ne' (xstar_lt_nat hC N0 b).ne']
  unfold tailTerm atomR
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hxa := xstar_lt_nat hC N0 a
  have hxb := xstar_lt_nat hC N0 b
  by_cases hlt : (N0 : ℝ) + (Fr.xs : ℝ) < (n : ℝ) + (Fr.μ i : ℝ)
  · have hp : (-(n : ℝ) - (Fr.μ i : ℝ)) < Fr.xstar N0 := by unfold xstar; linarith
    unfold g3F
    rw [contL_tri_west _ _ _ _ _ h1 h2 hp hxa hxb, if_pos (by exact_mod_cast hlt)]
    push_cast
    have hQ : ((-(n : ℂ) - (Fr.μ i : ℂ)) - (a : ℂ)) * ((-(n : ℂ) - (Fr.μ i : ℂ)) - (b : ℂ))
        = ((a : ℂ) + n + (Fr.μ i : ℂ)) * ((b : ℂ) + n + (Fr.μ i : ℂ)) := by ring
    rw [hQ]
    ring
  · have hp : Fr.xstar N0 < (-(n : ℝ) - (Fr.μ i : ℝ)) := by
      unfold xstar; push_neg at hlt;
      have := pole_ne hC N0 n i
      have h3 : (-(n : ℝ) - (Fr.μ i : ℝ)) ≠ -(N0 : ℝ) - (Fr.xs : ℝ) := this
      rcases lt_or_gt_of_ne h3 with h4 | h4
      · linarith
      · exact h4
    unfold g3F
    rw [contL_tri_east _ _ _ _ _ h1 h2 hp hxa hxb, if_neg (by exact_mod_cast hlt)]
    simp


/-! ### Uniform domination of the terms along a ray -/

lemma norm_D (z : ℂ) (q1 q2 : ℝ) (h1 : z - (q1 : ℂ) ≠ 0) (h2 : z - (q2 : ℂ) ≠ 0) :
    ‖(z - q1)⁻¹ - (z - q2)⁻¹‖ = |q1 - q2| * (‖(z - q1)⁻¹‖ * ‖(z - q2)⁻¹‖) := by
  have e : (z - q1)⁻¹ - (z - q2)⁻¹ = ((q1 : ℂ) - q2) * ((z - q1)⁻¹ * (z - q2)⁻¹) := by
    field_simp; ring
  rw [e, norm_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

lemma norm_D_ray_le {x θ r : ℝ} (q1 q2 : ℝ) (h1 : q1 ≠ x) (h2 : q2 ≠ x)
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖(rayPt x θ r - q1)⁻¹ - (rayPt x θ r - q2)⁻¹‖
      ≤ ‖((x : ℂ) - q1)⁻¹ - ((x : ℂ) - q2)⁻¹‖ / Real.sqrt (kap2 θ) ^ 2 := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  set K := Real.sqrt (kap2 θ)
  have d1 : 0 < |x - q1| := abs_pos.2 (sub_ne_zero.2 h1.symm)
  have d2 : 0 < |x - q2| := abs_pos.2 (sub_ne_zero.2 h2.symm)
  have hx1 : (x : ℂ) - q1 ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 h1.symm
  have hx2 : (x : ℂ) - q2 ≠ 0 := by
    rw [← Complex.ofReal_sub]; exact_mod_cast sub_ne_zero.2 h2.symm
  rw [norm_D _ q1 q2 (rayPt_sub_ne h1 hs hr) (rayPt_sub_ne h2 hs hr), norm_D _ q1 q2 hx1 hx2]
  have a1 := norm_inv_rayPt_le (x := x) (θ := θ) q1 h1 hs hr
  have a2 := norm_inv_rayPt_le (x := x) (θ := θ) q2 h2 hs hr
  have b1 : ‖((x : ℂ) - q1)⁻¹‖ = 1 / |x - q1| := by
    rw [norm_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_div]
  have b2 : ‖((x : ℂ) - q2)⁻¹‖ = 1 / |x - q2| := by
    rw [norm_inv, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, one_div]
  rw [b1, b2]
  have c1 : 1 / (K * (|x - q1| + r)) ≤ 1 / (K * |x - q1|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have c2 : 1 / (K * (|x - q2| + r)) ≤ 1 / (K * |x - q2|) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hq : 0 ≤ |q1 - q2| := abs_nonneg _
  calc |q1 - q2| * (‖(rayPt x θ r - q1)⁻¹‖ * ‖(rayPt x θ r - q2)⁻¹‖)
      ≤ |q1 - q2| * ((1 / (K * |x - q1|)) * (1 / (K * |x - q2|))) := by
        apply mul_le_mul_of_nonneg_left _ hq
        exact mul_le_mul (a1.trans c1) (a2.trans c2) (norm_nonneg _) (by positivity)
    _ = |q1 - q2| * (1 / |x - q1| * (1 / |x - q2|)) / K ^ 2 := by
        field_simp

/-- The size at the vertex of the `i`-th difference term of `eterm`. -/
noncomputable def Dn (N0 : ℕ) (n : ℤ) (i : Fin Fr.d) : ℝ :=
  ‖(((Fr.xstar N0 : ℝ) : ℂ) - ((-(n : ℝ) - Fr.μ i : ℝ) : ℂ))⁻¹
    - (((Fr.xstar N0 : ℝ) : ℂ) - ((-(n : ℝ) - Fr.cref : ℝ) : ℂ))⁻¹‖

lemma eterm_eq_D (z : ℂ) (n : ℤ) :
    Fr.eterm z n = -∑ i, (Fr.w i : ℂ) *
      ((z - ((-(n : ℝ) - Fr.μ i : ℝ) : ℂ))⁻¹ - (z - ((-(n : ℝ) - Fr.cref : ℝ) : ℂ))⁻¹) := by
  rw [Fr.eterm_eq_pair z n ((Fr.cref : ℝ) : ℂ)]
  refine congrArg Neg.neg (Finset.sum_congr rfl (fun i _ => ?_))
  push_cast
  ring

/-- Dominating sequence for `‖eterm z n‖` along a ray with direction `θ` from `x*`. -/
noncomputable def Bn (N0 : ℕ) (θ : ℝ) (n : ℤ) : ℝ :=
  ∑ i, |(Fr.w i : ℝ)| * (Fr.Dn N0 n i / Real.sqrt (kap2 θ) ^ 2)

lemma norm_eterm_ray_le (hC : Fr.ContourOK) (N0 : ℕ) (n : ℤ) {θ r : ℝ}
    (hs : Real.sin θ ≠ 0) (hr : 0 ≤ r) :
    ‖Fr.eterm (rayPt (Fr.xstar N0) θ r) n‖ ≤ Fr.Bn N0 θ n := by
  rw [eterm_eq_D, norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [norm_mul]
  have : ‖(Fr.w i : ℂ)‖ = |(Fr.w i : ℝ)| := by simp
  rw [this]
  exact mul_le_mul_of_nonneg_left
    (norm_D_ray_le _ _ (pole_ne hC N0 n i) (cref_ne N0 n) hs hr) (abs_nonneg _)

lemma summable_Bn (N0 : ℕ) (θ : ℝ) : Summable (Fr.Bn N0 θ) := by
  unfold Bn
  refine summable_sum (fun i _ => ?_)
  refine Summable.mul_left _ ?_
  refine Summable.div_const ?_ _
  have h := (Decay.summable_pair_int (((Fr.xstar N0 : ℝ)) : ℂ) (Fr.μ i : ℝ) Fr.cref).norm
  refine h.congr (fun n => ?_)
  unfold Dn
  congr 1
  push_cast
  rw [one_div, one_div]
  ring_nf

lemma norm_inv_ray_nat_le (hC : Fr.ContourOK) (N0 a : ℕ) {θ r : ℝ} (hs : Real.sin θ ≠ 0)
    (hr : 0 ≤ r) :
    ‖(rayPt (Fr.xstar N0) θ r - (a : ℝ))⁻¹‖
      ≤ 1 / (Real.sqrt (kap2 θ) * ((Fr.xs : ℝ) + r)) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  refine (norm_inv_rayPt_le (a : ℝ) (xstar_lt_nat hC N0 a).ne' hs hr).trans ?_
  exact one_div_le_one_div_of_le (by positivity) (by nlinarith [xs_le_dist hC N0 a])

/-- **Interchange of sum and ray integral**: `∑_n ∫_ray e_n v_a v_b = ∫_ray E v_a v_b`. -/
theorem rayI_E_hasSum (hC : Fr.ContourOK) (N0 a b : ℕ) {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasSum (fun n : ℤ => rayI (Fr.xstar N0) θ
        (fun z => Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹)))
      (rayI (Fr.xstar N0) θ (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hK := Real.sqrt_pos.2 (kap2_pos hs)
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  set K := Real.sqrt (kap2 θ) with hKdef
  set x := Fr.xstar N0 with hxdef
  unfold rayI
  refine hasSum_integral_of_dominated_convergence
    (fun n r => Fr.Bn N0 θ n * ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2))) ?_ ?_ ?_ ?_ ?_
  · intro n
    refine Measurable.aestronglyMeasurable ?_
    unfold rayPt Frame.eterm
    refine Measurable.mul (Measurable.mul ?_ (by fun_prop)) (by fun_prop)
    refine Measurable.neg (Finset.measurable_sum _ (fun i _ => ?_))
    fun_prop
  · intro n
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : 0 ≤ r := le_of_lt hr
    rw [norm_mul, norm_mul, norm_mul, norm_exp_ofReal_mul_I, mul_one]
    have h1 := norm_eterm_ray_le hC N0 n hs hr'
    have h2 := norm_inv_ray_nat_le hC N0 a hs hr'
    have h3 := norm_inv_ray_nat_le hC N0 b hs hr'
    have hpos : 0 < K * ((Fr.xs : ℝ) + r) := by positivity
    have hB : 0 ≤ Fr.Bn N0 θ n := by unfold Bn Dn; positivity
    calc ‖Fr.eterm (rayPt x θ r) n‖ * (‖(rayPt x θ r - (a : ℂ))⁻¹‖ * ‖(rayPt x θ r - (b : ℂ))⁻¹‖)
        ≤ Fr.Bn N0 θ n * ((1 / (K * ((Fr.xs : ℝ) + r))) * (1 / (K * ((Fr.xs : ℝ) + r)))) := by
          apply mul_le_mul h1 (mul_le_mul h2 h3 (norm_nonneg _) (by positivity))
            (by positivity) hB
      _ = _ := by field_simp
  · exact Eventually.of_forall fun r => (summable_Bn N0 θ).mul_right _
  · have hI := (integrableOn_invsq (Fr.xs : ℝ) hxs).const_mul (1 / K ^ 2)
    have : (fun r : ℝ => ∑' n : ℤ, Fr.Bn N0 θ n * ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)))
        = fun r => (∑' n : ℤ, Fr.Bn N0 θ n) * ((1 / K ^ 2) * (1 / ((Fr.xs : ℝ) + r) ^ 2)) := by
      funext r; exact tsum_mul_right
    rw [this]
    exact hI.const_mul _
  · refine Eventually.of_forall fun r => ?_
    exact ((Fr.summable_eterm _).hasSum.mul_right _).mul_right _

/-- The ray integral of a single term is nonzero only through the poles to the left of `x*`. -/
theorem hasSum_tail (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (N0 a b : ℕ) :
    HasSum (fun m : ℕ => ((Fr.tailTerm N0 a b (m : ℝ) : ℝ) : ℂ))
      ((2 * Real.pi * I)⁻¹ *
        contL (Fr.xstar N0) φ (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
  have hpi := Real.pi_pos
  have hsφ : Real.sin φ ≠ 0 := by
    apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  have hsφ' : Real.sin (-φ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hsφ
  have hU := rayI_E_hasSum hC N0 a b hsφ
  have hL := rayI_E_hasSum hC N0 a b hsφ'
  have hCt := hL.sub hU
  have h2pi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hT : HasSum (fun n : ℤ => ((Fr.tailTerm N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ))
      ((2 * Real.pi * I)⁻¹ *
        contL (Fr.xstar N0) φ (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹))) := by
    have h3 := hCt.mul_left ((2 * Real.pi * I)⁻¹)
    have h4 : (fun n : ℤ => (2 * Real.pi * I)⁻¹ * (rayI (Fr.xstar N0) (-φ)
          (fun z => Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))
        - rayI (Fr.xstar N0) φ (fun z => Fr.eterm z n * ((z - a)⁻¹ * (z - b)⁻¹))))
        = fun n : ℤ => ((Fr.tailTerm N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) := by
      funext n
      have := contL_eterm hC h1 h2 N0 a b n
      unfold contL at this
      rw [this]
      field_simp
    rw [h4] at h3
    exact h3
  have hi : Function.Injective (Nat.cast : ℕ → ℤ) := Nat.cast_injective
  have hzero : ∀ n : ℤ, n ∉ Set.range (Nat.cast : ℕ → ℤ) →
      ((Fr.tailTerm N0 a b ((n : ℤ) : ℝ) : ℝ) : ℂ) = 0 := by
    intro n hn
    have hneg : n < 0 := by
      by_contra h
      push_neg at h
      exact hn ⟨n.toNat, by simp [Int.toNat_of_nonneg h]⟩
    have hn' : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
    have hμ : ∀ i, (Fr.μ i : ℝ) ≤ 1 := fun i => by exact_mod_cast (Fr.hμ i).2
    have h0 : (0 : ℝ) ≤ N0 := Nat.cast_nonneg N0
    unfold tailTerm
    push_cast
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_neg (by have := hμ i; intro h; linarith)]
    simp
  have := (hi.hasSum_iff hzero).2 hT
  simpa [Function.comp_def] using this

/-- **The contour identity** (general frame).  With `x* = -N0 - xs` and `Γ` the two rays
`x* + r e^{±iφ}` (`π/2 < φ < π`) traversed downward (`contL`),
`∑' m, atomSum a b m = atomHead N0 a b + (1/2πi) ∫_Γ E v_a v_b dz`.
Here `∑' m, atomSum a b m = norm · T_{ab}` is `T_eq_atoms` (WP2b). -/
theorem contour_identity (hC : Fr.ContourOK) {φ : ℝ} (h1 : Real.pi / 2 < φ) (h2 : φ < Real.pi)
    (N0 a b : ℕ) :
    ((∑' m : ℕ, Fr.atomSum a b m : ℝ) : ℂ)
      = ((Fr.atomHead N0 a b : ℝ) : ℂ) + (2 * Real.pi * I)⁻¹ *
          contL (Fr.xstar N0) φ (fun z => Fr.EC z * ((z - a)⁻¹ * (z - b)⁻¹)) := by
  have hT := hasSum_tail hC h1 h2 N0 a b
  set M := N0 + ⌈(Fr.xs : ℝ)⌉₊ with hM
  have hH : HasSum (fun m : ℕ => ((Fr.headTerm N0 a b (m : ℝ) : ℝ) : ℂ))
      (∑ m ∈ range M, ((Fr.headTerm N0 a b (m : ℝ) : ℝ) : ℂ)) := by
    refine hasSum_sum_of_ne_finset_zero (fun m hm => ?_)
    have hm' : M ≤ m := by simpa using hm
    have hc : (Fr.xs : ℝ) ≤ ⌈(Fr.xs : ℝ)⌉₊ := Nat.le_ceil _
    have hmM : ((N0 + ⌈(Fr.xs : ℝ)⌉₊ : ℕ) : ℝ) ≤ m := by exact_mod_cast hm'
    push_cast at hmM
    have hμ : ∀ i, (0 : ℝ) < (Fr.μ i : ℝ) := fun i => by exact_mod_cast (Fr.hμ i).1
    unfold headTerm
    push_cast
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_pos (by have := hμ i; linarith)]
    simp
  have hsum := hT.add hH
  have hpt : ∀ m : ℕ, ((Fr.tailTerm N0 a b (m : ℝ) : ℝ) : ℂ) + ((Fr.headTerm N0 a b (m : ℝ) : ℝ) : ℂ)
      = ((Fr.atomSum a b m : ℝ) : ℂ) := by
    intro m
    unfold tailTerm headTerm atomSum
    push_cast
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> simp
  simp only [hpt] at hsum
  rw [Complex.ofReal_tsum, hsum.tsum_eq, add_comm]
  unfold atomHead
  push_cast
  rfl

end Frame
end CatalanCore
