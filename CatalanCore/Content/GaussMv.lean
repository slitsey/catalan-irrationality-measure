module

public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# The multivariate Gauss content (generic)

`p` a prime, `σ` any type of variables.  For `f ∈ ℚ[σ]` and `e ∈ ℤ`,
`GV p e f` says that the Gauss valuation of `f` at `p` is at least `e`: every coefficient
of `p^{-e} f` lies in `ℤ_(p)`.  This is the multivariate form of `GLE`
(`Arith/Hybrid/Tropical.lean`), with integer (possibly negative) exponents.

* algebra: `GV.add`, `GV.mul` (the easy half of Gauss's lemma, all that a lower bound needs),
  `GV.sum`, `GV.prod`, `GV.const_iff`, `GV.X`;
* specialisation only raises the valuation: `GV.eval` (points in `ℤ_(p)^σ`),
  `GV.subst` (substitution of polynomials of content `≥ 0`, e.g. `T ↦ τ ∈ ℤ_(p)`);
* integrality: `int_coeff_of_forall_GV` (content `≥ 0` at every prime gives `ℤ` coefficients);
* determinants: `GV.det` (row and column weights) and the rank principle `GV.det_of_rank`:
  if the scaled matrix `p^{-(r_i+c_j)} M_ij` is integral and its reduction over
  `Frac 𝔽_p[σ]` has rank `≤ n - k`, then `GV (∑ r + ∑ c + k) (det M)`.
-/

open MvPolynomial CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Linalg

namespace CatalanCore.Content

section GV

variable {σ : Type*} (p : ℕ) [hp : Fact p.Prime]

/-- The Gauss valuation of `f` at `p` is at least `e`. -/
def GV (e : ℤ) (f : MvPolynomial σ ℚ) : Prop := ∀ m, (p : ℚ) ^ (-e) * f.coeff m ∈ LocRing p

variable {p}

lemma natPow_mem (k : ℕ) : (p : ℚ) ^ k ∈ LocRing p := by
  simpa using int_mem_locRing (ℓ := p) ((p : ℤ) ^ k)

lemma p_ne_zero : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

lemma prod_zpow_p {ι : Type*} (s : Finset ι) (w : ι → ℤ) :
    ∏ i ∈ s, (p : ℚ) ^ (w i) = (p : ℚ) ^ (∑ i ∈ s, w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ p_ne_zero]

lemma GV.mono {e e' : ℤ} (h : e' ≤ e) {f : MvPolynomial σ ℚ} (hf : GV p e f) : GV p e' f := by
  intro m
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 h)
  have : (p : ℚ) ^ (-e') * f.coeff m = (p : ℚ) ^ k * ((p : ℚ) ^ (-e) * f.coeff m) := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ p_ne_zero, ← hk]; ring_nf
  rw [this]; exact (LocRing p).mul_mem (natPow_mem k) (hf m)

lemma GV.zero (e : ℤ) : GV p e (0 : MvPolynomial σ ℚ) := by
  intro m; simp

lemma GV.add {e : ℤ} {f g : MvPolynomial σ ℚ} (hf : GV p e f) (hg : GV p e g) :
    GV p e (f + g) := by
  intro m; rw [show (f + g).coeff m = f.coeff m + g.coeff m by simp, mul_add]; exact (LocRing p).add_mem (hf m) (hg m)

lemma GV.neg {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f) : GV p e (-f) := by
  intro m; rw [coeff_neg, mul_neg]; exact (LocRing p).neg_mem (hf m)

lemma GV.sub {e : ℤ} {f g : MvPolynomial σ ℚ} (hf : GV p e f) (hg : GV p e g) :
    GV p e (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma GV.sum {κ : Type*} {e : ℤ} {s : Finset κ} {f : κ → MvPolynomial σ ℚ}
    (h : ∀ k ∈ s, GV p e (f k)) : GV p e (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.zero (σ := σ) e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma GV.zsmul {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f) (n : ℤ) : GV p e (n • f) := by
  intro m
  rw [coeff_smul, zsmul_eq_mul, mul_left_comm]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) n) (hf m)

lemma GV.const_iff {e : ℤ} {x : ℚ} : GV p e (C x : MvPolynomial σ ℚ) ↔ (p : ℚ) ^ (-e) * x ∈ LocRing p := by
  constructor
  · intro h; simpa using h 0
  · intro h m
    classical
    rw [coeff_C]
    split_ifs
    · exact h
    · simp

lemma GV.const {e : ℤ} {x : ℚ} (h : (p : ℚ) ^ (-e) * x ∈ LocRing p) : GV p e (C x : MvPolynomial σ ℚ) :=
  GV.const_iff.2 h

lemma GV.const_int (z : ℤ) : GV p 0 (C (z : ℚ) : MvPolynomial σ ℚ) :=
  GV.const (by simpa using int_mem_locRing (ℓ := p) z)

lemma GV.const_loc {x : ℚ} (hx : x ∈ LocRing p) : GV p 0 (C x : MvPolynomial σ ℚ) :=
  GV.const (by simpa using hx)

lemma GV.var (i : σ) : GV p 0 (X i : MvPolynomial σ ℚ) := by
  intro m
  classical
  rw [coeff_X]
  split_ifs <;> simp [(LocRing p).one_mem]

lemma GV.one : GV p 0 (1 : MvPolynomial σ ℚ) := by
  simpa using GV.const_int (σ := σ) (p := p) 1

lemma GV.mul {e e' : ℤ} {f g : MvPolynomial σ ℚ} (hf : GV p e f) (hg : GV p e' g) :
    GV p (e + e') (f * g) := by
  classical
  intro m
  rw [coeff_mul, Finset.mul_sum]
  refine (LocRing p).sum_mem fun x _ => ?_
  have : (p : ℚ) ^ (-(e + e')) * (f.coeff x.1 * g.coeff x.2) =
      ((p : ℚ) ^ (-e) * f.coeff x.1) * ((p : ℚ) ^ (-e') * g.coeff x.2) := by
    rw [neg_add, zpow_add₀ p_ne_zero]; ring
  rw [this]; exact (LocRing p).mul_mem (hf _) (hg _)

lemma GV.prod {κ : Type*} {s : Finset κ} {f : κ → MvPolynomial σ ℚ} {e : κ → ℤ}
    (h : ∀ k ∈ s, GV p (e k) (f k)) : GV p (∑ k ∈ s, e k) (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.one (σ := σ) (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma GV.pow {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f) (n : ℕ) : GV p (n * e) (f ^ n) := by
  induction n with
  | zero => simpa using GV.one (σ := σ) (p := p)
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hf
    convert this using 1; push_cast; ring

lemma GV.const_mul {e e' : ℤ} {x : ℚ} (hx : (p : ℚ) ^ (-e) * x ∈ LocRing p) {f : MvPolynomial σ ℚ}
    (hf : GV p e' f) : GV p (e + e') (C x * f) := (GV.const hx).mul hf

/-- Multiplication by the constant `p^k` shifts the valuation by `k`. -/
lemma GV.const_zpow_mul_iff {e k : ℤ} {f : MvPolynomial σ ℚ} :
    GV p (e + k) (C ((p : ℚ) ^ k) * f) ↔ GV p e f := by
  constructor <;> intro h m
  · have := h m
    rwa [coeff_C_mul, ← mul_assoc, ← zpow_add₀ p_ne_zero, neg_add, add_assoc, neg_add_cancel,
      add_zero] at this
  · rw [coeff_C_mul, ← mul_assoc, ← zpow_add₀ p_ne_zero, neg_add, add_assoc, neg_add_cancel,
      add_zero]
    exact h m

/-! ### Specialisation -/

/-- Evaluation at a point of `ℤ_(p)^σ` only raises the valuation. -/
lemma GV.evalPt {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f) (v : σ → ℚ)
    (hv : ∀ i, v i ∈ LocRing p) : (p : ℚ) ^ (-e) * MvPolynomial.eval v f ∈ LocRing p := by
  classical
  rw [MvPolynomial.eval_eq, Finset.mul_sum]
  refine (LocRing p).sum_mem fun d _ => ?_
  rw [← mul_assoc]
  exact (LocRing p).mul_mem (hf d) ((LocRing p).prod_mem fun i _ => (LocRing p).pow_mem (hv i) _)

/-- Substituting polynomials of content `≥ 0` only raises the valuation. -/
lemma GV.subst {τ : Type*} {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f)
    (g : σ → MvPolynomial τ ℚ) (hg : ∀ i, GV p 0 (g i)) : GV p e (MvPolynomial.bind₁ g f) := by
  classical
  rw [bind₁, aeval_def, eval₂_eq]
  refine GV.sum fun d _ => ?_
  have h1 : GV p e (C (f.coeff d) : MvPolynomial τ ℚ) := GV.const (hf d)
  have h2 : GV p 0 (∏ i ∈ d.support, g i ^ d i) := by
    have := GV.prod (s := d.support) (e := fun _ => (0 : ℤ)) (f := fun i => g i ^ d i)
      (fun i _ => by simpa using (hg i).pow (d i))
    simpa using this
  have := h1.mul h2
  simpa [MvPolynomial.algebraMap_eq] using this

/-- Content `≥ 0` at every prime: integer coefficients. -/
lemma int_coeff_of_forall_GV {f : MvPolynomial σ ℚ}
    (H : ∀ (q : ℕ) [Fact q.Prime], GV q 0 f) (m : σ →₀ ℕ) : ∃ z : ℤ, f.coeff m = z :=
  int_of_forall_locRing _ fun q _ => by simpa using H q m

/-- Content `≥ 0` at every prime: the value at an integer point is an integer (the integer
specialisation used for `HasScaledContent`). -/
lemma int_eval_of_forall_GV {f : MvPolynomial σ ℚ}
    (H : ∀ (q : ℕ) [Fact q.Prime], GV q 0 f) (v : σ → ℤ) :
    ∃ z : ℤ, MvPolynomial.eval (fun i => (v i : ℚ)) f = z :=
  int_of_forall_locRing _ fun q _ => by
    simpa using GV.evalPt (H q) (fun i => (v i : ℚ)) (fun i => int_mem_locRing (v i))

/-! ### Determinants -/

lemma GV.det {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (r c : ι → ℤ) (h : ∀ i j, GV p (r i + c j) (M i j)) : GV p (∑ i, r i + ∑ j, c j) M.det := by
  rw [Matrix.det_apply]
  refine GV.sum fun τ _ => ?_
  rw [Units.smul_def]
  have hprod : GV p (∑ i, (r (τ i) + c i)) (∏ i, M (τ i) i) := GV.prod fun i _ => h (τ i) i
  rw [Finset.sum_add_distrib, Equiv.sum_comp τ r] at hprod
  exact hprod.zsmul _

end GV

/-! ### Lifts and the reduction to `Frac 𝔽_p[σ]` -/

section Red

variable {σ : Type*} (p : ℕ) [hp : Fact p.Prime]

/-- Integral polynomials as rational polynomials. -/
noncomputable abbrev toQmv : MvPolynomial σ (LocRing p) →+* MvPolynomial σ ℚ :=
  MvPolynomial.map (LocRing p).subtype

/-- Reduction of integral polynomials into the fraction field of `𝔽_p[σ]`. -/
noncomputable def redMv : MvPolynomial σ (LocRing p) →+* FractionRing (MvPolynomial σ (ZMod p)) :=
  (algebraMap (MvPolynomial σ (ZMod p)) (FractionRing (MvPolynomial σ (ZMod p)))).comp
    (MvPolynomial.map (redQ p))

variable {p}

lemma toQmv_coeff (g : MvPolynomial σ (LocRing p)) (m : σ →₀ ℕ) :
    (toQmv p g).coeff m = ((g.coeff m : LocRing p) : ℚ) := by
  simp [toQmv, coeff_map]

lemma toQmv_injective : Function.Injective (toQmv (σ := σ) p) :=
  MvPolynomial.map_injective _ Subtype.val_injective

lemma redMv_eq_zero_iff (g : MvPolynomial σ (LocRing p)) :
    redMv p g = 0 ↔ C ((p : ℕ) : LocRing p) ∣ g := by
  rw [C_dvd_iff_dvd_coeff]
  unfold redMv
  rw [RingHom.comp_apply,
    map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial σ (ZMod p)) _)]
  constructor
  · intro h m
    have := congrArg (fun F => F.coeff m) h
    simpa [coeff_map, redQ_eq_zero_iff] using this
  · intro h
    ext m
    simp [coeff_map, (redQ_eq_zero_iff p _).2 (h m)]

lemma prime_Cp : Prime (C ((p : ℕ) : LocRing p) : MvPolynomial σ (LocRing p)) :=
  (MvPolynomial.prime_C_iff σ).2 (prime_p p)

/-- The reduction of an integral polynomial, coefficientwise. -/
lemma map_redQ_coeff (g : MvPolynomial σ (LocRing p)) (m : σ →₀ ℕ) :
    (MvPolynomial.map (redQ p) g).coeff m = (((g.coeff m : LocRing p) : ℚ) : ZMod p) := by
  rw [coeff_map, redQ_apply]

/-- A polynomial of content `≥ e`, scaled by `p^{-e}`, lifts to an integral polynomial. -/
lemma GV.exists_lift {e : ℤ} {f : MvPolynomial σ ℚ} (hf : GV p e f) :
    ∃ g : MvPolynomial σ (LocRing p), toQmv p g = C ((p : ℚ) ^ (-e)) * f := by
  classical
  refine ⟨∑ m ∈ f.support, monomial m ⟨_, hf m⟩, ?_⟩
  rw [map_sum]
  conv_rhs => rw [f.as_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [toQmv, map_monomial, C_mul_monomial]
  rfl

/-- Conversely an integral lift gives content `≥ e`. -/
lemma GV.of_lift {e : ℤ} {f : MvPolynomial σ ℚ} (g : MvPolynomial σ (LocRing p))
    (hg : toQmv p g = C ((p : ℚ) ^ (-e)) * f) : GV p e f := by
  intro m
  have := congrArg (fun F => F.coeff m) hg
  simp only [toQmv_coeff, coeff_C_mul] at this
  rw [← this]; exact (g.coeff m).2

/-- **The rank principle for the multivariate Gauss content.**  Let `Z` be an integral matrix
with `Z_ij = p^{-(r_i + c_j)} M_ij`.  If the reduction of `Z` has rank `≤ card ι - k`, then
`v_p(det M) ≥ ∑ r + ∑ c + k`. -/
theorem GV.det_of_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℚ)) (r c : ι → ℤ) (Z : Matrix ι ι (MvPolynomial σ (LocRing p)))
    (hZ : ∀ i j, toQmv p (Z i j) = C ((p : ℚ) ^ (-(r i + c j))) * M i j) (k : ℕ)
    (hrk : (Z.map (redMv p)).rank + k ≤ Fintype.card ι) :
    GV p (∑ i, r i + ∑ j, c j + k) M.det := by
  classical
  -- `p^k ∣ det Z`
  set e := Fintype.equivFin ι
  set Zf := Z.submatrix e.symm e.symm with hZf
  have hrank : (Zf.map (redMv p)).rank = (Z.map (redMv p)).rank := by
    have : Zf.map (redMv p) = (Z.map (redMv p)).submatrix e.symm e.symm := rfl
    rw [this, Matrix.rank_submatrix]
  have hdvd : C ((p : ℕ) : LocRing p) ^ k ∣ Z.det := by
    have := dvd_det_of_rank (redMv p) prime_Cp (redMv_eq_zero_iff (σ := σ))
      (Fintype.card ι) k Zf (by rw [hrank]; exact hrk)
    rwa [hZf, Matrix.det_submatrix_equiv_self] at this
  obtain ⟨w, hw⟩ := hdvd
  -- `toQmv (det Z) = p^{-(∑r+∑c)} det M`
  have hmat : (toQmv p).mapMatrix Z = Matrix.diagonal (fun i => C ((p : ℚ) ^ (-r i))) * M *
      Matrix.diagonal (fun j => C ((p : ℚ) ^ (-c j))) := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hZ i j, neg_add, zpow_add₀ p_ne_zero, C_mul]; ring
  have h1 : ∀ w : ι → ℤ, ∏ i, (C ((p : ℚ) ^ (-w i)) : MvPolynomial σ ℚ) =
      C ((p : ℚ) ^ (-∑ i, w i)) := by
    intro w
    rw [← map_prod, prod_zpow_p, Finset.sum_neg_distrib]
  have hdetQ : toQmv p Z.det = C ((p : ℚ) ^ (-(∑ i, r i + ∑ j, c j))) * M.det := by
    rw [RingHom.map_det, hmat, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_diagonal, h1, h1, neg_add, zpow_add₀ p_ne_zero, C_mul]; ring
  rw [hw, map_mul, map_pow, toQmv, map_C] at hdetQ
  have hpk : (C (((LocRing p).subtype) ((p : ℕ) : LocRing p)) : MvPolynomial σ ℚ) ^ k =
      C ((p : ℚ) ^ (k : ℤ)) := by
    rw [← C_pow]; simp
  rw [hpk] at hdetQ
  apply GV.of_lift w
  have hC : (C ((p : ℚ) ^ (k : ℤ)) : MvPolynomial σ ℚ) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact zpow_ne_zero _ p_ne_zero
  apply mul_left_cancel₀ hC
  rw [hdetQ, ← mul_assoc, ← C_mul, ← zpow_add₀ p_ne_zero]
  congr 3; ring

end Red

end CatalanCore.Content
