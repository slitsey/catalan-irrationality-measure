module

public import CatalanCore.Lai.ContentL2
public import CatalanCore.Lai.ContentLaw
public import CatalanCore.Content.GaussMv
public import CatalanCore.Content.CrtBasis
public import CatalanCore.Content.ContentLaw
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The root-shifted `Δ`-scaled basis over the generic node constants `T` (Lai, Lemma G / Theorem L2, step 1)

`MPT = ℚ[a, b, X, T]`.  The generic functional `L_T` (`laiLT`, built in `Lai.ContentL2`) has the
local orthogonal polynomial `π ∈ 𝒪[y]` with coefficients in `Frac F_p[T]`; the basis is therefore
taken **scaled by the Hankel determinant `Δ`** (a Gauss unit), so that it lies in `MPT[X]`, with
no inverse.

* Part 1: the Gauss lemma in `GV` form: `GUnit`, `GV.of_unit_mul` (a Gauss unit can be cancelled from a
  content bound); `GUnit` is closed under products, powers and congruences mod `p`.
* Part 2: congruences mod `p` of polynomials over `MPT` and of determinants (`PInt`, `PCong`, `GV.det_cong`).
* Part 3: `linM`, `gram_det_gen`: `det (𝓛(f_x f_y)) = (det B)² det (m_{i+j})` over any commutative ring
  (generalises `gram_det`).
* Part 4: the decomposition of `R ∈ MPT[X]` in the `T`-monomials (`decomp`) and the transfer principle
  `GV_transfer`.
* Part 5-7: the extension `laiLTx` of `L_T` to `MPT[X]`, its node expansion `laiLTx_nodes`, and the node
  valuations `ndT_ge`, `ndT0_ge`, `ndT_modNdT_lead`, `nodeT_ge`, `laiLTx_ge_except` (the `MPT[X]` forms of
  `node_ge`, `node0_ge`, `node_lead_T`, `laiL_ge_except`).
* Part 8: `shiftP p μ s A = ∑_{j ≤ μ} A_j p^{μ-j} (t+s)^j`: exact node values `P_s(-k) = p^μ A(-ℓ)`
  (`shiftP_eval`) and `p P_s'(-k) = p^μ A'(-ℓ)` (`shiftP_deriv`) at `k = s + ℓ p`, and `P_s ≡ A_μ (t+s)^μ`
  (`shiftP_cong`).
* Part 9-10: the family `famFun` (CRT form with local factors), its unimodularity `fam_det_unit` (every row
  is `Δ^c` times the integer CRT row mod `p`) and `GV_laiJ_of_famT` (the generic-`T` analogue of
  `GV_laiJ_of_crt`: a content bound on the Gram determinant gives one on `J_n`).
* Part 11-12: `orthA`, the Cramer form `Δ y^μ + ∑ a_j y^j` of the orthogonal polynomial
  (`orthA_orth`, `orthA_coeff_top`, `orthA_pint`) and `cLoc_delta_unit`: `Δ` is a Gauss unit (Lemma H).
* Part 13: `localOK_window`, `GV_laiJ_of_window`: the window family of the paper (`P_s` on the window,
  `(t+r)^{m_r}` off it).
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content

namespace CatalanCore.Lai

/-! ### Part 1: the Gauss lemma in `GV` form -/

section Gauss

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- A *Gauss unit*: content exactly `0` (nonzero reduction mod `p`). -/
def GUnit (p : ℕ) [Fact p.Prime] (f : MvPolynomial σ ℚ) : Prop := GV p 0 f ∧ ¬ GV p 1 f

lemma exists_pow_mul_mem (x : ℚ) : ∃ k : ℕ, (p : ℚ) ^ k * x ∈ LocRing p := by
  obtain ⟨a, d', hd', hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := x.den) x.den_nz p hp.out.ne_one
  refine ⟨a, ?_⟩
  have hx : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den x).symm
  have hp0 : (p : ℚ) ^ a ≠ 0 := pow_ne_zero _ (p_ne_zero (p := p))
  have hd'0 : (d' : ℚ) ≠ 0 := by
    have : d' ≠ 0 := by
      rintro rfl
      simp at hd
    exact_mod_cast this
  have : (p : ℚ) ^ a * x = (x.num : ℚ) * ((d' : ℚ))⁻¹ := by
    have hx' : (x.num : ℚ) = x * x.den := (Rat.mul_den_eq_num x).symm
    have hden : (x.den : ℚ) = (p : ℚ) ^ a * d' := by exact_mod_cast hd
    rw [hx', hden]
    field_simp
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) x.num) (inv_natCast_mem_locRing hd')

lemma exists_GV_negK (g : MvPolynomial σ ℚ) : ∃ K : ℕ, GV p (-(K : ℤ)) g := by
  classical
  have h : ∀ m ∈ g.support, ∃ k : ℕ, (p : ℚ) ^ k * g.coeff m ∈ LocRing p :=
    fun m _ => exists_pow_mul_mem (g.coeff m)
  choose! kf hkf using h
  refine ⟨g.support.sup kf, fun m => ?_⟩
  rw [neg_neg, zpow_natCast]
  by_cases hm : m ∈ g.support
  · have h1 := hkf m hm
    have hle : kf m ≤ g.support.sup kf := Finset.le_sup (f := kf) hm
    have : (p : ℚ) ^ (g.support.sup kf) * g.coeff m =
        (p : ℚ) ^ (g.support.sup kf - kf m) * ((p : ℚ) ^ kf m * g.coeff m) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [this]
    exact (LocRing p).mul_mem (natPow_mem _) h1
  · have : g.coeff m = 0 := by simpa using hm
    simp [this]

lemma exists_GV_neg (g : MvPolynomial σ ℚ) (e : ℤ) : ∃ k : ℕ, GV p (e - k) g := by
  obtain ⟨K, hK⟩ := exists_GV_negK (p := p) g
  exact ⟨K + e.toNat, hK.mono (by push_cast; omega)⟩

lemma toQmv_Cp_mul (h : MvPolynomial σ (LocRing p)) :
    toQmv p (MvPolynomial.C ((p : ℕ) : LocRing p) * h) = MvPolynomial.C (p : ℚ) * toQmv p h := by
  simp [toQmv]

lemma zpow_neg_sub_one (e : ℤ) : (p : ℚ) ^ (-(e - 1)) = (p : ℚ) * (p : ℚ) ^ (-e) := by
  rw [show -(e - 1) = -e + 1 by ring, zpow_add_one₀ (p_ne_zero (p := p))]; ring

lemma Cinv_mul_C : (MvPolynomial.C ((p : ℚ) ^ (-1 : ℤ)) : MvPolynomial σ ℚ) * MvPolynomial.C (p : ℚ) = 1 := by
  rw [← map_mul]
  have : (p : ℚ) ^ (-1 : ℤ) * (p : ℚ) = 1 := by
    rw [zpow_neg_one]; exact inv_mul_cancel₀ (p_ne_zero (p := p))
  rw [this, map_one]

/-- One step of the Gauss lemma. -/
lemma GV.step_of_unit {e : ℤ} {f g : MvPolynomial σ ℚ} (hf : GUnit p f) (hfg : GV p e (f * g))
    (hg : GV p (e - 1) g) : GV p e g := by
  obtain ⟨f1, hf1⟩ := GV.exists_lift hf.1
  obtain ⟨g1, hg1⟩ := GV.exists_lift hg
  obtain ⟨h1, hh1⟩ := GV.exists_lift hfg
  have hf1' : toQmv p f1 = f := by simpa using hf1
  have hprod : f1 * g1 = MvPolynomial.C ((p : ℕ) : LocRing p) * h1 := by
    apply toQmv_injective
    rw [map_mul, toQmv_Cp_mul, hf1', hg1, hh1, zpow_neg_sub_one, map_mul]
    ring
  have hred : redMv p f1 * redMv p g1 = 0 := by
    rw [← map_mul, hprod, map_mul, (redMv_eq_zero_iff (MvPolynomial.C ((p : ℕ) : LocRing p))).2 dvd_rfl,
      zero_mul]
  have hf0 : redMv p f1 ≠ 0 := by
    intro h0
    obtain ⟨f2, hf2⟩ := (redMv_eq_zero_iff f1).1 h0
    apply hf.2
    refine GV.of_lift f2 ?_
    have : f = MvPolynomial.C (p : ℚ) * toQmv p f2 := by rw [← hf1', hf2, toQmv_Cp_mul]
    rw [this, ← mul_assoc, Cinv_mul_C, one_mul]
  have hg0 : redMv p g1 = 0 := (mul_eq_zero.1 hred).resolve_left hf0
  obtain ⟨g2, hg2⟩ := (redMv_eq_zero_iff g1).1 hg0
  refine GV.of_lift g2 ?_
  have h3 : MvPolynomial.C (p : ℚ) * toQmv p g2 = MvPolynomial.C ((p : ℚ) ^ (-(e - 1))) * g := by
    rw [← toQmv_Cp_mul, ← hg2, hg1]
  have h4 : toQmv p g2 = MvPolynomial.C ((p : ℚ) ^ (-1 : ℤ)) * (MvPolynomial.C (p : ℚ) * toQmv p g2) := by
    rw [← mul_assoc, Cinv_mul_C, one_mul]
  rw [h4, h3, ← mul_assoc, ← map_mul, ← zpow_add₀ (p_ne_zero (p := p))]
  congr 3; ring

/-- **Gauss lemma** (lower-bound form): a Gauss unit can be cancelled from a content bound. -/
theorem GV.of_unit_mul {e : ℤ} {f g : MvPolynomial σ ℚ} (hf : GUnit p f) (hfg : GV p e (f * g)) :
    GV p e g := by
  obtain ⟨k, hk⟩ := exists_GV_neg (p := p) g e
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    apply ih
    have h' : GV p (e - k - 1) g := by
      have : e - ((k + 1 : ℕ) : ℤ) = e - k - 1 := by push_cast; ring
      rwa [this] at hk
    exact GV.step_of_unit hf (hfg.mono (by omega)) h'

lemma GUnit.C_int (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : GUnit p (MvPolynomial.C (z : ℚ) : MvPolynomial σ ℚ) := by
  refine ⟨GV.const_int z, fun h => ?_⟩
  have h1 := GV.const_iff.1 h
  have h2 := inv_intCast_mem (p := p) z hz
  have hz0 : (z : ℚ) ≠ 0 := by
    intro h0
    apply hz
    have : z = 0 := by exact_mod_cast h0
    simp [this]
  have h3 : (p : ℚ)⁻¹ ∈ LocRing p := by
    have := (LocRing p).mul_mem h1 h2
    rwa [zpow_neg_one, mul_assoc, mul_inv_cancel₀ hz0, mul_one] at this
  rw [mem_locRing] at h3
  simp [Rat.inv_natCast_den, hp.out.ne_zero] at h3

lemma GUnit.one : GUnit p (1 : MvPolynomial σ ℚ) := by
  have := GUnit.C_int (σ := σ) (p := p) 1 (by
    intro h
    have : p ∣ 1 := by exact_mod_cast h
    exact hp.out.not_dvd_one this)
  simpa using this

lemma GUnit.mul {f g : MvPolynomial σ ℚ} (hf : GUnit p f) (hg : GUnit p g) : GUnit p (f * g) :=
  ⟨by simpa using hf.1.mul hg.1, fun h => hg.2 (GV.of_unit_mul hf h)⟩

lemma GUnit.pow {f : MvPolynomial σ ℚ} (hf : GUnit p f) (n : ℕ) : GUnit p (f ^ n) := by
  induction n with
  | zero => simpa using GUnit.one (σ := σ) (p := p)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

lemma GUnit.prod {κ : Type*} {s : Finset κ} {f : κ → MvPolynomial σ ℚ} (h : ∀ k ∈ s, GUnit p (f k)) :
    GUnit p (∏ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GUnit.one (σ := σ) (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- A Gauss unit stays one after a perturbation of content `≥ 1`. -/
lemma GUnit.congr {f g : MvPolynomial σ ℚ} (hg : GUnit p g) (h0 : GV p 0 f) (hd : GV p 1 (f - g)) :
    GUnit p f :=
  ⟨h0, fun h1 => hg.2 (by simpa using h1.sub hd)⟩

end Gauss

/-! ### Part 2: congruences of polynomials and determinants -/

section Cong

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- Integral polynomials in `X` over `ℚ[σ]`: all coefficients of content `≥ 0`. -/
def PInt (p : ℕ) [Fact p.Prime] (F : (MvPolynomial σ ℚ)[X]) : Prop := ∀ i, GV p 0 (F.coeff i)

/-- Congruence mod `p`: all coefficients of the difference have content `≥ 1`. -/
def PCong (p : ℕ) [Fact p.Prime] (F G : (MvPolynomial σ ℚ)[X]) : Prop :=
  ∀ i, GV p 1 (F.coeff i - G.coeff i)

lemma PInt.mul {F G : (MvPolynomial σ ℚ)[X]} (hF : PInt p F) (hG : PInt p G) : PInt p (F * G) := by
  intro n
  rw [Polynomial.coeff_mul]
  have := GV.sum (p := p) (e := 0) (s := Finset.antidiagonal n)
    (f := fun x => F.coeff x.1 * G.coeff x.2) (fun x _ => by simpa using (hF x.1).mul (hG x.2))
  exact this

lemma PInt.add {F G : (MvPolynomial σ ℚ)[X]} (hF : PInt p F) (hG : PInt p G) : PInt p (F + G) := by
  intro n; rw [Polynomial.coeff_add]; exact (hF n).add (hG n)

lemma PInt.pow {F : (MvPolynomial σ ℚ)[X]} (hF : PInt p F) (n : ℕ) : PInt p (F ^ n) := by
  induction n with
  | zero =>
    intro i
    rw [pow_zero, Polynomial.coeff_one]
    split_ifs
    · exact GV.one
    · exact GV.zero _
  | succ n ih => rw [pow_succ]; exact ih.mul hF

lemma PInt.prod {κ : Type*} {s : Finset κ} {F : κ → (MvPolynomial σ ℚ)[X]} (h : ∀ k ∈ s, PInt p (F k)) :
    PInt p (∏ k ∈ s, F k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro i
    rw [Finset.prod_empty, Polynomial.coeff_one]
    split_ifs
    · exact GV.one
    · exact GV.zero _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma PInt.C_mul {c : MvPolynomial σ ℚ} (hc : GV p 0 c) {F : (MvPolynomial σ ℚ)[X]} (hF : PInt p F) :
    PInt p (Polynomial.C c * F) := by
  intro i; rw [Polynomial.coeff_C_mul]; simpa using hc.mul (hF i)

lemma PCong.mul {F F' G G' : (MvPolynomial σ ℚ)[X]} (hF : PInt p F) (hG' : PInt p G')
    (h : PCong p F G) (h' : PCong p F' G') : PCong p (F * F') (G * G') := by
  intro n
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul, ← Finset.sum_sub_distrib]
  refine GV.sum fun x _ => ?_
  have e : F.coeff x.1 * F'.coeff x.2 - G.coeff x.1 * G'.coeff x.2 =
      F.coeff x.1 * (F'.coeff x.2 - G'.coeff x.2) + (F.coeff x.1 - G.coeff x.1) * G'.coeff x.2 := by ring
  rw [e]
  have a1 := (hF x.1).mul (h' x.2)
  have a2 := (h x.1).mul (hG' x.2)
  rw [zero_add] at a1
  rw [add_zero] at a2
  exact a1.add a2

lemma PCong.refl (F : (MvPolynomial σ ℚ)[X]) : PCong p F F := fun i => by simpa using GV.zero (p := p) 1

lemma PCong.C_mul {c : MvPolynomial σ ℚ} (hc : GV p 0 c) {F G : (MvPolynomial σ ℚ)[X]} (h : PCong p F G) :
    PCong p (Polynomial.C c * F) (Polynomial.C c * G) := by
  intro i
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, ← mul_sub]
  simpa using hc.mul (h i)

lemma PCong.prod {κ : Type*} {s : Finset κ} {F G : κ → (MvPolynomial σ ℚ)[X]}
    (hF : ∀ k ∈ s, PInt p (F k)) (hG : ∀ k ∈ s, PInt p (G k)) (h : ∀ k ∈ s, PCong p (F k) (G k)) :
    PCong p (∏ k ∈ s, F k) (∏ k ∈ s, G k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PCong.refl (p := p) (1 : (MvPolynomial σ ℚ)[X])
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact PCong.mul (hF a (Finset.mem_insert_self a s)) (PInt.prod fun k hk => hG k (Finset.mem_insert_of_mem hk))
      (h a (Finset.mem_insert_self a s))
      (ih (fun k hk => hF k (Finset.mem_insert_of_mem hk)) (fun k hk => hG k (Finset.mem_insert_of_mem hk))
        (fun k hk => h k (Finset.mem_insert_of_mem hk)))

lemma GV.prod_cong {κ : Type*} {s : Finset κ} {f g : κ → MvPolynomial σ ℚ}
    (hf : ∀ k ∈ s, GV p 0 (f k)) (hg : ∀ k ∈ s, GV p 0 (g k)) (h : ∀ k ∈ s, GV p 1 (f k - g k)) :
    GV p 1 (∏ k ∈ s, f k - ∏ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.zero (p := p) (σ := σ) 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hP : GV p 0 (∏ k ∈ s, g k) := by
      have := GV.prod (p := p) (s := s) (e := fun _ => (0 : ℤ)) (f := g) (fun k hk => hg k (Finset.mem_insert_of_mem hk))
      simpa using this
    have hP' : GV p 0 (∏ k ∈ s, f k) := by
      have := GV.prod (p := p) (s := s) (e := fun _ => (0 : ℤ)) (f := f) (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa using this
    have ih' := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) (fun k hk => hg k (Finset.mem_insert_of_mem hk))
      (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have e : f a * ∏ k ∈ s, f k - g a * ∏ k ∈ s, g k =
        f a * (∏ k ∈ s, f k - ∏ k ∈ s, g k) + (f a - g a) * ∏ k ∈ s, g k := by ring
    rw [e]
    have a1 := (hf a (Finset.mem_insert_self a s)).mul ih'
    have a2 := (h a (Finset.mem_insert_self a s)).mul hP
    rw [zero_add] at a1
    rw [add_zero] at a2
    exact a1.add a2

lemma GV.det_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (MvPolynomial σ ℚ))
    (h : ∀ i j, GV p 0 (M i j)) : GV p 0 M.det := by
  have := GV.det (p := p) M (fun _ => 0) (fun _ => 0) (fun i j => by simpa using h i j)
  simpa using this

lemma GV.det_cong {ι : Type*} [Fintype ι] [DecidableEq ι] (M M' : Matrix ι ι (MvPolynomial σ ℚ))
    (h0 : ∀ i j, GV p 0 (M i j)) (h0' : ∀ i j, GV p 0 (M' i j)) (hd : ∀ i j, GV p 1 (M i j - M' i j)) :
    GV p 1 (M.det - M'.det) := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine GV.sum fun τ _ => ?_
  rw [Units.smul_def, Units.smul_def, ← smul_sub]
  exact (GV.prod_cong (fun i _ => h0 _ _) (fun i _ => h0' _ _) (fun i _ => hd _ _)).zsmul _

end Cong



/-! ### Part 3: the Gram determinant over a general commutative ring -/

section GramGen

variable {R : Type*} [CommRing R]

/-- The linear extension to `R[X]` of the moment sequence `m`: `∑ f_i m_i`. -/
noncomputable def linM (m : ℕ → R) (f : R[X]) : R := f.sum fun i c => c * m i

lemma linM_add (m : ℕ → R) (f g : R[X]) : linM m (f + g) = linM m f + linM m g := by
  unfold linM
  exact Polynomial.sum_add_index _ _ _ (fun i => by simp) (fun i a b => by ring)

lemma linM_zero (m : ℕ → R) : linM m 0 = 0 := by simp [linM]

lemma linM_monomial (m : ℕ → R) (k : ℕ) (c : R) : linM m (Polynomial.C c * Polynomial.X ^ k) = c * m k := by
  rw [Polynomial.C_mul_X_pow_eq_monomial]
  unfold linM
  rw [Polynomial.sum_monomial_index]
  simp

lemma linM_C_mul (m : ℕ → R) (c : R) (f : R[X]) : linM m (Polynomial.C c * f) = c * linM m f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, linM_add, linM_add, hf, hg, mul_add]
  | monomial n a =>
    have h1 : Polynomial.monomial n a = Polynomial.C a * Polynomial.X ^ n := (Polynomial.C_mul_X_pow_eq_monomial).symm
    have h2 : Polynomial.C c * Polynomial.monomial n a = Polynomial.C (c * a) * Polynomial.X ^ n := by
      rw [h1, ← mul_assoc, ← Polynomial.C_mul]
    rw [h2, linM_monomial, h1, linM_monomial, mul_assoc]

lemma linM_sum {κ : Type*} (s : Finset κ) (m : ℕ → R) (P : κ → R[X]) :
    linM m (∑ k ∈ s, P k) = ∑ k ∈ s, linM m (P k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linM_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linM_add, ih]

/-- `linM (f g)` for polynomials of degree `< N` in terms of the moments. -/
lemma linM_mul_expand (m : ℕ → R) (N : ℕ) (f g : R[X]) (hf : f.natDegree < N) (hg : g.natDegree < N) :
    linM m (f * g) = ∑ i ∈ range N, ∑ j ∈ range N, f.coeff i * g.coeff j * m (i + j) := by
  have hf' : f = ∑ i ∈ range N, Polynomial.C (f.coeff i) * Polynomial.X ^ i := by
    conv_lhs => rw [Polynomial.as_sum_range' f N hf]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have hg' : g = ∑ j ∈ range N, Polynomial.C (g.coeff j) * Polynomial.X ^ j := by
    conv_lhs => rw [Polynomial.as_sum_range' g N hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  have : f * g = ∑ i ∈ range N, ∑ j ∈ range N,
      Polynomial.C (f.coeff i * g.coeff j) * Polynomial.X ^ (i + j) := by
    conv_lhs => rw [hf', hg']
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.C_mul, pow_add]; ring
  rw [this, linM_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [linM_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [linM_monomial]

lemma sumRange_fin2 {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ → ℕ → M) :
    ∑ i ∈ range N, ∑ j ∈ range N, g i j = ∑ i : Fin N, ∑ j : Fin N, g i j := by
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix of coefficients of the family `f` (rows `x`, columns `t^i`, `i < N`). -/
noncomputable def coeffMatG (N : ℕ) (f : ι → R[X]) : Matrix ι (Fin N) R :=
  Matrix.of fun x i => (f x).coeff i

/-- The Hankel matrix of the moments. -/
def hankelG (m : ℕ → R) (N : ℕ) : Matrix (Fin N) (Fin N) R := Matrix.of fun i j => m ((i : ℕ) + j)

theorem gram_eq_gen (m : ℕ → R) (N : ℕ) (f : ι → R[X]) (hf : ∀ x, (f x).natDegree < N) :
    (Matrix.of fun x y => linM m (f x * f y)) =
      coeffMatG N f * hankelG m N * (coeffMatG N f).transpose := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.of_apply, linM_mul_expand m N _ _ (hf x) (hf y), Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, coeffMatG, Matrix.of_apply, hankelG, Finset.sum_mul]
  rw [sumRange_fin2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Generic Gram determinant.**  `det (𝓛(f_x f_y)) = (det B)² det (m_{i+j})` for a family of
`N` polynomials of degree `< N`, indexed by `ι ≃ Fin N`. -/
theorem gram_det_gen (m : ℕ → R) (N : ℕ) (e : ι ≃ Fin N) (f : ι → R[X]) (hf : ∀ x, (f x).natDegree < N) :
    (Matrix.of fun x y => linM m (f x * f y)).det =
      (coeffMatG N (fun z => f (e.symm z))).det ^ 2 * (hankelG m N).det := by
  have h : (Matrix.of fun z w : Fin N => linM m (f (e.symm z) * f (e.symm w))) =
      coeffMatG N (fun z => f (e.symm z)) * hankelG m N * (coeffMatG N (fun z => f (e.symm z))).transpose :=
    gram_eq_gen m N (fun z => f (e.symm z)) (fun z => hf _)
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h2
  rw [← Matrix.det_submatrix_equiv_self e.symm (Matrix.of fun x y => linM m (f x * f y))]
  have : (Matrix.of fun x y => linM m (f x * f y)).submatrix e.symm e.symm =
      Matrix.of fun z w : Fin N => linM m (f (e.symm z) * f (e.symm w)) := rfl
  rw [this, h2]
  ring

end GramGen

/-! ### Part 4: decomposition in the `T`-monomials and the transfer principle -/

section Decomp

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- The coefficient of `T^α` of a polynomial in `X` over `ℚ[σ]`, as a polynomial over `ℚ`. -/
noncomputable def slice (R : (MvPolynomial σ ℚ)[X]) (α : σ →₀ ℕ) : ℚ[X] :=
  ∑ i ∈ R.support, Polynomial.monomial i ((R.coeff i).coeff α)

lemma slice_coeff (R : (MvPolynomial σ ℚ)[X]) (α : σ →₀ ℕ) (j : ℕ) :
    (slice R α).coeff j = (R.coeff j).coeff α := by
  classical
  unfold slice
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases hj : j ∈ R.support
  · simp [hj]
  · have : R.coeff j = 0 := by simpa using hj
    simp [hj, this]

lemma slice_int {R : (MvPolynomial σ ℚ)[X]} (hR : PInt p R) (α : σ →₀ ℕ) : IntPoly p (slice R α) := by
  intro j
  rw [slice_coeff]
  simpa using hR j α

lemma decomp (R : (MvPolynomial σ ℚ)[X]) : ∃ A : Finset (σ →₀ ℕ),
    R = ∑ α ∈ A,
      Polynomial.C (MvPolynomial.monomial α (1 : ℚ)) * (slice R α).map (MvPolynomial.C : ℚ →+* MvPolynomial σ ℚ) := by
  classical
  refine ⟨R.support.biUnion (fun i => (R.coeff i).support), ?_⟩
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, slice_coeff]
  have h1 : ∀ α : σ →₀ ℕ, MvPolynomial.monomial α (1 : ℚ) * MvPolynomial.C ((R.coeff j).coeff α) =
      MvPolynomial.monomial α ((R.coeff j).coeff α) := by
    intro α
    rw [mul_comm, MvPolynomial.C_mul_monomial, mul_one]
  simp only [h1]
  conv_lhs => rw [MvPolynomial.as_sum (R.coeff j)]
  refine Finset.sum_subset ?_ ?_
  · intro α hα
    by_cases hj : j ∈ R.support
    · exact Finset.mem_biUnion.2 ⟨j, hj, hα⟩
    · have : R.coeff j = 0 := by simpa using hj
      rw [this] at hα
      simp at hα
  · intro α _ hα
    have : (R.coeff j).coeff α = 0 := by simpa using hα
    simp [this]

/-- **Transfer principle.**  A functional `Θ` on `ℚ[σ][X]`, additive and homogeneous over `ℚ[σ]`, has
content `≥ e` on every `PInt` polynomial as soon as it has content `≥ e` on the `p`-integral
rational polynomials. -/
theorem GV_transfer {e : ℤ} (Θ : (MvPolynomial σ ℚ)[X] → MvPolynomial σ ℚ)
    (hadd : ∀ F G, Θ (F + G) = Θ F + Θ G)
    (hsm : ∀ (c : MvPolynomial σ ℚ) F, Θ (Polynomial.C c * F) = c * Θ F)
    (R : (MvPolynomial σ ℚ)[X]) (hR : PInt p R)
    (h : ∀ R0 : ℚ[X], IntPoly p R0 → GV p e (Θ (R0.map (MvPolynomial.C : ℚ →+* MvPolynomial σ ℚ)))) :
    GV p e (Θ R) := by
  classical
  have h0 : Θ 0 = 0 := by
    have := hsm 0 0
    simpa using this
  have hsum : ∀ (s : Finset (σ →₀ ℕ)) (G : (σ →₀ ℕ) → (MvPolynomial σ ℚ)[X]),
      Θ (∑ α ∈ s, G α) = ∑ α ∈ s, Θ (G α) := by
    intro s G
    induction s using Finset.induction_on with
    | empty => simpa using h0
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  obtain ⟨A, hR'⟩ := decomp R
  have key : GV p e (Θ (∑ α ∈ A,
      Polynomial.C (MvPolynomial.monomial α (1 : ℚ)) *
        (slice R α).map (MvPolynomial.C : ℚ →+* MvPolynomial σ ℚ))) := by
    rw [hsum]
    refine GV.sum fun α _ => ?_
    rw [hsm]
    have hm : GV p 0 (MvPolynomial.monomial α (1 : ℚ) : MvPolynomial σ ℚ) := by
      intro m
      rw [MvPolynomial.coeff_monomial]
      split_ifs <;> simp [(LocRing p).one_mem]
    have := hm.mul (h _ (slice_int hR α))
    simpa using this
  rwa [← hR'] at key

end Decomp

/-! ### Part 5: the node expansion of `L_T` on `MPT[X]` -/

section NodeT

variable {p : ℕ} [hp : Fact p.Prime]

lemma ren_C (x : ℚ) : ren (MvPolynomial.C x : MP) = (MvPolynomial.C x : MPT) := by
  unfold ren; simp

lemma GV_ren {e : ℤ} {f : MP} (hf : GV p e f) : GV p e (ren f) :=
  GV.subst hf (fun i : Fin 3 => (MvPolynomial.X (Sum.inl i) : MPT)) (fun i => GV.var _)

/-- `F(-k)` as an element of `MPT`. -/
noncomputable def evk (k : ℕ) (F : MPT[X]) : MPT := F.eval (MvPolynomial.C (-(k : ℚ)))

/-- `F'(-k)` as an element of `MPT`. -/
noncomputable def devk (k : ℕ) (F : MPT[X]) : MPT :=
  (Polynomial.derivative F).eval (MvPolynomial.C (-(k : ℚ)))

lemma evk_map (k : ℕ) (F0 : ℚ[X]) :
    evk k (F0.map (MvPolynomial.C : ℚ →+* MPT)) = MvPolynomial.C (F0.eval (-(k : ℚ))) := by
  unfold evk
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (MvPolynomial.C : ℚ →+* MPT) (-(k : ℚ))

lemma devk_map (k : ℕ) (F0 : ℚ[X]) :
    devk k (F0.map (MvPolynomial.C : ℚ →+* MPT)) = MvPolynomial.C (F0.derivative.eval (-(k : ℚ))) := by
  unfold devk
  rw [Polynomial.derivative_map, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (MvPolynomial.C : ℚ →+* MPT) (-(k : ℚ))

lemma evk_add (k : ℕ) (F G : MPT[X]) : evk k (F + G) = evk k F + evk k G := by
  unfold evk; rw [Polynomial.eval_add]

lemma devk_add (k : ℕ) (F G : MPT[X]) : devk k (F + G) = devk k F + devk k G := by
  unfold devk; rw [Polynomial.derivative_add, Polynomial.eval_add]

lemma evk_C_mul (k : ℕ) (c : MPT) (F : MPT[X]) : evk k (Polynomial.C c * F) = c * evk k F := by
  unfold evk; rw [Polynomial.eval_mul, Polynomial.eval_C]

lemma devk_C_mul (k : ℕ) (c : MPT) (F : MPT[X]) : devk k (Polynomial.C c * F) = c * devk k F := by
  unfold devk; rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]

/-- The `k`-th node of `L_n`, for polynomials with coefficients in `MPT`. -/
noncomputable def ndT (n k : ℕ) (F : MPT[X]) : MPT :=
  ren (MvPolynomial.C (laiCoef n k : ℚ)) * (ren (laiU k) * devk k F + ren (laiV n k) * evk k F)

/-- The modification of `L_T` at the node `k = s + ℓ p`. -/
noncomputable def modNdT (p : ℕ) (σ : ℤ) (cl τu τv : ℚ) (l k : ℕ) (F : MPT[X]) : MPT :=
  bT * (MvPolynomial.C ((p : ℚ) ^ (σ - 3) * cl) * (Tu l - MvPolynomial.C τu) * devk k F +
    MvPolynomial.C ((p : ℚ) ^ (σ - 4) * cl) * (Tv l - MvPolynomial.C τv) * evk k F)

lemma ndT_map (n k : ℕ) (F0 : ℚ[X]) :
    ndT n k (F0.map (MvPolynomial.C : ℚ →+* MPT)) = ren (laiNd n k F0) := by
  unfold ndT laiNd
  rw [evk_map, devk_map]
  simp only [map_mul, map_add, ren_C]

lemma modNdT_map (p : ℕ) (σ : ℤ) (cl τu τv : ℚ) (l k : ℕ) (F0 : ℚ[X]) :
    modNdT p σ cl τu τv l k (F0.map (MvPolynomial.C : ℚ →+* MPT)) = modNd p σ cl τu τv l k F0 := by
  unfold modNdT modNd
  rw [evk_map, devk_map]

lemma ndT_add (n k : ℕ) (F G : MPT[X]) : ndT n k (F + G) = ndT n k F + ndT n k G := by
  unfold ndT; rw [evk_add, devk_add]; ring

lemma ndT_C_mul (n k : ℕ) (c : MPT) (F : MPT[X]) : ndT n k (Polynomial.C c * F) = c * ndT n k F := by
  unfold ndT; rw [evk_C_mul, devk_C_mul]; ring

lemma modNdT_add (p : ℕ) (σ : ℤ) (cl τu τv : ℚ) (l k : ℕ) (F G : MPT[X]) :
    modNdT p σ cl τu τv l k (F + G) = modNdT p σ cl τu τv l k F + modNdT p σ cl τu τv l k G := by
  unfold modNdT; rw [evk_add, devk_add]; ring

lemma modNdT_C_mul (p : ℕ) (σ : ℤ) (cl τu τv : ℚ) (l k : ℕ) (c : MPT) (F : MPT[X]) :
    modNdT p σ cl τu τv l k (Polynomial.C c * F) = c * modNdT p σ cl τu τv l k F := by
  unfold modNdT; rw [evk_C_mul, devk_C_mul]; ring

/-- The node of `L_T` at `k`: `ndT` plus the modification if `k ∈ K`. -/
noncomputable def nodeT (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) (F : MPT[X]) : MPT :=
  ndT n k F + if k ∈ K then modNdT p (σ k) (cl k) (τu (k / p)) (τv (k / p)) (k / p) k F else 0

lemma nodeT_add (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) (F G : MPT[X]) :
    nodeT (p := p) n K σ cl τu τv k (F + G) =
      nodeT (p := p) n K σ cl τu τv k F + nodeT (p := p) n K σ cl τu τv k G := by
  unfold nodeT
  rw [ndT_add]
  split_ifs
  · rw [modNdT_add]; ring
  · ring

lemma nodeT_C_mul (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) (c : MPT) (F : MPT[X]) :
    nodeT (p := p) n K σ cl τu τv k (Polynomial.C c * F) = c * nodeT (p := p) n K σ cl τu τv k F := by
  unfold nodeT
  rw [ndT_C_mul]
  split_ifs
  · rw [modNdT_C_mul]; ring
  · ring

/-- Extension of `L_T` to `MPT[X]`. -/
noncomputable def laiLTx (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (F : MPT[X]) : MPT :=
  linM (fun i => laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ i)) F

lemma eq_linM_of_lin {R : Type*} [CommRing R] (Φ : R[X] → R) (hadd : ∀ F G, Φ (F + G) = Φ F + Φ G)
    (hsm : ∀ (c : R) F, Φ (Polynomial.C c * F) = c * Φ F) (F : R[X]) :
    Φ F = linM (fun i => Φ (Polynomial.X ^ i)) F := by
  induction F using Polynomial.induction_on' with
  | add f g hf hg => rw [hadd, linM_add, hf, hg]
  | monomial n a => rw [← Polynomial.C_mul_X_pow_eq_monomial, linM_monomial, hsm]

/-- **Node expansion of `L_T` on `MPT[X]`.** -/
theorem laiLTx_nodes (n : ℕ) (K : Finset ℕ) (hK : K ⊆ range (6 * n + 1)) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ)
    (F : MPT[X]) :
    laiLTx (p := p) n K σ cl τu τv F = ∑ k ∈ range (6 * n + 1), nodeT (p := p) n K σ cl τu τv k F := by
  classical
  have hΦ := eq_linM_of_lin (fun F : MPT[X] => ∑ k ∈ range (6 * n + 1), nodeT (p := p) n K σ cl τu τv k F)
    (fun F G => by simp only [nodeT_add, Finset.sum_add_distrib])
    (fun c F => by simp only [nodeT_C_mul, Finset.mul_sum]) F
  unfold laiLTx
  rw [hΦ]
  congr 1
  funext i
  have hX : (Polynomial.X : MPT[X]) ^ i = ((Polynomial.X : ℚ[X]) ^ i).map (MvPolynomial.C : ℚ →+* MPT) := by
    simp
  show laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ i) = _
  unfold laiLT
  rw [hX]
  simp only [nodeT, Finset.sum_add_distrib, ndT_map]
  rw [laiL_eq_sum, map_sum]
  congr 1
  simp only [modNdT_map]
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hK]

end NodeT

/-! ### Part 6: node valuations for `MPT[X]` coefficients -/

section NodeBounds

variable {p : ℕ} [hp : Fact p.Prime]

/-- `X + s` in `MPT[X]`. -/
noncomputable def sX (s : ℕ) : MPT[X] := Polynomial.X + Polynomial.C (MvPolynomial.C (s : ℚ))

lemma sX_map (s : ℕ) :
    sX s = ((Polynomial.X + Polynomial.C (s : ℚ) : ℚ[X])).map (MvPolynomial.C : ℚ →+* MPT) := by
  simp [sX]

lemma shift_map (s m : ℕ) (R0 : ℚ[X]) :
    sX s ^ m * R0.map (MvPolynomial.C : ℚ →+* MPT) =
      (((Polynomial.X + Polynomial.C (s : ℚ) : ℚ[X])) ^ m * R0).map (MvPolynomial.C : ℚ →+* MPT) := by
  rw [sX_map, ← Polynomial.map_pow, ← Polynomial.map_mul]

lemma eval_map_C (R0 : ℚ[X]) (x : ℚ) :
    (R0.map (MvPolynomial.C : ℚ →+* MPT)).eval (MvPolynomial.C x) = MvPolynomial.C (R0.eval x) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (MvPolynomial.C : ℚ →+* MPT) x

/-- Evaluating a `PInt` polynomial at a `p`-integral constant gives content `≥ 0`. -/
lemma GV_eval {R : MPT[X]} (hR : PInt p R) {x : ℚ} (hx : x ∈ LocRing p) :
    GV p 0 (R.eval (MvPolynomial.C x)) := by
  rw [Polynomial.eval_eq_sum_range]
  refine GV.sum fun i _ => ?_
  have h1 : GV p 0 ((MvPolynomial.C x : MPT) ^ i) := by
    have := (GV.const_loc (σ := TVar) hx).pow i
    simpa using this
  simpa using (hR i).mul h1

lemma ndT_theta_add (n k : ℕ) (s m : ℕ) (F G : MPT[X]) :
    ndT n k (sX s ^ m * (F + G)) = ndT n k (sX s ^ m * F) + ndT n k (sX s ^ m * G) := by
  rw [mul_add, ndT_add]

lemma ndT_theta_smul (n k : ℕ) (s m : ℕ) (c : MPT) (F : MPT[X]) :
    ndT n k (sX s ^ m * (Polynomial.C c * F)) = c * ndT n k (sX s ^ m * F) := by
  rw [show sX s ^ m * (Polynomial.C c * F) = Polynomial.C c * (sX s ^ m * F) by ring, ndT_C_mul]

/-- **Lemma N for `MPT[X]` (node valuation, `ℓ ≥ 1`).** -/
theorem ndT_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (m : ℕ) (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p (k % p) : ℤ) - 4 + m) (ndT n k (sX (k % p) ^ m * R)) := by
  refine GV_transfer (fun R => ndT n k (sX (k % p) ^ m * R)) (fun F G => ndT_theta_add n k _ m F G)
    (fun c F => ndT_theta_smul n k _ m c F) R hR ?_
  intro R0 hR0
  show GV p _ (ndT n k (sX (k % p) ^ m * R0.map (MvPolynomial.C : ℚ →+* MPT)))
  rw [shift_map, ndT_map]
  exact GV_ren (node_ge (p := p) n k h8 h3 hk hl m R0 hR0)

lemma sX_eval_self (k : ℕ) : (sX k).eval (MvPolynomial.C (-(k : ℚ))) = 0 := by
  simp only [sX, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← map_add]; simp

/-- `ℓ = 0` (`k < p`): valuation `≥ σ - 1 + min(m,1)`. -/
theorem ndT0_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hkp : k < p)
    (m : ℕ) (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p k : ℤ) - 1 + (min m 1 : ℕ)) (ndT n k (sX k ^ m * R)) := by
  refine GV_transfer (fun R => ndT n k (sX k ^ m * R)) (fun F G => ndT_theta_add n k _ m F G)
    (fun c F => ndT_theta_smul n k _ m c F) R hR ?_
  intro R0 hR0
  show GV p _ (ndT n k (sX k ^ m * R0.map (MvPolynomial.C : ℚ →+* MPT)))
  rw [shift_map, ndT_map]
  exact GV_ren (node0_ge (p := p) n k h8 h3 hk hkp m R0 hR0)

/-- For `m ≥ 2` the `ℓ = 0` node vanishes. -/
lemma ndT_zero_of_two (n k m' : ℕ) (R : MPT[X]) : ndT n k (sX k ^ (m' + 2) * R) = 0 := by
  have e1 : evk k (sX k ^ (m' + 2) * R) = 0 := by
    unfold evk
    rw [Polynomial.eval_mul, Polynomial.eval_pow, sX_eval_self]; simp
  have e2 : devk k (sX k ^ (m' + 2) * R) = 0 := by
    unfold devk
    have hd : (Polynomial.derivative (sX k)) = 1 := by simp [sX]
    rw [Polynomial.derivative_mul, Polynomial.derivative_pow, hd]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_natCast, mul_one]
    rw [sX_eval_self]; simp
  unfold ndT
  rw [e1, e2]; simp

/-- Node data of an `L_T` modification at `k`: the `p`-adic shape of `c_k` and the node constants. -/
def NodeData (p : ℕ) (n : ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) : Prop :=
  1 ≤ k / p ∧ σ k = (sig n p (k % p) : ℤ) ∧
    ∃ (u : ℕ) (c κ : ℤ), (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u ∧
      (p : ℤ) ∣ (u : ℤ) - c * κ ∧ cl k = c ∧ τu (k / p) = κ * uL (k / p) ∧
      τv (k / p) = κ * vL n p k (k / p)

/-- The main term of the leading coefficient at a modified node. -/
noncomputable def leadMain (p : ℕ) (σ : ℕ) (cl : ℤ) (m l : ℕ) (ρ : MPT) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * cl) * ρ * bT *
    (MvPolynomial.C ((m : ℚ) * (-(l : ℚ)) ^ (m - 1)) * Tu l + MvPolynomial.C ((-(l : ℚ)) ^ m) * Tv l)

lemma GV_leadMain (σ : ℕ) (cl : ℤ) (m l : ℕ) {ρ : MPT} (hρ : GV p 0 ρ) :
    GV p ((σ : ℤ) - 4 + m) (leadMain p σ cl m l ρ) := by
  have hp0 := p_ne_zero (p := p)
  have hc : GV p ((σ : ℤ) - 4 + m) (MvPolynomial.C ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * cl) : MPT) := by
    apply GV.const
    have : (p : ℚ) ^ (-((σ : ℤ) - 4 + m)) * ((p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * cl) = cl := by
      have e1 : (p : ℚ) ^ (-((σ : ℤ) - 4 + m)) = (((p : ℚ) ^ σ)⁻¹ * ((p : ℚ) ^ m)⁻¹) * (p : ℚ) ^ 4 := by
        rw [show -((σ : ℤ) - 4 + m) = -(σ : ℤ) - (m : ℤ) + 4 by ring, zpow_add₀ hp0, zpow_sub₀ hp0, zpow_neg,
          zpow_natCast, zpow_natCast]
        simp [div_eq_mul_inv]
      rw [e1]; field_simp
    rw [this]
    exact_mod_cast int_mem_locRing (ℓ := p) cl
  have h1 : GV p 0 (MvPolynomial.C ((m : ℚ) * (-(l : ℚ)) ^ (m - 1)) * Tu l +
      MvPolynomial.C ((-(l : ℚ)) ^ m) * Tv l : MPT) := by
    have a1 : GV p 0 (MvPolynomial.C ((m : ℚ) * (-(l : ℚ)) ^ (m - 1)) : MPT) :=
      GV.const_loc ((LocRing p).mul_mem (natq_mem m) ((LocRing p).pow_mem ((LocRing p).neg_mem (natq_mem l)) _))
    have a2 : GV p 0 (MvPolynomial.C ((-(l : ℚ)) ^ m) : MPT) :=
      GV.const_loc ((LocRing p).pow_mem ((LocRing p).neg_mem (natq_mem l)) _)
    have b1 := a1.mul (GV.var (p := p) (Sum.inr (l, false) : TVar))
    have b2 := a2.mul (GV.var (p := p) (Sum.inr (l, true) : TVar))
    simpa [Tu, Tv] using b1.add b2
  have h2 := ((hc.mul hρ).mul (GV.var (p := p) (Sum.inl (1 : Fin 3) : TVar))).mul h1
  simpa [leadMain, bT] using h2

/-- **Leading term at a modified node, `MPT[X]` coefficients.** -/
theorem ndT_modNdT_lead (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (u : ℕ) (hu : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u)
    (cl κ : ℤ) (hcl : (p : ℤ) ∣ (u : ℤ) - cl * κ) (m : ℕ) (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p (k % p) : ℤ) - 3 + m)
      (ndT n k (sX (k % p) ^ m * R) +
        modNdT p (sig n p (k % p) : ℤ) (cl : ℚ) ((κ : ℚ) * uL (k / p)) ((κ : ℚ) * vL n p k (k / p)) (k / p) k
          (sX (k % p) ^ m * R) -
        leadMain p (sig n p (k % p)) cl m (k / p) (R.eval (MvPolynomial.C (-((k % p : ℕ) : ℚ))))) := by
  refine GV_transfer (fun R => ndT n k (sX (k % p) ^ m * R) +
        modNdT p (sig n p (k % p) : ℤ) (cl : ℚ) ((κ : ℚ) * uL (k / p)) ((κ : ℚ) * vL n p k (k / p)) (k / p) k
          (sX (k % p) ^ m * R) -
        leadMain p (sig n p (k % p)) cl m (k / p) (R.eval (MvPolynomial.C (-((k % p : ℕ) : ℚ)))))
    ?_ ?_ R hR ?_
  · intro F G
    simp only [mul_add, ndT_add, modNdT_add, leadMain, Polynomial.eval_add]
    ring
  · intro c F
    have e : sX (k % p) ^ m * (Polynomial.C c * F) = Polynomial.C c * (sX (k % p) ^ m * F) := by ring
    simp only [e, ndT_C_mul, modNdT_C_mul, leadMain, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  · intro R0 hR0
    show GV p _ (ndT n k (sX (k % p) ^ m * R0.map (MvPolynomial.C : ℚ →+* MPT)) +
        modNdT p (sig n p (k % p) : ℤ) (cl : ℚ) ((κ : ℚ) * uL (k / p)) ((κ : ℚ) * vL n p k (k / p)) (k / p) k
          (sX (k % p) ^ m * R0.map (MvPolynomial.C : ℚ →+* MPT)) -
        leadMain p (sig n p (k % p)) cl m (k / p)
          ((R0.map (MvPolynomial.C : ℚ →+* MPT)).eval (MvPolynomial.C (-((k % p : ℕ) : ℚ)))))
    rw [shift_map, ndT_map, modNdT_map, eval_map_C]
    have := node_lead_T (p := p) n k h8 h3 hk hl u hu cl κ hcl m R0 hR0
    unfold leadMain
    rw [← map_mul]
    exact this

end NodeBounds

/-! ### Part 7: the node sum with an exceptional set removed -/

section Assemble

variable {p : ℕ} [hp : Fact p.Prime]

/-- Valuation of a node of `L_T` (modified or not) on `(X + s)^m R`, `ℓ ≥ 1`. -/
theorem nodeT_ge (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p)
    (k : ℕ) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p) (hK : k ∈ K → NodeData p n σ cl τu τv k)
    (m : ℕ) (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p (k % p) : ℤ) - 4 + m)
      (nodeT (p := p) n K σ cl τu τv k (sX (k % p) ^ m * R)) := by
  unfold nodeT
  by_cases hkK : k ∈ K
  · rw [if_pos hkK]
    obtain ⟨-, hσ, u, c, κ, hu, hc, hcl, hτu, hτv⟩ := hK hkK
    have h1 := ndT_modNdT_lead (p := p) n k h8 h3 hk hl u hu c κ hc m R hR
    have h2 := GV_leadMain (p := p) (sig n p (k % p)) c m (k / p)
      (GV_eval hR ((LocRing p).neg_mem (natq_mem (k % p))))
    rw [hσ, hcl, hτu, hτv]
    have := (h1.mono (by omega : (sig n p (k % p) : ℤ) - 4 + m ≤ (sig n p (k % p) : ℤ) - 3 + m)).add h2
    simpa using this
  · rw [if_neg hkK, add_zero]
    exact ndT_ge (p := p) n k h8 h3 hk hl m R hR

/-- **The sum over nodes, with an exceptional set `E` removed** (`MPT[X]` version of
`laiL_ge_except`). -/
theorem laiLTx_ge_except (n : ℕ) (K : Finset ℕ) (hK6 : K ⊆ range (6 * n + 1)) (σ : ℕ → ℤ)
    (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (F : MPT[X]) (mm : ℕ → ℕ) (RR : ℕ → MPT[X])
    (hR : ∀ s, s < p → PInt p (RR s)) (hF : ∀ s, s < p → F = sX s ^ mm s * RR s) (e : ℤ)
    (E : Finset ℕ) (hE : E ⊆ range (6 * n + 1)) (hKd : ∀ k ∈ K, NodeData p n σ cl τu τv k)
    (h1 : ∀ k, k ≤ 6 * n → k ∉ E → 1 ≤ k / p → e ≤ (sig n p (k % p) : ℤ) - 4 + mm (k % p))
    (h0 : ∀ k, k ≤ 6 * n → k ∉ E → k < p →
      e ≤ (sig n p k : ℤ) - 1 + (min (mm k) 1 : ℕ) ∨ 2 ≤ mm k) :
    GV p e (laiLTx (p := p) n K σ cl τu τv F - ∑ k ∈ E, nodeT (p := p) n K σ cl τu τv k F) := by
  rw [laiLTx_nodes n K hK6, ← Finset.sum_sdiff hE, add_sub_cancel_right]
  refine GV.sum fun k hk => ?_
  have hk' := Finset.mem_sdiff.1 hk
  have hk6 : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk'.1
  by_cases hl : 1 ≤ k / p
  · have hs : k % p < p := Nat.mod_lt _ hp.out.pos
    rw [hF (k % p) hs]
    exact (nodeT_ge n K σ cl τu τv h8 h3 k hk6 hl (fun h => hKd k h) _ _ (hR _ hs)).mono (h1 k hk6 hk'.2 hl)
  · have hkp : k < p := by
      by_contra hc
      exact hl (Nat.div_pos (by omega) hp.out.pos)
    have hkK : k ∉ K := fun h => hl (hKd k h).1
    have hnd : ∀ F' : MPT[X], nodeT (p := p) n K σ cl τu τv k F' = ndT n k F' := by
      intro F'; unfold nodeT; rw [if_neg hkK, add_zero]
    rw [hF k hkp, hnd]
    rcases h0 k hk6 hk'.2 hkp with h | h
    · exact (ndT0_ge n k h8 h3 hk6 hkp _ _ (hR _ hkp)).mono h
    · obtain ⟨m', hm'⟩ : ∃ m', mm k = m' + 2 := ⟨mm k - 2, by omega⟩
      rw [hm', ndT_zero_of_two]
      exact GV.zero _

end Assemble

/-! ### Part 8: the shifted scaled polynomial and its exact node values -/

section ShiftP

variable {p : ℕ} [hp : Fact p.Prime]

lemma PInt.sum {κ : Type*} {s : Finset κ} {F : κ → MPT[X]} (h : ∀ k ∈ s, PInt p (F k)) :
    PInt p (∑ k ∈ s, F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro i; simpa using GV.zero (p := p) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

lemma PInt_X : PInt p (Polynomial.X : MPT[X]) := by
  intro i
  rw [Polynomial.coeff_X]
  split_ifs
  · exact GV.one
  · exact GV.zero _

lemma PInt_C {c : MPT} (hc : GV p 0 c) : PInt p (Polynomial.C c) := by
  intro i
  rw [Polynomial.coeff_C]
  split_ifs
  · exact hc
  · exact GV.zero _

lemma PInt_X_sub_C {z : MPT} (hz : GV p 0 z) : PInt p (Polynomial.X - Polynomial.C z : MPT[X]) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  exact PInt_X.add (PInt_C hz.neg)

lemma PInt_sX (s : ℕ) : PInt p (sX s) := by
  unfold sX
  exact PInt_X.add (PInt_C (GV.const_loc (natq_mem s)))

end ShiftP

section ShiftB

/-- The shifted scaled polynomial `P_s(t) = p^μ A((t+s)/p) = ∑_{j ≤ μ} A_j p^{μ-j} (t+s)^j`. -/
noncomputable def shiftP (p μ s : ℕ) (A : MPT[X]) : MPT[X] :=
  ∑ j ∈ range (μ + 1), Polynomial.C (A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j))) * sX s ^ j

lemma sX_natDegree (s : ℕ) : (sX s).natDegree = 1 := by
  unfold sX; exact Polynomial.natDegree_X_add_C _

lemma shiftP_natDegree_le (p μ s : ℕ) (A : MPT[X]) : (shiftP p μ s A).natDegree ≤ μ := by
  unfold shiftP
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  have hj' : j ≤ μ := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_pow_le).trans ?_
  rw [sX_natDegree]; simpa using hj'

lemma sX_eval_node (p s l : ℕ) :
    (sX s).eval (MvPolynomial.C (-((s + l * p : ℕ) : ℚ))) = MvPolynomial.C (p : ℚ) * MvPolynomial.C (-(l : ℚ)) := by
  simp only [sX, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← map_add, ← map_mul]
  congr 1
  push_cast; ring

/-- **Exact entry value** `P_s(-k) = p^μ A(-ℓ)` at the node `k = s + ℓ p`. -/
theorem shiftP_eval (p μ s l : ℕ) (A : MPT[X]) (hA : A.natDegree ≤ μ) :
    evk (s + l * p) (shiftP p μ s A) =
      MvPolynomial.C ((p : ℚ) ^ μ) * A.eval (MvPolynomial.C (-(l : ℚ))) := by
  unfold evk shiftP
  rw [Polynomial.eval_finset_sum, Polynomial.eval_eq_sum_range' (n := μ + 1) (by omega), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ μ := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, sX_eval_node, mul_pow, ← map_pow, ← map_pow]
  have : (MvPolynomial.C ((p : ℚ) ^ (μ - j)) : MPT) * MvPolynomial.C ((p : ℚ) ^ j) =
      MvPolynomial.C ((p : ℚ) ^ μ) := by
    rw [← map_mul, ← pow_add, Nat.sub_add_cancel hj']
  rw [← this]
  ring

/-- The derivative of a polynomial of degree `≤ μ` evaluated, as a sum over `range (μ+1)`. -/
lemma eval_derivative_range (A : MPT[X]) (μ : ℕ) (hA : A.natDegree ≤ μ) (x : MPT) :
    (Polynomial.derivative A).eval x = ∑ j ∈ range (μ + 1), A.coeff j * (j : MPT) * x ^ (j - 1) := by
  conv_lhs => rw [Polynomial.as_sum_range' A (μ + 1) (by omega)]
  rw [map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.derivative_monomial, Polynomial.eval_monomial]

/-- **Exact entry value of the derivative** `p P_s'(-k) = p^μ A'(-ℓ)`. -/
theorem shiftP_deriv (p μ s l : ℕ) (A : MPT[X]) (hA : A.natDegree ≤ μ) :
    MvPolynomial.C (p : ℚ) * devk (s + l * p) (shiftP p μ s A) =
      MvPolynomial.C ((p : ℚ) ^ μ) * (Polynomial.derivative A).eval (MvPolynomial.C (-(l : ℚ))) := by
  unfold devk shiftP
  rw [map_sum, Polynomial.eval_finset_sum, eval_derivative_range A μ hA, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ μ := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
  have hd : Polynomial.derivative (sX s) = 1 := by simp [sX]
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow, hd, mul_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_natCast]
  rw [sX_eval_node]
  rcases j with _ | j
  · simp
  · simp only [Nat.add_sub_cancel, mul_pow, ← map_pow]
    have : MvPolynomial.C (p : ℚ) * MvPolynomial.C ((p : ℚ) ^ (μ - (j + 1))) * MvPolynomial.C ((p : ℚ) ^ j) =
        (MvPolynomial.C ((p : ℚ) ^ μ) : MPT) := by
      rw [← map_mul, ← map_mul, ← pow_succ', ← pow_add]
      congr 2; omega
    rw [← this]
    ring

end ShiftB

section ShiftC

variable {p : ℕ} [hp : Fact p.Prime]

lemma PInt_shiftP (μ s : ℕ) {A : MPT[X]} (hA : PInt p A) : PInt p (shiftP p μ s A) := by
  unfold shiftP
  refine PInt.sum fun j hj => ?_
  refine PInt.C_mul ?_ ((PInt_sX s).pow j)
  have hc : GV p 0 (MvPolynomial.C ((p : ℚ) ^ (μ - j)) : MPT) := GV.const_loc (by simpa using natPow_mem (μ - j))
  simpa using (hA j).mul hc

/-- `P_s ≡ A_μ (t+s)^μ (mod p)`. -/
theorem shiftP_cong (μ s : ℕ) {A : MPT[X]} (hA : PInt p A) :
    PCong p (shiftP p μ s A) (Polynomial.C (A.coeff μ) * sX s ^ μ) := by
  intro i
  unfold shiftP
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, map_one, mul_one, Polynomial.coeff_add,
    Polynomial.finset_sum_coeff, add_sub_cancel_right]
  refine GV.sum fun j hj => ?_
  have hj' : j < μ := Finset.mem_range.1 hj
  rw [Polynomial.coeff_C_mul]
  obtain ⟨t, ht⟩ : ∃ t, μ - j = t + 1 := ⟨μ - j - 1, by omega⟩
  have hc : GV p 1 (MvPolynomial.C ((p : ℚ) ^ (μ - j)) : MPT) := by
    apply GV.const
    rw [ht, zpow_neg_one, pow_succ]
    have hp0 := p_ne_zero (p := p)
    have : ((p : ℚ))⁻¹ * ((p : ℚ) ^ t * (p : ℚ)) = (p : ℚ) ^ t := by field_simp
    rw [this]; exact natPow_mem t
  have h1 := (hA j).mul hc
  rw [zero_add] at h1
  have h2 := h1.mul ((PInt_sX s).pow j i)
  rw [add_zero] at h2
  exact h2

end ShiftC

/-! ### Part 9: the root-shifted Δ-scaled family and its unimodularity -/

section Family

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Fintype S] [DecidableEq S]

/-- The ring map `ℤ → MPT`. -/
noncomputable def zphi : ℤ →+* MPT := (MvPolynomial.C : ℚ →+* MPT).comp (Int.castRingHom ℚ)

lemma zphi_apply (z : ℤ) : zphi z = MvPolynomial.C (z : ℚ) := by simp [zphi]

/-- The family `e_{r,i} = u_r^i ∏_{r' ≠ r} q_{r'}`, `g_j = X^j ∏_r q_r` (`u_r = X - a_r`,
`q_r` the local factors: `(X - a_r)^{m_r}` off the window and the shifted scaled `P_s` on it). -/
noncomputable def famFun (u q : S → MPT[X]) (m : S → ℕ) (d : ℕ) :
    ((Σ r : S, Fin (m r)) ⊕ Fin d) → MPT[X] :=
  Sum.elim (fun x => u x.1 ^ (x.2 : ℕ) * ∏ r' ∈ univ.erase x.1, q r')
    (fun j => Polynomial.X ^ (j : ℕ) * ∏ r, q r)

/-- The power of `Δ` by which row `x` of the family exceeds the monic CRT row. -/
def famExp (ex : S → ℕ) (m : S → ℕ) (d : ℕ) : ((Σ r : S, Fin (m r)) ⊕ Fin d) → ℕ :=
  Sum.elim (fun x => ∑ r' ∈ univ.erase x.1, ex r') (fun _ => ∑ r, ex r)

/-- Hypotheses on the local factors: integral, and congruent to `Δ^{ex r} (X - a_r)^{m_r}`. -/
def LocalOK (p : ℕ) [Fact p.Prime] (Δ : MPT) (a : S → ℤ) (m ex : S → ℕ) (q : S → MPT[X]) : Prop :=
  ∀ r, PInt p (q r) ∧ PCong p (q r)
    (Polynomial.C (Δ ^ ex r) * (Polynomial.X - Polynomial.C (zphi (a r))) ^ m r)

lemma famFun_pint {Δ : MPT} (hΔ : GV p 0 Δ) {a : S → ℤ} {m ex : S → ℕ} {q : S → MPT[X]}
    (hq : LocalOK p Δ a m ex q) (d : ℕ) (x : (Σ r : S, Fin (m r)) ⊕ Fin d) :
    PInt p (famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d x) := by
  have hu : ∀ r, PInt p (Polynomial.X - Polynomial.C (zphi (a r)) : MPT[X]) := fun r =>
    PInt_X_sub_C (by rw [zphi_apply]; exact GV.const_int _)
  rcases x with ⟨r, i⟩ | j
  · exact ((hu r).pow _).mul (PInt.prod fun r' _ => (hq r').1)
  · exact ((PInt_X (p := p)).pow _).mul (PInt.prod fun r' _ => (hq r').1)

lemma fam_row_cong {Δ : MPT} (hΔ : GV p 0 Δ) {a : S → ℤ} {m ex : S → ℕ} {q : S → MPT[X]}
    (hq : LocalOK p Δ a m ex q) (d : ℕ) (x : (Σ r : S, Fin (m r)) ⊕ Fin d) :
    PCong p (famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d x)
      (Polynomial.C (Δ ^ famExp ex m d x) * (crtFam a m d x).map zphi) := by
  have hu : ∀ r, PInt p (Polynomial.X - Polynomial.C (zphi (a r)) : MPT[X]) := fun r =>
    PInt_X_sub_C (by rw [zphi_apply]; exact GV.const_int _)
  have hΔe : ∀ e : ℕ, GV p 0 (Δ ^ e) := fun e => by simpa using hΔ.pow e
  have hT : ∀ r, PInt p (Polynomial.C (Δ ^ ex r) * (Polynomial.X - Polynomial.C (zphi (a r))) ^ m r) :=
    fun r => PInt.C_mul (hΔe _) ((hu r).pow _)
  -- the product over a subset of the local factors
  have hprod : ∀ s : Finset S, PCong p (∏ r' ∈ s, q r')
      (Polynomial.C (Δ ^ (∑ r' ∈ s, ex r')) * ∏ r' ∈ s, (Polynomial.X - Polynomial.C (zphi (a r'))) ^ m r') := by
    intro s
    have h1 := PCong.prod (s := s) (fun r' _ => (hq r').1) (fun r' _ => hT r') (fun r' _ => (hq r').2)
    rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum] at h1
    exact h1
  rcases x with ⟨r, i⟩ | j
  · have key : (crtFam a m d (Sum.inl ⟨r, i⟩)).map zphi =
        (Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ) *
          ∏ r' ∈ univ.erase r, (Polynomial.X - Polynomial.C (zphi (a r'))) ^ m r' := by
      simp [crtFam, crtE, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub]
    rw [key]
    have h2 := PCong.mul (F := (Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ)) ((hu r).pow _)
      (PInt.C_mul (hΔe _) (PInt.prod fun r' _ => (hu r').pow _))
      (PCong.refl _) (hprod (univ.erase r))
    have e : Polynomial.C (Δ ^ famExp ex m d (Sum.inl ⟨r, i⟩)) *
        ((Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ) *
          ∏ r' ∈ univ.erase r, (Polynomial.X - Polynomial.C (zphi (a r'))) ^ m r') =
        (Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ) *
          (Polynomial.C (Δ ^ (∑ r' ∈ univ.erase r, ex r')) *
            ∏ r' ∈ univ.erase r, (Polynomial.X - Polynomial.C (zphi (a r'))) ^ m r') := by
      simp only [famExp, Sum.elim_inl]; ring
    rw [e]
    exact h2
  · have key : (crtFam a m d (Sum.inr j)).map zphi =
        Polynomial.X ^ (j : ℕ) * ∏ r, (Polynomial.X - Polynomial.C (zphi (a r))) ^ m r := by
      simp [crtFam, crtG, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub]
    rw [key]
    have h2 := PCong.mul (F := (Polynomial.X : MPT[X]) ^ (j : ℕ)) ((PInt_X (p := p)).pow _)
      (PInt.C_mul (hΔe _) (PInt.prod fun r' _ => (hu r').pow _))
      (PCong.refl _) (hprod univ)
    have e : Polynomial.C (Δ ^ famExp ex m d (Sum.inr j)) *
        (Polynomial.X ^ (j : ℕ) * ∏ r, (Polynomial.X - Polynomial.C (zphi (a r))) ^ m r) =
        (Polynomial.X : MPT[X]) ^ (j : ℕ) *
          (Polynomial.C (Δ ^ (∑ r', ex r')) * ∏ r', (Polynomial.X - Polynomial.C (zphi (a r'))) ^ m r') := by
      simp only [famExp, Sum.elim_inr]; ring
    rw [e]
    exact h2

lemma famFun_natDegree_lt {a : S → ℤ} {m : S → ℕ} {q : S → MPT[X]} (hqd : ∀ r, (q r).natDegree ≤ m r)
    (d N : ℕ) (hN : ∑ r, m r + d = N) (x : (Σ r : S, Fin (m r)) ⊕ Fin d) :
    (famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d x).natDegree < N := by
  have hu : ∀ r, (Polynomial.X - Polynomial.C (zphi (a r)) : MPT[X]).natDegree ≤ 1 := fun r =>
    (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hP : ∀ s : Finset S, (∏ r' ∈ s, q r').natDegree ≤ ∑ r' ∈ s, m r' := fun s =>
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum fun r' _ => hqd r')
  rcases x with ⟨r, i⟩ | j
  · simp only [famFun, Sum.elim_inl]
    have h1 := Polynomial.natDegree_mul_le (p := (Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ))
      (q := ∏ r' ∈ univ.erase r, q r')
    have h2 : ((Polynomial.X - Polynomial.C (zphi (a r))) ^ (i : ℕ)).natDegree ≤ (i : ℕ) := by
      refine Polynomial.natDegree_pow_le.trans ?_
      have := hu r
      nlinarith
    have h3 := hP (univ.erase r)
    have h4 : ∑ r' ∈ univ.erase r, m r' + m r = ∑ r', m r' := Finset.sum_erase_add _ _ (Finset.mem_univ r)
    have h5 := i.2
    omega
  · simp only [famFun, Sum.elim_inr]
    have h1 := Polynomial.natDegree_mul_le (p := (Polynomial.X : MPT[X]) ^ (j : ℕ)) (q := ∏ r, q r)
    have h2 : ((Polynomial.X : MPT[X]) ^ (j : ℕ)).natDegree ≤ (j : ℕ) := by simp
    have h3 := hP univ
    have h5 := j.2
    omega

/-- **Unimodularity of the root-shifted Δ-scaled family.**  The coefficient matrix has a Gauss unit
as determinant: modulo `p` every row is `Δ^c` times the integer CRT row. -/
theorem fam_det_unit {Δ : MPT} (hΔ : GUnit p Δ) {a : S → ℤ}
    (ha : Function.Injective fun r => (Int.castRingHom (ZMod p)) (a r)) {m ex : S → ℕ} {q : S → MPT[X]}
    (hq : LocalOK p Δ a m ex q) (d N : ℕ) (hN : ∑ r, m r + d = N)
    (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin N) :
    GUnit p (coeffMatG N (fun z => famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d
      (e.symm z))).det := by
  set M := coeffMatG N (fun z => famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d
      (e.symm z)) with hM
  set B0 : Matrix (Fin N) (Fin N) ℤ :=
    Matrix.of fun z i => (crtFam a m d (e.symm z)).coeff i with hB0
  set D : Fin N → MPT := fun z => Δ ^ famExp ex m d (e.symm z) with hD
  set M' : Matrix (Fin N) (Fin N) MPT := Matrix.of fun z i => D z * zphi (B0 z i) with hM'
  have hMi : ∀ z i, GV p 0 (M z i) := fun z i => famFun_pint hΔ.1 hq d _ i
  have hM'i : ∀ z i, GV p 0 (M' z i) := fun z i => by
    have h1 : GV p 0 (D z) := by simpa using hΔ.1.pow (famExp ex m d (e.symm z))
    have h2 : GV p 0 (zphi (B0 z i)) := by rw [zphi_apply]; exact GV.const_int _
    simpa [hM'] using h1.mul h2
  have hd : ∀ z i, GV p 1 (M z i - M' z i) := fun z i => by
    have h := fam_row_cong hΔ.1 hq d (e.symm z) i
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_map] at h
    exact h
  have hdet' : M'.det = (∏ z, D z) * zphi B0.det := by
    have h1 : M' = Matrix.of fun z i => D z * (B0.map zphi) z i := by
      refine Matrix.ext fun z i => ?_
      simp [hM']
    rw [h1, Matrix.det_mul_column, RingHom.map_det]
    rfl
  have hU' : GUnit p M'.det := by
    rw [hdet', zphi_apply]
    exact (GUnit.prod fun z _ => hΔ.pow _).mul (GUnit.C_int _ (crt_det_not_dvd p a ha m d N hN e))
  exact GUnit.congr hU' (GV.det_zero M hMi) (GV.det_cong M M' hMi hM'i hd)

end Family

/-! ### Part 10: from the Gram determinant of the family to `J_n` -/

section Terminal

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Fintype S] [DecidableEq S]

/-- **Generic-`T` analogue of `GV_laiJ_of_crt`.**  A content bound on the Gram determinant of the
root-shifted Δ-scaled family under the generic functional `L_T` gives the content bound of `J_n`
(after the `ν_p` normalisation).  The change of basis has the Gauss-unit determinant of
`fam_det_unit`; no inverse is taken. -/
theorem GV_laiJ_of_famT (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ)
    (hτu : ∀ l, τu l ∈ LocRing p) (hτv : ∀ l, τv l ∈ LocRing p)
    {Δ : MPT} (hΔ : GUnit p Δ) {a : S → ℤ}
    (ha : Function.Injective fun r => (Int.castRingHom (ZMod p)) (a r)) {m ex : S → ℕ} {q : S → MPT[X]}
    (hq : LocalOK p Δ a m ex q) (hqd : ∀ r, (q r).natDegree ≤ m r) (d : ℕ) (hN : ∑ r, m r + d = 3 * n)
    (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin (3 * n)) (E : ℤ)
    (hG : GV p E (Matrix.of fun x y : (Σ r : S, Fin (m r)) ⊕ Fin d =>
      laiLTx (p := p) n K σ cl τu τv
        (famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d x *
          famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d y)).det) :
    GV p (E - nuP n p) (laiJ n) := by
  have hdeg := famFun_natDegree_lt (a := a) hqd d (3 * n) hN
  have hgram := gram_det_gen (fun i => laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ i)) (3 * n) e
    (famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d) hdeg
  have hG' : GV p E ((coeffMatG (3 * n) (fun z => famFun (fun r => Polynomial.X - Polynomial.C (zphi (a r))) q m d
      (e.symm z))).det ^ 2 *
      (hankelG (fun i => laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ i)) (3 * n)).det) := by
    rw [← hgram]; exact hG
  have hU := (fam_det_unit hΔ ha hq d (3 * n) hN e).pow 2
  have h1 := GV.of_unit_mul hU hG'
  exact GV_laiJ_of_det (p := p) n E (GV_det_transfer n K σ cl τu τv hτu hτv E h1)

end Terminal

/-! ### Part 11: the scaled orthogonal polynomial (Cramer form) -/

section OrthA

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- Coefficients `a_j` of the Cramer form of the orthogonal polynomial: no division. -/
noncomputable def orthCoef {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) : Fin μ → R :=
  fun j => -((Matrix.of fun i j : Fin μ => c ((i : ℕ) + j)).adjugate.mulVec
    (fun i : Fin μ => c ((i : ℕ) + μ))) j

/-- The Hankel determinant `Δ`. -/
noncomputable def orthDet {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) : R :=
  (Matrix.of fun i j : Fin μ => c ((i : ℕ) + j)).det

/-- `Δ y^μ + ∑_j a_j y^j`, the `Δ`-multiple of the monic `𝓛`-orthogonal polynomial of degree `μ`. -/
noncomputable def orthA {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) : R[X] :=
  Polynomial.C (orthDet c μ) * Polynomial.X ^ μ +
    ∑ j : Fin μ, Polynomial.C (orthCoef c μ j) * Polynomial.X ^ (j : ℕ)

lemma orth_key {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) (i : Fin μ) :
    orthDet c μ * c ((i : ℕ) + μ) + ∑ j : Fin μ, orthCoef c μ j * c ((i : ℕ) + j) = 0 := by
  set H : Matrix (Fin μ) (Fin μ) R := Matrix.of fun i j => c ((i : ℕ) + j) with hH
  set v : Fin μ → R := fun i => c ((i : ℕ) + μ) with hv
  have h1 : H.mulVec (H.adjugate.mulVec v) = H.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun h1 i
  have key : ∑ j : Fin μ, orthCoef c μ j * c ((i : ℕ) + j) = -(H.mulVec (H.adjugate.mulVec v)) i := by
    simp only [Matrix.mulVec, dotProduct, orthCoef]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hH, Matrix.of_apply]
    ring
  rw [key, h2]
  simp only [Pi.smul_apply, smul_eq_mul, hv, orthDet, hH]
  ring

lemma orthA_natDegree_le {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) : (orthA c μ).natDegree ≤ μ := by
  unfold orthA
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact Polynomial.natDegree_C_mul_X_pow_le _ _
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans j.2.le

lemma orthA_coeff_top {R : Type*} [CommRing R] (c : ℕ → R) (μ : ℕ) : (orthA c μ).coeff μ = orthDet c μ := by
  unfold orthA
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, if_pos rfl, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_zero, add_zero]
  intro j _
  rw [Polynomial.coeff_C_mul_X_pow, if_neg (by have := j.2; omega)]

/-- **Orthogonality** of the scaled polynomial: `𝓛(y^i · Δπ) = 0` for `i < μ`. -/
theorem orthA_orth {R : Type*} [CommRing R] (c : ℕ → R) (μ i : ℕ) (hi : i < μ) :
    linM c (Polynomial.X ^ i * orthA c μ) = 0 := by
  unfold orthA
  rw [mul_add, linM_add, Finset.mul_sum, linM_sum]
  have e1 : (Polynomial.X : R[X]) ^ i * (Polynomial.C (orthDet c μ) * Polynomial.X ^ μ) =
      Polynomial.C (orthDet c μ) * Polynomial.X ^ (i + μ) := by rw [pow_add]; ring
  have e2 : ∀ j : Fin μ, (Polynomial.X : R[X]) ^ i * (Polynomial.C (orthCoef c μ j) * Polynomial.X ^ (j : ℕ)) =
      Polynomial.C (orthCoef c μ j) * Polynomial.X ^ (i + (j : ℕ)) := fun j => by rw [pow_add]; ring
  simp only [e2, e1, linM_monomial]
  have := orth_key c μ ⟨i, hi⟩
  simpa using this

lemma GV_adjugate_entry {σ : Type*} {μ : ℕ} (M : Matrix (Fin μ) (Fin μ) (MvPolynomial σ ℚ))
    (h : ∀ i j, GV p 0 (M i j)) (i j : Fin μ) : GV p 0 (M.adjugate i j) := by
  rw [Matrix.adjugate_apply]
  refine GV.det_zero _ fun i' j' => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact GV.one
    · exact GV.zero _
  · exact h _ _

/-- The scaled orthogonal polynomial has integral coefficients when the moments are integral. -/
lemma orthA_pint (c : ℕ → MPT) (μ : ℕ) (hc : ∀ i, GV p 0 (c i)) :
    PInt p (orthA c μ) := by
  have hH : ∀ i j : Fin μ, GV p 0 ((Matrix.of fun i j : Fin μ => c ((i : ℕ) + j)) i j) := fun i j => hc _
  have hΔ : GV p 0 (orthDet c μ) := GV.det_zero _ hH
  have ha : ∀ j, GV p 0 (orthCoef c μ j) := fun j => by
    unfold orthCoef
    refine GV.neg ?_
    simp only [Matrix.mulVec, dotProduct]
    refine GV.sum fun k _ => ?_
    simpa using (GV_adjugate_entry _ hH j k).mul (hc _)
  unfold orthA
  exact (PInt.C_mul hΔ (PInt_X.pow μ)).add (PInt.sum fun j _ => PInt.C_mul (ha j) (PInt_X.pow j))

end OrthA

/-! ### Part 12: the local moments and the Gauss unit `Δ` -/

section LocalHankel

variable {p : ℕ} [hp : Fact p.Prime]

/-- The moments `𝓛_T(y^i) = ∑_{ℓ=1}^{L} [T^v_ℓ (-ℓ)^i + T^u_ℓ · i (-ℓ)^{i-1}]` of the local generic
functional `𝓛_T(φ) = ∑_ℓ [T^v_ℓ φ(-ℓ) + T^u_ℓ φ'(-ℓ)]`. -/
noncomputable def cLoc (L : ℕ) (i : ℕ) : MPT :=
  ∑ l ∈ range L, (Tv (l + 1) * MvPolynomial.C ((-((l + 1 : ℕ) : ℚ)) ^ i) +
    Tu (l + 1) * MvPolynomial.C ((i : ℚ) * (-((l + 1 : ℕ) : ℚ)) ^ (i - 1)))

lemma GV_cLoc (L i : ℕ) : GV p 0 (cLoc L i) := by
  unfold cLoc
  refine GV.sum fun l _ => ?_
  have a1 : GV p 0 (MvPolynomial.C ((-((l + 1 : ℕ) : ℚ)) ^ i) : MPT) :=
    GV.const_loc ((LocRing p).pow_mem ((LocRing p).neg_mem (natq_mem _)) _)
  have a2 : GV p 0 (MvPolynomial.C ((i : ℚ) * (-((l + 1 : ℕ) : ℚ)) ^ (i - 1)) : MPT) :=
    GV.const_loc ((LocRing p).mul_mem (natq_mem i) ((LocRing p).pow_mem ((LocRing p).neg_mem (natq_mem _)) _))
  have b1 := (GV.var (p := p) (Sum.inr (l + 1, true) : TVar)).mul a1
  have b2 := (GV.var (p := p) (Sum.inr (l + 1, false) : TVar)).mul a2
  simpa [Tv, Tu] using b1.add b2

/-- **Lemma H (Gauss-unit form).**  For `L < p` and `μ ≤ 2L` the Hankel determinant `Δ` of the generic
local functional is a Gauss unit: it has content `0`, because a specialisation of `T` to `0/1`
gives the integer Hankel determinant of a functional with node multiplicities in `{0,1,2}`, which is
nonzero mod `p` by `hankel_det_ne_zero`. -/
theorem cLoc_delta_unit (L μ : ℕ) (hL : L < p) (hμ : μ ≤ 2 * L) : GUnit p (orthDet (cLoc L) μ) := by
  refine ⟨GV.det_zero _ fun i j => GV_cLoc L _, fun h1 => ?_⟩
  obtain ⟨m, hm2, hmsum⟩ := exists_mult L μ hμ
  set mu : ℕ → ℕ := fun l => if h : 1 ≤ l ∧ l - 1 < L then m ⟨l - 1, h.2⟩ else 0 with hmu
  have hmu' : ∀ l : Fin L, mu ((l : ℕ) + 1) = m l := by
    intro l
    simp [hmu]
  set τ : TVar → ℚ := fun v => match v with
    | Sum.inl _ => 0
    | Sum.inr (l, true) => if mu l = 1 then 1 else 0
    | Sum.inr (l, false) => if mu l = 2 then 1 else 0 with hτdef
  have hτ : ∀ v, τ v ∈ LocRing p := by
    rintro (i | ⟨l, _ | _⟩)
    · exact (LocRing p).zero_mem
    · simp only [hτdef]; split_ifs <;> simp [(LocRing p).one_mem, (LocRing p).zero_mem]
    · simp only [hτdef]; split_ifs <;> simp [(LocRing p).one_mem, (LocRing p).zero_mem]
  have h2 := GV.evalPt h1 τ hτ
  set Hz : Matrix (Fin μ) (Fin μ) ℤ := Matrix.of fun i j => ∑ l ∈ range L,
    ((if mu (l + 1) = 1 then 1 else 0) * (-((l + 1 : ℕ) : ℤ)) ^ ((i : ℕ) + j) +
      (if mu (l + 1) = 2 then 1 else 0) * ((((i : ℕ) + j : ℕ) : ℤ) * (-((l + 1 : ℕ) : ℤ)) ^ ((i : ℕ) + j - 1)))
    with hHz
  have hev : MvPolynomial.eval τ (orthDet (cLoc L) μ) = ((Hz.det : ℤ) : ℚ) := by
    unfold orthDet
    have hc := RingHom.map_det (Int.castRingHom ℚ) Hz
    simp only [eq_intCast] at hc
    rw [RingHom.map_det (MvPolynomial.eval τ), hc]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, hHz, cLoc, map_sum,
      map_add, map_mul, MvPolynomial.eval_C, Tu, Tv, MvPolynomial.eval_X, eq_intCast]
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [hτdef]
  have hdvd : (p : ℤ) ∣ Hz.det := by
    by_contra hnd
    refine (GUnit.C_int (σ := TVar) (p := p) Hz.det hnd).2 (GV.const ?_)
    rw [hev] at h2
    simpa using h2
  have hx : Function.Injective (fun l : Fin L => -(((l : ℕ) + 1 : ℕ) : ZMod p)) := by
    intro l l' h
    have h' : (((l : ℕ) + 1 : ℕ) : ZMod p) = (((l' : ℕ) + 1 : ℕ) : ZMod p) := neg_injective h
    have h3 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h'
    have := Nat.ModEq.eq_of_lt_of_lt h3 (by have := l.2; omega) (by have := l'.2; omega)
    exact Fin.ext (by omega)
  have hdet := CatalanCore.Content.det_intCast_zmod p μ Hz
  have h0 : ((Hz.det : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
  rw [h0] at hdet
  have hmat : (Matrix.of fun i j : Fin μ => Lfun (fun l : Fin L => -(((l : ℕ) + 1 : ℕ) : ZMod p)) m
      ((Polynomial.X : (ZMod p)[X]) ^ ((i : ℕ) + j))) = Hz.map (Int.castRingHom (ZMod p)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.map_apply, hHz, Lfun_apply, map_sum]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hmu' l]
    by_cases h2 : m l = 2
    · simp [h2, Polynomial.derivative_X_pow]
    · by_cases h1 : m l = 1
      · simp [h1]
      · simp [h1, h2]
  refine hankel_det_ne_zero (fun l : Fin L => -(((l : ℕ) + 1 : ℕ) : ZMod p)) hx m hm2 μ hmsum.symm ?_
  rw [hmat]; exact hdet.symm

end LocalHankel

/-! ### Part 13: the window family and the terminal statement -/

section Window

variable {p : ℕ} [hp : Fact p.Prime] {S : Type*} [Fintype S] [DecidableEq S]

lemma sX_eq_sub (r : ℕ) : sX r = Polynomial.X - Polynomial.C (zphi (-(r : ℤ))) := by
  unfold sX
  rw [zphi_apply]
  simp [sub_eq_add_neg]

/-- The local factors of the root-shifted Δ-scaled basis: `P_s` on the window, `(X + r)^{m_r}` off it,
satisfy `LocalOK` with `Δ = A_μ` and the exponents `1` on the window and `0` off it. -/
theorem localOK_window {Δ : MPT} {A : MPT[X]} {μ : ℕ} (hA : PInt p A) (hAtop : A.coeff μ = Δ)
    (res : S → ℕ) (Wp : S → Prop) [DecidablePred Wp] (m : S → ℕ) (hm : ∀ r, Wp r → m r = μ)
    (q : S → MPT[X]) (hqW : ∀ r, Wp r → q r = shiftP p μ (res r) A)
    (hqN : ∀ r, ¬ Wp r → q r = sX (res r) ^ m r) :
    LocalOK p Δ (fun r => -(res r : ℤ)) m (fun r => if Wp r then 1 else 0) q := by
  intro r
  have e : (Polynomial.X - Polynomial.C (zphi (-(res r : ℤ))) : MPT[X]) = sX (res r) := (sX_eq_sub _).symm
  show PInt p (q r) ∧ PCong p (q r)
    (Polynomial.C (Δ ^ (if Wp r then 1 else 0)) * (Polynomial.X - Polynomial.C (zphi (-(res r : ℤ)))) ^ m r)
  rw [e]
  by_cases hr : Wp r
  · rw [hqW r hr, if_pos hr, hm r hr, pow_one]
    refine ⟨PInt_shiftP μ _ hA, ?_⟩
    simpa [hAtop] using shiftP_cong μ (res r) hA
  · rw [hqN r hr, if_neg hr, pow_zero, Polynomial.C_1, one_mul]
    exact ⟨(PInt_sX _).pow _, PCong.refl _⟩

/-- Degrees of the local factors. -/
lemma localdeg_window {A : MPT[X]} {μ : ℕ} (hAd : A.natDegree ≤ μ)
    (res : S → ℕ) (Wp : S → Prop) [DecidablePred Wp] (m : S → ℕ) (hm : ∀ r, Wp r → m r = μ)
    (q : S → MPT[X]) (hqW : ∀ r, Wp r → q r = shiftP p μ (res r) A)
    (hqN : ∀ r, ¬ Wp r → q r = sX (res r) ^ m r) : ∀ r, (q r).natDegree ≤ m r := by
  intro r
  by_cases hr : Wp r
  · rw [hqW r hr, hm r hr]; exact shiftP_natDegree_le p μ _ A
  · rw [hqN r hr]
    refine Polynomial.natDegree_pow_le.trans ?_
    rw [sX_natDegree]; simp

/-- **The Δ-scaled root-shifted basis over generic `T`: terminal statement.**  For a window `Wp` of
residues (with local multiplicity `μ ≤ 2L`, `L < p`), the family built from `P_s = shiftP … (orthA …)`
on the window and `(X + r)^{m_r}` off it has Gram determinant under `L_T` of content `≥ E` only if
`J_n` has content `≥ E - ν_p`. -/
theorem GV_laiJ_of_window (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ)
    (hτu : ∀ l, τu l ∈ LocRing p) (hτv : ∀ l, τv l ∈ LocRing p) (L μ : ℕ) (hL : L < p) (hμ : μ ≤ 2 * L)
    (res : S → ℕ) (hres : Function.Injective fun r => ((-(res r : ℤ) : ℤ) : ZMod p))
    (Wp : S → Prop) [DecidablePred Wp] (m : S → ℕ) (hm : ∀ r, Wp r → m r = μ)
    (q : S → MPT[X]) (hqW : ∀ r, Wp r → q r = shiftP p μ (res r) (orthA (cLoc L) μ))
    (hqN : ∀ r, ¬ Wp r → q r = sX (res r) ^ m r)
    (d : ℕ) (hN : ∑ r, m r + d = 3 * n)
    (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin (3 * n)) (E : ℤ)
    (hG : GV p E (Matrix.of fun x y : (Σ r : S, Fin (m r)) ⊕ Fin d =>
      laiLTx (p := p) n K σ cl τu τv
        (famFun (fun r => Polynomial.X - Polynomial.C (zphi (-(res r : ℤ)))) q m d x *
          famFun (fun r => Polynomial.X - Polynomial.C (zphi (-(res r : ℤ)))) q m d y)).det) :
    GV p (E - nuP n p) (laiJ n) := by
  have hA : PInt p (orthA (cLoc L) μ) := orthA_pint _ _ (fun i => GV_cLoc L i)
  have hok := localOK_window (Δ := orthDet (cLoc L) μ) (A := orthA (cLoc L) μ) (μ := μ) hA
    (orthA_coeff_top _ _) res Wp m hm q hqW hqN
  have hqd := localdeg_window (orthA_natDegree_le (cLoc L) μ) res Wp m hm q hqW hqN
  exact GV_laiJ_of_famT n K σ cl τu τv hτu hτv (a := fun r => -(res r : ℤ)) (cLoc_delta_unit L μ hL hμ)
    (by simpa using hres) hok hqd d hN e E hG

end Window

end CatalanCore.Lai

#print axioms CatalanCore.Lai.GV.of_unit_mul
#print axioms CatalanCore.Lai.gram_det_gen
#print axioms CatalanCore.Lai.GV_transfer
#print axioms CatalanCore.Lai.laiLTx_nodes
#print axioms CatalanCore.Lai.ndT_ge
#print axioms CatalanCore.Lai.ndT0_ge
#print axioms CatalanCore.Lai.ndT_modNdT_lead
#print axioms CatalanCore.Lai.nodeT_ge
#print axioms CatalanCore.Lai.laiLTx_ge_except
#print axioms CatalanCore.Lai.shiftP_eval
#print axioms CatalanCore.Lai.shiftP_deriv
#print axioms CatalanCore.Lai.shiftP_cong
#print axioms CatalanCore.Lai.fam_det_unit
#print axioms CatalanCore.Lai.GV_laiJ_of_famT
#print axioms CatalanCore.Lai.orthA_orth
#print axioms CatalanCore.Lai.orthA_pint
#print axioms CatalanCore.Lai.cLoc_delta_unit
#print axioms CatalanCore.Lai.GV_laiJ_of_window
