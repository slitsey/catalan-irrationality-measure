module

public import CatalanCore.Zeta5.Parity.Symbol
public import CatalanCore.Zeta5.Local.Tate
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section

/-!
# ZC06(b), part 1: reduction modulo `p` and the full local symbol

* `red`: the reduction `ℚ → 𝔽_p` is the cast `(q : ZMod p)`; it is additive and multiplicative on
  `p`-integral rationals (`red_add`, `red_mul`, …), kills `p ℤ_(p)` (`red_zero_of_VG_one`), and
  detects it (`VG_one_of_red`).
* `redP`: coefficientwise reduction `ℚ[X] → 𝔽_p[X]`, a ring map on `ℤ_(p)[X]`.
* `polySym W = ∑_{n < p} (W mod (X^p - X))_n · red τ(x^n)`: the reduction of `τ` on `𝔽_p[X]`
  (`polySym_red`: `red τ(P) = polySym (P mod p)` for `P ∈ ℤ_(p)[X]` of degree `≤ p`).  It is odd
  under `J : W ↦ W(-1-X)` (`polySym_Jr`).
* `locSym I W = polySym (W div B_I) + ∑_{k ∈ I} res_k(W / B_I) H⁽⁵⁾_{d(k)}`: the full own-source
  symbol of a local pole set `I` (polynomial part of the quotient included).  For an even
  `refl`-symmetric `I` it is odd under `J` (`locSym_Jr`), and `fullSym I` is the bilinear form
  `(U, V) ↦ locSym I (U V)` (the field `Cf` of `ParityData`, (H′)).
-/

open Finset Polynomial

namespace Apery

section red
variable {p : ℕ} [hp : Fact p.Prime]

lemma val_le_neg_one_of_dvd_den {q : ℚ} (hq : q ≠ 0) (hd : p ∣ q.den) :
    padicValRat p q ≤ -1 := by
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [show Nat.gcd q.num.natAbs q.den = 1 from q.reduced] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have h0 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
  have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hd
  have : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
  omega

lemma den_ne_zero_of_VG {q : ℚ} (h : VG p q 0) : ((q.den : ℕ) : ZMod p) ≠ 0 := by
  intro hd
  rw [ZMod.natCast_eq_zero_iff] at hd
  rcases h with h0 | h
  · rw [h0] at hd
    simp only [Rat.den_ofNat, Nat.dvd_one] at hd
    exact hp.out.one_lt.ne' hd
  · have hq : q ≠ 0 := by
      rintro rfl
      exact hp.out.one_lt.ne' (Nat.dvd_one.mp (by simpa using hd))
    have := val_le_neg_one_of_dvd_den hq hd
    have h' : (0 : ℚ) ≤ padicValRat p q := h
    have : (padicValRat p q : ℚ) ≤ -1 := by exact_mod_cast this
    linarith

lemma red_zero_of_VG_one {q : ℚ} (h : VG p q 1) : (q : ZMod p) = 0 := by
  rcases h with h0 | h
  · simp [h0]
  have hq : q ≠ 0 := by rintro rfl; rw [padicValRat.zero] at h; norm_num at h
  have hd : ¬ p ∣ q.den := by
    intro hd
    have := val_le_neg_one_of_dvd_den hq hd
    have : (padicValRat p q : ℚ) ≤ -1 := by exact_mod_cast this
    linarith
  have hv : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
  rw [padicValNat.eq_zero_of_not_dvd hd] at hv
  have h1 : 1 ≤ padicValInt p q.num := by
    have : (1 : ℚ) ≤ padicValRat p q := h
    have : (1 : ℤ) ≤ padicValRat p q := by exact_mod_cast this
    omega
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hdvd : (p : ℤ) ∣ q.num := by
    have := (padicValInt_dvd_iff (p := p) 1 q.num).mpr (Or.inr h1)
    simpa using this
  rw [Rat.cast_def, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd, zero_div]

lemma VG_one_of_red {q : ℚ} (h0 : VG p q 0) (hr : (q : ZMod p) = 0) : VG p q 1 := by
  by_cases hq : q = 0
  · left; exact hq
  right
  have hd := den_ne_zero_of_VG h0
  have hd' : ¬ p ∣ q.den := fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mpr h)
  rw [Rat.cast_def] at hr
  have hn : ((q.num : ℤ) : ZMod p) = 0 := by
    rcases div_eq_zero_iff.mp hr with h | h
    · exact h
    · exact absurd h hd
  have hdvd : (p : ℤ) ∣ q.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
  have hnum0 : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have h1 := (padicValInt_dvd_iff (p := p) 1 q.num).mp (by simpa using hdvd)
  rcases h1 with h1 | h1
  · exact absurd h1 hnum0
  have hv : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
  rw [padicValNat.eq_zero_of_not_dvd hd'] at hv
  have : (1 : ℤ) ≤ padicValRat p q := by omega
  exact_mod_cast this

lemma red_add {q r : ℚ} (hq : VG p q 0) (hr : VG p r 0) :
    ((q + r : ℚ) : ZMod p) = (q : ZMod p) + r :=
  Rat.cast_add_of_ne_zero (den_ne_zero_of_VG hq) (den_ne_zero_of_VG hr)

lemma red_sub {q r : ℚ} (hq : VG p q 0) (hr : VG p r 0) :
    ((q - r : ℚ) : ZMod p) = (q : ZMod p) - r :=
  Rat.cast_sub_of_ne_zero (den_ne_zero_of_VG hq) (den_ne_zero_of_VG hr)

lemma red_mul {q r : ℚ} (hq : VG p q 0) (hr : VG p r 0) :
    ((q * r : ℚ) : ZMod p) = (q : ZMod p) * r :=
  Rat.cast_mul_of_ne_zero (den_ne_zero_of_VG hq) (den_ne_zero_of_VG hr)

lemma red_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, VG p (f i) 0) :
    ((∑ i ∈ s, f i : ℚ) : ZMod p) = ∑ i ∈ s, ((f i : ℚ) : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      red_add (h a (mem_insert_self _ _)) (VG.sum _ fun i hi => h i (mem_insert_of_mem hi)),
      ih fun i hi => h i (mem_insert_of_mem hi)]

lemma red_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, VG p (f i) 0) :
    ((∏ i ∈ s, f i : ℚ) : ZMod p) = ∏ i ∈ s, ((f i : ℚ) : ZMod p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hprod : VG p (∏ i ∈ s, f i) 0 := by
      have := VG.prod (p := p) s (r := fun _ => (0 : ℚ)) fun i hi => h i (mem_insert_of_mem hi)
      simpa using this
    rw [Finset.prod_insert ha, Finset.prod_insert ha, red_mul (h a (mem_insert_self _ _)) hprod,
      ih fun i hi => h i (mem_insert_of_mem hi)]

lemma red_pow {q : ℚ} (hq : VG p q 0) (n : ℕ) : ((q ^ n : ℚ) : ZMod p) = (q : ZMod p) ^ n := by
  have := red_prod (p := p) (Finset.range n) (fun _ => q) (fun _ _ => hq)
  simpa using this

lemma red_inv {q : ℚ} (hq : VG p q 0) (hqi : VG p q⁻¹ 0) :
    ((q⁻¹ : ℚ) : ZMod p) = (q : ZMod p)⁻¹ := by
  by_cases h0 : q = 0
  · simp [h0]
  have : (q : ZMod p) * ((q⁻¹ : ℚ) : ZMod p) = 1 := by
    rw [← red_mul hq hqi, mul_inv_cancel₀ h0, Rat.cast_one]
  exact (eq_inv_of_mul_eq_one_right this)

lemma red_congr {q r : ℚ} (hq : VG p q 0) (hr : VG p r 0) (h : VG p (q - r) 1) :
    (q : ZMod p) = r := by
  have := red_zero_of_VG_one h
  rw [red_sub hq hr] at this
  exact sub_eq_zero.mp this

lemma red_intCast (z : ℤ) : (((z : ℚ)) : ZMod p) = (z : ZMod p) := Rat.cast_intCast z

lemma red_natCast (n : ℕ) : (((n : ℚ)) : ZMod p) = (n : ZMod p) := Rat.cast_natCast n

/-- A `p`-unit reduces to a nonzero residue. -/
lemma red_ne_zero {q : ℚ} (h0 : q ≠ 0) (hq : VG p q 0) (hqi : VG p q⁻¹ 0) :
    (q : ZMod p) ≠ 0 := by
  intro h
  have := red_mul hq hqi
  rw [mul_inv_cancel₀ h0, Rat.cast_one, h, zero_mul] at this
  exact one_ne_zero this

/-! ### Coefficientwise reduction of polynomials -/

/-- Coefficientwise reduction `ℚ[X] → 𝔽_p[X]`. -/
noncomputable def redP (p : ℕ) [Fact p.Prime] (P : ℚ[X]) : (ZMod p)[X] :=
  ∑ n ∈ range (P.natDegree + 1), C ((P.coeff n : ℚ) : ZMod p) * X ^ n

lemma coeff_redP (P : ℚ[X]) (n : ℕ) : (redP p P).coeff n = ((P.coeff n : ℚ) : ZMod p) := by
  unfold redP
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using h)]; simp

lemma redP_ext {P : ℚ[X]} {W : (ZMod p)[X]} (h : ∀ n, ((P.coeff n : ℚ) : ZMod p) = W.coeff n) :
    redP p P = W := by
  ext n; rw [coeff_redP, h]

lemma natDegree_redP_le (P : ℚ[X]) : (redP p P).natDegree ≤ P.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_redP, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn)]; simp

lemma redP_C (c : ℚ) : redP p (C c) = C (c : ZMod p) := by
  refine redP_ext fun n => ?_
  rw [coeff_C, coeff_C]; split_ifs <;> simp

lemma redP_X : redP p (X : ℚ[X]) = X := by
  refine redP_ext fun n => ?_
  rw [coeff_X, coeff_X]; split_ifs <;> simp

lemma redP_neg (P : ℚ[X]) : redP p (-P) = -redP p P := by
  refine redP_ext fun n => ?_
  rw [coeff_neg, coeff_neg, coeff_redP, Rat.cast_neg]

lemma redP_add {P Q : ℚ[X]} (hP : GV p P 0) (hQ : GV p Q 0) :
    redP p (P + Q) = redP p P + redP p Q := by
  refine redP_ext fun n => ?_
  rw [coeff_add, coeff_add, coeff_redP, coeff_redP, red_add (hP n) (hQ n)]

lemma redP_sub {P Q : ℚ[X]} (hP : GV p P 0) (hQ : GV p Q 0) :
    redP p (P - Q) = redP p P - redP p Q := by
  refine redP_ext fun n => ?_
  rw [coeff_sub, coeff_sub, coeff_redP, coeff_redP, red_sub (hP n) (hQ n)]

lemma redP_mul {P Q : ℚ[X]} (hP : GV p P 0) (hQ : GV p Q 0) :
    redP p (P * Q) = redP p P * redP p Q := by
  refine redP_ext fun n => ?_
  rw [coeff_mul, coeff_mul, red_sum _ _ fun x _ => by simpa using (hP x.1).mul (hQ x.2)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [red_mul (hP x.1) (hQ x.2), coeff_redP, coeff_redP]

lemma redP_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, GV p (f i) 0) :
    redP p (∑ i ∈ s, f i) = ∑ i ∈ s, redP p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redP_C (p := p) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      redP_add (h a (mem_insert_self _ _)) (GV.sum _ fun i hi => h i (mem_insert_of_mem hi)),
      ih fun i hi => h i (mem_insert_of_mem hi)]

lemma GV_prod0 {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, GV p (f i) 0) :
    GV p (∏ i ∈ s, f i) 0 := by
  have := GV.prod (p := p) s (r := fun _ => (0 : ℚ)) h
  simpa using this

lemma redP_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, GV p (f i) 0) :
    redP p (∏ i ∈ s, f i) = ∏ i ∈ s, redP p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using redP_C (p := p) 1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      redP_mul (h a (mem_insert_self _ _)) (GV_prod0 _ _ fun i hi => h i (mem_insert_of_mem hi)),
      ih fun i hi => h i (mem_insert_of_mem hi)]

lemma redP_pow {P : ℚ[X]} (hP : GV p P 0) (n : ℕ) : redP p (P ^ n) = redP p P ^ n := by
  have := redP_prod (p := p) (Finset.range n) (fun _ => P) (fun _ _ => hP)
  simpa using this

lemma redP_C_mul {c : ℚ} {P : ℚ[X]} (hc : VG p c 0) (hP : GV p P 0) :
    redP p (C c * P) = C (c : ZMod p) * redP p P := by
  rw [redP_mul (GV.C hc) hP, redP_C]

lemma redP_eq_zero_of_GV_one {P : ℚ[X]} (h : GV p P 1) : redP p P = 0 := by
  refine redP_ext fun n => ?_
  rw [coeff_zero]; exact red_zero_of_VG_one (h n)

lemma GV_one_of_redP {P : ℚ[X]} (h0 : GV p P 0) (h : redP p P = 0) : GV p P 1 := fun n => by
  refine VG_one_of_red (h0 n) ?_
  rw [← coeff_redP, h, coeff_zero]

lemma redP_congr {P Q : ℚ[X]} (hP : GV p P 0) (hQ : GV p Q 0) (h : GV p (P - Q) 1) :
    redP p P = redP p Q := by
  have := redP_eq_zero_of_GV_one h
  rw [redP_sub hP hQ] at this
  exact sub_eq_zero.mp this

lemma eval_eq_sum_range_le {R : Type*} [CommSemiring R] (P : R[X]) {d : ℕ} (hd : P.natDegree ≤ d)
    (x : R) : P.eval x = ∑ n ∈ range (d + 1), P.coeff n * x ^ n :=
  eval_eq_sum_range' (by omega) x

lemma redP_eval {P : ℚ[X]} (hP : GV p P 0) {x : ℚ} (hx : VG p x 0) :
    ((P.eval x : ℚ) : ZMod p) = (redP p P).eval (x : ZMod p) := by
  rw [eval_eq_sum_range_le P le_rfl, eval_eq_sum_range_le (redP p P) (natDegree_redP_le P),
    red_sum _ _ fun n _ => by simpa using (hP n).mul (hx.pow n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [red_mul (hP n) (by simpa using hx.pow n), red_pow hx, coeff_redP]

lemma comp_eq_sum_le {R : Type*} [CommSemiring R] (P G : R[X]) {d : ℕ} (hd : P.natDegree ≤ d) :
    P.comp G = ∑ n ∈ range (d + 1), C (P.coeff n) * G ^ n := by
  conv_lhs => rw [P.as_sum_range' (d + 1) (by omega)]
  rw [comp, eval₂_finsetSum]
  simp

lemma redP_comp {P G : ℚ[X]} (hP : GV p P 0) (hG : GV p G 0) :
    redP p (P.comp G) = (redP p P).comp (redP p G) := by
  rw [comp_eq_sum_le P G le_rfl, comp_eq_sum_le (redP p P) (redP p G) (natDegree_redP_le P),
    redP_sum _ _ fun n _ => by simpa using (GV.C (hP n)).mul (GV.pow hG n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [redP_mul (GV.C (hP n)) (by simpa using GV.pow hG n), redP_C, redP_pow hG, coeff_redP]

lemma GV_redP_X_sub_C (z : ℤ) : redP p (X - C (z : ℚ)) = X - C (z : ZMod p) := by
  rw [redP_sub GV.X (GV.C (VG.intCast z)), redP_X, redP_C, red_intCast]

/-- Lift of an `𝔽_p`-polynomial to `ℤ_(p)[X]` (coefficients in `[0, p)`). -/
noncomputable def liftP (p : ℕ) [Fact p.Prime] (W : (ZMod p)[X]) : ℚ[X] :=
  ∑ n ∈ range (W.natDegree + 1), C ((((W.coeff n).val : ℕ) : ℚ)) * X ^ n

lemma coeff_liftP (W : (ZMod p)[X]) (n : ℕ) : (liftP p W).coeff n = (((W.coeff n).val : ℕ) : ℚ) := by
  unfold liftP
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by simpa using h)]; simp

lemma GV_liftP (W : (ZMod p)[X]) : GV p (liftP p W) 0 := fun n => by
  rw [coeff_liftP]; exact VG.natCast _

lemma redP_liftP (W : (ZMod p)[X]) : redP p (liftP p W) = W := by
  refine redP_ext fun n => ?_
  rw [coeff_liftP, red_natCast, ZMod.natCast_zmod_val]

lemma natDegree_liftP_le (W : (ZMod p)[X]) : (liftP p W).natDegree ≤ W.natDegree := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_liftP, coeff_eq_zero_of_natDegree_lt (by exact_mod_cast hn)]; simp

end red

/-! ### The reduced Tate functional `polySym` -/

section poly
variable {p : ℕ} [hp : Fact p.Prime]

/-- `X^p - X`. -/
noncomputable def gX (p : ℕ) : (ZMod p)[X] := X ^ p - X

lemma gX_monic : (gX p).Monic := by
  unfold gX
  refine monic_X_pow_sub ?_
  rw [degree_X]; exact_mod_cast hp.out.one_lt

lemma natDegree_gX : (gX p).natDegree = p :=
  FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp.out.one_lt

/-- The reduction of `τ` on `𝔽_p[X]`: `∑_{n < p} (W mod (X^p - X))_n · red τ(x^n)`. -/
noncomputable def polySym (p : ℕ) [Fact p.Prime] (W : (ZMod p)[X]) : ZMod p :=
  ∑ n ∈ range p, (W %ₘ gX p).coeff n * ((tau (X ^ n) : ℚ) : ZMod p)

lemma polySym_add (W V : (ZMod p)[X]) : polySym p (W + V) = polySym p W + polySym p V := by
  unfold polySym
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_modByMonic, coeff_add]; ring

lemma polySym_smul (c : ZMod p) (W : (ZMod p)[X]) : polySym p (c • W) = c * polySym p W := by
  unfold polySym
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [smul_modByMonic, coeff_smul, smul_eq_mul]; ring

lemma polySym_mod (W : (ZMod p)[X]) : polySym p (W %ₘ gX p) = polySym p W := by
  unfold polySym
  rw [(modByMonic_eq_self_iff gX_monic).mpr (degree_modByMonic_lt _ gX_monic)]

lemma polySym_add_gX_mul (W V : (ZMod p)[X]) : polySym p (W + gX p * V) = polySym p W := by
  have : (gX p * V) %ₘ gX p = 0 := (modByMonic_eq_zero_iff_dvd gX_monic).mpr (dvd_mul_right _ _)
  unfold polySym
  rw [add_modByMonic, this, add_zero]

lemma red_tau_X_pow_p (hp5 : 5 ≤ p) : ((tau (X ^ p) : ℚ) : ZMod p) = 0 := by
  refine red_zero_of_VG_one ?_
  rw [tau_X_pow, div_eq_mul_inv]
  have h3 : p.descFactorial 3 = p * ((p - 1) * (p - 2)) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.descFactorial_succ, show (2 : ℕ) = 1 + 1 from rfl,
      Nat.descFactorial_succ, Nat.descFactorial_one]
    ring_nf
  have h1 : VG p ((p.descFactorial 3 : ℕ) : ℚ) 1 := by
    rw [h3]; push_cast
    have := (VG.primePow (p := p) 1).mul (VG.natCast (p := p) ((p - 1) * (p - 2)))
    simpa using this
  have h2 := VG_bernoulli_lt hp5 (n := p - 3) (by omega)
  have := (h1.mul h2).mul (VG_inv24 hp5)
  simpa using this

lemma tau_X_eq : tau (X : ℚ[X]) = 0 := by
  have := tau_X_pow 1
  simpa using this

/-- The reduction of `τ`: `red τ(P) = polySym (P mod p)` for `P ∈ ℤ_(p)[X]` of degree `≤ p`. -/
theorem polySym_red (hp5 : 5 ≤ p) {P : ℚ[X]} (hP : GV p P 0) (hd : P.natDegree ≤ p) :
    ((tau P : ℚ) : ZMod p) = polySym p (redP p P) := by
  set W := redP p P with hW
  have hWd : W.natDegree ≤ p := (natDegree_redP_le P).trans hd
  -- `W mod (X^p - X) = W - C W_p (X^p - X)`
  have hmod : W %ₘ gX p = W - C (W.coeff p) * gX p := by
    have := (div_modByMonic_unique (C (W.coeff p)) (W - C (W.coeff p) * gX p) gX_monic
      ⟨by ring, ?_⟩).2
    · exact this
    rw [degree_eq_natDegree gX_monic.ne_zero, natDegree_gX, degree_lt_iff_coeff_zero]
    intro m hm
    have hm' : p ≤ m := by exact_mod_cast hm
    rw [coeff_sub, coeff_C_mul]
    rcases eq_or_lt_of_le hm' with rfl | hlt
    · have : (gX p).coeff p = 1 := by
        have := gX_monic (p := p); rw [Monic, leadingCoeff, natDegree_gX] at this; exact this
      rw [this]; ring
    · have e1 : W.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have e2 : (gX p).coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [natDegree_gX]; omega)
      rw [e1, e2]; ring
  have hcoef : ∀ n < p, (W %ₘ gX p).coeff n = W.coeff n + (if n = 1 then W.coeff p else 0) := by
    intro n hn
    rw [hmod, coeff_sub, coeff_C_mul]
    have : (gX p).coeff n = if n = 1 then -1 else 0 := by
      unfold gX
      rw [coeff_sub, coeff_X_pow, coeff_X, if_neg (show n ≠ p by omega)]
      by_cases h1 : n = 1
      · subst h1; simp
      · rw [if_neg h1, if_neg (fun h => h1 h.symm)]; simp
    rw [this]; split_ifs <;> ring
  -- both sides equal `∑_{n < p} W_n red τ(x^n)`
  have hint : ∀ n ∈ range (p + 1), VG p (tau (X ^ n)) 0 := fun n hn =>
    VG_tau_X_pow_int hp5 (by have := Finset.mem_range.mp hn; omega)
  have hτ : tau P = ∑ n ∈ range (p + 1), P.coeff n * tau (X ^ n) := by
    conv_lhs => rw [P.as_sum_range' (p + 1) (by omega)]
    rw [tau_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [← C_mul_X_pow_eq_monomial, tau_C_mul]
  have hL : ((tau P : ℚ) : ZMod p) =
      ∑ n ∈ range p, W.coeff n * ((tau (X ^ n) : ℚ) : ZMod p) := by
    rw [hτ, red_sum _ _ fun n hn => by simpa using (hP n).mul (hint n hn),
      Finset.sum_range_succ, red_mul (hP p) (hint p (by simp)), red_tau_X_pow_p hp5, mul_zero,
      add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [red_mul (hP n) (hint n (by have := Finset.mem_range.mp hn; simp; omega)), hW, coeff_redP]
  have hR : polySym p W = ∑ n ∈ range p, W.coeff n * ((tau (X ^ n) : ℚ) : ZMod p) := by
    unfold polySym
    rw [Finset.sum_congr rfl fun n hn => by rw [hcoef n (Finset.mem_range.mp hn)]]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : ∑ n ∈ range p, (if n = 1 then W.coeff p else 0) * ((tau (X ^ n) : ℚ) : ZMod p) =
        0 := by
      refine Finset.sum_eq_zero fun n _ => ?_
      split_ifs with h
      · subst h; rw [pow_one, tau_X_eq]; simp
      · simp
    rw [h1, add_zero]
  rw [hL, hR]

lemma Jr_gX (hp5 : 5 ≤ p) : Jr (gX p) = -gX p := by
  unfold Jr gX
  rw [sub_comp, X_pow_comp, X_comp]
  have hodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have h1 : (-X - 1 : (ZMod p)[X]) ^ p = -(X ^ p + 1) := by
    rw [show (-X - 1 : (ZMod p)[X]) = -(X + 1) by ring, hodd.neg_pow, add_pow_char, one_pow]
  rw [h1]; ring

lemma natDegree_Jr (W : (ZMod p)[X]) : (Jr W).natDegree = W.natDegree := by
  unfold Jr
  rw [natDegree_comp]
  have : (-X - 1 : (ZMod p)[X]).natDegree = 1 := by
    rw [show (1 : (ZMod p)[X]) = C 1 from rfl, natDegree_sub_C, natDegree_neg, natDegree_X]
  rw [this, mul_one]

lemma degree_Jr (W : (ZMod p)[X]) : (Jr W).degree = W.degree := by
  by_cases hW : W = 0
  · subst hW; simp [Jr]
  have hJ : Jr W ≠ 0 := by
    intro h
    apply hW
    have := congrArg Jr h
    rwa [Jr_Jr, show Jr (0 : (ZMod p)[X]) = 0 by simp [Jr]] at this
  rw [degree_eq_natDegree hW, degree_eq_natDegree hJ, natDegree_Jr]

lemma redP_Jr {P : ℚ[X]} (hP : GV p P 0) : redP p (P.comp (-X - 1)) = Jr (redP p P) := by
  have hG : GV p (-X - 1 : ℚ[X]) 0 := (GV.X.neg).sub (by simpa using GV.C (p := p) VG.one)
  rw [redP_comp hP hG, Jr]
  congr 1
  rw [redP_sub GV.X.neg (by simpa using GV.C (p := p) VG.one), redP_neg, redP_X,
    show (1 : ℚ[X]) = C 1 from rfl, redP_C]
  simp

/-- **Oddness of the reduced Tate functional.**  `polySym (J W) = - polySym W`. -/
theorem polySym_Jr (hp5 : 5 ≤ p) (W : (ZMod p)[X]) : polySym p (Jr W) = -polySym p W := by
  set W0 := W %ₘ gX p with hW0
  have hdec : W = W0 + gX p * (W /ₘ gX p) := (modByMonic_add_div W (gX p)).symm
  have hdeg0 : W0.natDegree < p := by
    have := degree_modByMonic_lt W (gX_monic (p := p))
    rw [degree_eq_natDegree gX_monic.ne_zero, natDegree_gX] at this
    by_cases h0 : W0 = 0
    · rw [h0]; simp; exact hp.out.pos
    · rwa [degree_eq_natDegree h0, Nat.cast_lt] at this
  have hJW : Jr W = Jr W0 + gX p * (-Jr (W /ₘ gX p)) := by
    conv_lhs => rw [hdec]
    rw [Jr_add, Jr_mul, Jr_gX hp5]; ring
  rw [hJW, polySym_add_gX_mul, ← polySym_mod W]
  -- lift `W0`
  set P := liftP p W0 with hP
  have hPi : GV p P 0 := GV_liftP W0
  have hPd : P.natDegree ≤ p := (natDegree_liftP_le W0).trans hdeg0.le
  have hQ : GV p (P.comp (-X - 1)) 0 := GV.comp hPi ((GV.X.neg).sub (by simpa using GV.C (p := p) VG.one))
  have hQd : (P.comp (-X - 1)).natDegree ≤ p := by
    refine natDegree_comp_le.trans ?_
    have : (-X - 1 : ℚ[X]).natDegree ≤ 1 := by
      rw [show (-X - 1 : ℚ[X]) = C (-1) * X + C (-1) by simp; ring]
      exact natDegree_linear_le
    nlinarith
  have e1 : polySym p W0 = ((tau P : ℚ) : ZMod p) := by
    rw [polySym_red hp5 hPi hPd, hP, redP_liftP]
  have e2 : polySym p (Jr W0) = ((tau (P.comp (-X - 1)) : ℚ) : ZMod p) := by
    rw [polySym_red hp5 hQ hQd, redP_Jr hPi, hP, redP_liftP]
  rw [e2, tau_comp_neg_sub_one, Rat.cast_neg, ← e1]

end poly

/-! ### The full local symbol -/

section loc
variable {p : ℕ} [hp : Fact p.Prime]

/-- The full own-source symbol of the local pole set `I`: `τ` of the polynomial part of `W / B_I`
plus `∑_{k ∈ I} res_k(W / B_I) H⁽⁵⁾_{d(k)}`, modulo `p`. -/
noncomputable def locSym (p : ℕ) [Fact p.Prime] (I : Finset ℤ) (W : (ZMod p)[X]) : ZMod p :=
  polySym p (W /ₘ piF I) + resSym I (H5w (ZMod p)) W

lemma piF_monic (I : Finset ℤ) : (piF I : (ZMod p)[X]).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma locSym_add (I : Finset ℤ) (W V : (ZMod p)[X]) :
    locSym p I (W + V) = locSym p I W + locSym p I V := by
  unfold locSym
  rw [add_divByMonic, polySym_add, resSym_add]; ring

lemma locSym_smul (I : Finset ℤ) (c : ZMod p) (W : (ZMod p)[X]) :
    locSym p I (c • W) = c * locSym p I W := by
  unfold locSym
  rw [smul_divByMonic, polySym_smul, smul_eq_C_mul, resSym_smul]; ring

/-- `locSym` as a linear functional. -/
noncomputable def locL (p : ℕ) [Fact p.Prime] (I : Finset ℤ) : (ZMod p)[X] →ₗ[ZMod p] ZMod p where
  toFun := locSym p I
  map_add' := locSym_add I
  map_smul' := locSym_smul I

/-- **(H′), the field `Cf`**: the full own-source symbol as a bilinear form,
`(U, V) ↦ locSym I (U V)`. -/
noncomputable def fullSym (p : ℕ) [Fact p.Prime] (I : Finset ℤ) :
    (ZMod p)[X] →ₗ[ZMod p] (ZMod p)[X] →ₗ[ZMod p] ZMod p :=
  (LinearMap.mul (ZMod p) (ZMod p)[X]).compr₂ (locL p I)

lemma fullSym_apply (I : Finset ℤ) (U V : (ZMod p)[X]) : fullSym p I U V = locSym p I (U * V) := rfl

lemma divByMonic_Jr {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card)
    (W : (ZMod p)[X]) : (Jr W) /ₘ piF I = Jr (W /ₘ piF I) := by
  have hB : Jr (piF I : (ZMod p)[X]) = piF I := piF_Jr hsym hev
  have hdec := modByMonic_add_div W (piF I : (ZMod p)[X])
  refine (div_modByMonic_unique (Jr (W /ₘ piF I)) (Jr (W %ₘ piF I)) (piF_monic I) ⟨?_, ?_⟩).1
  · conv_rhs => rw [← hdec]
    rw [Jr_add, Jr_mul, hB]
  · rw [degree_Jr]; exact degree_modByMonic_lt _ (piF_monic I)

/-- **ZC24, full symbol modulo `p`.**  For an even `refl`-symmetric pole set the full symbol is odd
under `J`. -/
theorem locSym_Jr (hp5 : 5 ≤ p) {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card)
    (W : (ZMod p)[X]) : locSym p I (Jr W) = -locSym p I W := by
  unfold locSym
  rw [divByMonic_Jr hsym hev, polySym_Jr hp5, zc24_odd hsym hev _ (fun k => H5w_refl k)]
  ring

theorem fullSym_odd (hp5 : 5 ≤ p) {I : Finset ℤ} (hsym : I.image refl = I) (hev : Even I.card)
    (U V : (ZMod p)[X]) : fullSym p I (Jr U) (Jr V) = -fullSym p I U V := by
  rw [fullSym_apply, fullSym_apply, ← Jr_mul, locSym_Jr hp5 hsym hev]

end loc

end Apery
