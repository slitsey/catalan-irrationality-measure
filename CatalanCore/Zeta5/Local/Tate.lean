module

public import CatalanCore.Zeta5.Local.MomentVal
public import CatalanCore.Zeta5.Local.IntPoly
public import CatalanCore.Zeta5.Local.DirectPoly
public import CatalanCore.Zeta5.Local.Pullback
public import CatalanCore.Zeta5.Local.BasisChange
public import CatalanCore.Zeta5.Local.Reflect

@[expose] public section

/-!
# Rows ZC04 and ZC05: von Staudt--Clausen integrality and the integrality (I3)

* `VG_tau_X_pow` / `VG_tau_X_pow_int`: `κ_d = τ(x^d) = d(d-1)(d-2) B_{d-3}/24` has `v_p ≥ -1` for
  every `d` and `v_p ≥ 0` for `d ≤ p+1` (`p ≥ 5`);
* `VG_tau` / `VG_tau_int`: hence `τ` on `ℤ_(p)[x]` has norm `≤ p` (loss `p`), and is
  `p`-integral on polynomials of degree `≤ p+1` (the Tate-algebra statement, polynomial form);
* `GV_polyPart`, `VG_resP_unit`: division by `∏(x - r)` and the residues at poles of pairwise unit
  difference are `p`-integral;
* `tauX_I3`: **(I3)** for `T = ∏(x - r_ν)`, `r_ν ∈ ℤ` with pairwise `p`-unit differences and
  `d(r_ν) < p`, `U_j ∈ ℤ_(p)[x]`, `deg U_0 ≤ p+1`, `Y ∈ ℤ_(p)[X]`:
  `τ_Y(∑_{j<J} p^j U_j / T) ∈ ℤ_(p)[X]`.  (Finite sums: the infinite series of the paper is the
  `p`-adic limit of these.)
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### ZC04 -/

lemma VG_neg_half (hp5 : 5 ≤ p) : VG p (-1 / 2 : ℚ) 0 := by
  have h2 : ¬ p ∣ 2 := fun h => by
    have := Nat.le_of_dvd (by norm_num) h; omega
  have : VG p ((2 : ℚ)⁻¹) 0 := by
    refine (VG.inv (r := 0) (by norm_num) ?_).mono (by norm_num)
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd h2]
    simp
  simpa [div_eq_mul_inv] using this.neg

/-- `v_p(B_n) ≥ -1` for all `n` (`p ≥ 5`). -/
lemma VG_bernoulli_all (hp5 : 5 ≤ p) (n : ℕ) : VG p (_root_.bernoulli n) (-1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
  · rw [show n = 2 * k by omega]; exact VG_bernoulli_even k
  · rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by obtain ⟨m, hm⟩ := ho; omega
      subst this
      rw [_root_.bernoulli_one]
      exact (VG_neg_half hp5).mono (by norm_num)
    · rw [_root_.bernoulli_eq_zero_of_odd ho (by omega)]
      exact VG.zero _

/-- `B_n` is `p`-integral for `n + 1 < p`. -/
lemma VG_bernoulli_lt (hp5 : 5 ≤ p) {n : ℕ} (hn : n + 1 < p) : VG p (_root_.bernoulli n) 0 := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have : n = 0 := by omega
      subst this
      simpa using VG.one (p := p)
    · rw [show n = 2 * k by omega]
      refine VG_bernoulli_even_int k fun hdvd => ?_
      have := Nat.le_of_dvd (by omega) hdvd
      omega
  · rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by obtain ⟨m, hm⟩ := ho; omega
      subst this
      rw [_root_.bernoulli_one]
      exact VG_neg_half hp5
    · rw [_root_.bernoulli_eq_zero_of_odd ho (by omega)]
      exact VG.zero _

/-- **ZC04**: `κ_d = τ(x^d)` has `v_p ≥ -1` for every `d` (`p ≥ 5`). -/
theorem VG_tau_X_pow (hp5 : 5 ≤ p) (d : ℕ) : VG p (tau (X ^ d)) (-1) := by
  rw [tau_X_pow, div_eq_mul_inv]
  have h1 : VG p ((d.descFactorial 3 : ℕ) : ℚ) 0 := VG.natCast _
  have := (h1.mul (VG_bernoulli_all hp5 (d - 3))).mul (VG_inv24 hp5)
  simpa using this

/-- **ZC04**: `κ_d` is `p`-integral for `d ≤ p + 1` (`p ≥ 5`). -/
theorem VG_tau_X_pow_int (hp5 : 5 ≤ p) {d : ℕ} (hd : d ≤ p + 1) : VG p (tau (X ^ d)) 0 := by
  rw [tau_X_pow, div_eq_mul_inv]
  have h1 : VG p ((d.descFactorial 3 : ℕ) : ℚ) 0 := VG.natCast _
  have := (h1.mul (VG_bernoulli_lt hp5 (n := d - 3) (by omega))).mul (VG_inv24 hp5)
  simpa using this

lemma tau_eq_sum (P : ℚ[X]) :
    tau P = ∑ n ∈ range (P.natDegree + 1), P.coeff n * tau (X ^ n) := by
  conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
  rw [tau_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [tau_C_mul]

/-- **ZC04, Tate algebra (polynomial form)**: `τ` has norm `≤ p` on `ℤ_(p)[x]`. -/
theorem VG_tau (hp5 : 5 ≤ p) {P : ℚ[X]} (hP : GV p P 0) : VG p (tau P) (-1) := by
  rw [tau_eq_sum]
  refine VG.sum _ fun n _ => ?_
  have := (hP n).mul (VG_tau_X_pow hp5 n)
  simpa using this

/-- **ZC04**: `τ` is `p`-integral on polynomials of degree `≤ p + 1` with `p`-integral coefficients. -/
theorem VG_tau_int (hp5 : 5 ≤ p) {P : ℚ[X]} (hP : GV p P 0) (hd : P.natDegree ≤ p + 1) :
    VG p (tau P) 0 := by
  rw [tau_eq_sum]
  refine VG.sum _ fun n hn => ?_
  have hn' : n ≤ p + 1 := by have := Finset.mem_range.mp hn; omega
  have := (hP n).mul (VG_tau_X_pow_int hp5 hn')
  simpa using this

/-! ### ZC05: the integrality (I3), finite form -/

lemma divByMonic_mul' {M₁ M₂ A : ℚ[X]} (h1 : M₁.Monic) (h2 : M₂.Monic) :
    A /ₘ (M₁ * M₂) = (A /ₘ M₁) /ₘ M₂ := by
  have hM : (M₁ * M₂).Monic := h1.mul h2
  have e1 := modByMonic_add_div A M₁
  have e2 := modByMonic_add_div (A /ₘ M₁) M₂
  have hd1 := degree_modByMonic_lt A h1
  have hd2 := degree_modByMonic_lt (A /ₘ M₁) h2
  refine (div_modByMonic_unique ((A /ₘ M₁) /ₘ M₂) (M₁ * ((A /ₘ M₁) %ₘ M₂) + A %ₘ M₁) hM
    ⟨by linear_combination e1 + M₁ * e2, ?_⟩).1
  calc degree (M₁ * ((A /ₘ M₁) %ₘ M₂) + A %ₘ M₁)
      ≤ max (degree (M₁ * ((A /ₘ M₁) %ₘ M₂))) (degree (A %ₘ M₁)) := degree_add_le _ _
    _ < degree (M₁ * M₂) := by
        refine max_lt ?_ ?_
        · rw [degree_mul, degree_mul]
          exact WithBot.add_lt_add_left (by simpa using h1.ne_zero) hd2
        · refine hd1.trans_le ?_
          rw [degree_mul]
          exact le_add_of_nonneg_right (zero_le_degree_iff.mpr h2.ne_zero)

lemma GV_divByMonic_piPl (Pl : Finset ℤ) : ∀ {A : ℚ[X]}, GV p A 0 → GV p (A /ₘ piPl Pl) 0 := by
  classical
  induction Pl using Finset.induction_on with
  | empty => intro A hA; simpa [piPl] using hA
  | insert a Pl ha ih =>
    intro A hA
    have hpi : piPl (insert a Pl) = (X - C (a : ℚ)) * piPl Pl := by
      unfold piPl; rw [Finset.prod_insert ha]
    rw [hpi, divByMonic_mul' (monic_X_sub_C _) (piPl_monic Pl)]
    exact ih (GV.divByMonic_X_sub_C hA (VG.intCast a))

/-- The polynomial part of a `p`-integral numerator over integer poles is `p`-integral. -/
theorem GV_polyPart {A : ℚ[X]} (hA : GV p A 0) (Pl : Finset ℤ) : GV p (polyPart A Pl) 0 :=
  GV_divByMonic_piPl Pl hA

lemma VG_H5_lt {m : ℕ} (hm : m < p) : VG p (H5 m) 0 := by
  unfold H5
  refine VG.sum _ fun v hv => ?_
  rw [Finset.mem_Icc] at hv
  rw [one_div]
  refine (VG.inv (r := 0) (pow_ne_zero _ (by exact_mod_cast (by omega : v ≠ 0))) ?_).mono (by norm_num)
  rw [show ((v : ℚ) ^ 5) = ((v ^ 5 : ℕ) : ℚ) by push_cast; ring, padicValRat.of_nat,
    padicValNat.pow (p := p) v 5, padicValNat.eq_zero_of_not_dvd
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
  simp

/-- Residues at poles of pairwise `p`-unit difference are `p`-integral. -/
theorem VG_resP_unit {A : ℚ[X]} (hA : GV p A 0) (Pl : Finset ℤ)
    (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s) {r : ℤ} (hr : r ∈ Pl) :
    VG p (resP A Pl r) 0 := by
  unfold resP
  rw [div_eq_mul_inv]
  have hv : VG p (A.eval (r : ℚ)) 0 := VG.eval hA (VG.intCast r)
  have hD := prod_erase_sub_ne_zero Pl r
  have hval : padicValRat p (∏ s ∈ Pl.erase r, ((r : ℚ) - s)) = 0 := by
    rw [padicValRat_finset_prod _ _ (fun s hs => by
      rw [Finset.mem_erase] at hs
      exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm))]
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [Finset.mem_erase] at hs
    have e : ((r : ℚ) - s) = ((r - s : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    exact padicValRat_int_eq_zero (hunit r hr s hs.2 (Ne.symm hs.1))
  have hinv := VG.inv (p := p) hD (r := 0) (by rw [hval]; simp)
  simpa using hv.mul hinv

/-! ### `tauX` is linear in the numerator -/

lemma resP_add (A B : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) :
    resP (A + B) Pl r = resP A Pl r + resP B Pl r := by
  unfold resP; rw [eval_add, add_div]

lemma resP_C_mul (c : ℚ) (A : ℚ[X]) (Pl : Finset ℤ) (r : ℤ) :
    resP (C c * A) Pl r = c * resP A Pl r := by
  unfold resP; rw [eval_mul, eval_C, mul_div_assoc]

lemma polyPart_add (A B : ℚ[X]) (Pl : Finset ℤ) :
    polyPart (A + B) Pl = polyPart A Pl + polyPart B Pl :=
  divByMonic_add' (piPl_monic Pl) A B

lemma polyPart_C_mul (c : ℚ) (A : ℚ[X]) (Pl : Finset ℤ) :
    polyPart (C c * A) Pl = C c * polyPart A Pl :=
  divByMonic_C_mul' (piPl_monic Pl) c A

lemma tauX_add (A B : ℚ[X]) (Pl : Finset ℤ) : tauX (A + B) Pl = tauX A Pl + tauX B Pl := by
  unfold tauX
  rw [polyPart_add, tau_add, C_add, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun r _ => by rw [resP_add, C_add]; ring

lemma tauX_C_mul (c : ℚ) (A : ℚ[X]) (Pl : Finset ℤ) : tauX (C c * A) Pl = C c * tauX A Pl := by
  unfold tauX
  rw [polyPart_C_mul, tau_C_mul, mul_add, Finset.mul_sum, C_mul]
  congr 1
  exact Finset.sum_congr rfl fun r _ => by rw [resP_C_mul, C_mul]; ring

lemma tauX_zero (Pl : Finset ℤ) : tauX 0 Pl = 0 := by
  have := tauX_C_mul 0 0 Pl
  simpa using this

lemma tauX_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (Pl : Finset ℤ) :
    tauX (∑ i ∈ s, f i) Pl = ∑ i ∈ s, tauX (f i) Pl := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tauX_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauX_add, ih]

/-! ### Integrality of `tauX` -/

lemma GV_tauX_aux {A : ℚ[X]} (hA : GV p A 0) (Pl : Finset ℤ)
    (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hdd : ∀ r ∈ Pl, dd r < p)
    {β : ℚ} (hτ : VG p (tau (polyPart A Pl)) β) (hβ : β ≤ 0) : GV p (tauX A Pl) β := by
  unfold tauX
  refine GV.add (GV.C hτ) (GV.sum _ fun r hr => ?_)
  have h1 : VG p (resP A Pl r) 0 := VG_resP_unit hA Pl hunit hr
  have h2 : GV p (C (H5 (dd r)) - X) 0 := GV.sub (GV.C (VG_H5_lt (hdd r hr))) GV.X
  exact (GV.C_mul h1 h2).mono (by simpa using hβ)

/-- `p`-integrality of `tauX` when the numerator has degree `≤ p + 1`. -/
theorem GV_tauX_int (hp5 : 5 ≤ p) {A : ℚ[X]} (hA : GV p A 0) (hdeg : A.natDegree ≤ p + 1)
    (Pl : Finset ℤ) (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s)
    (hdd : ∀ r ∈ Pl, dd r < p) : GV p (tauX A Pl) 0 := by
  refine GV_tauX_aux hA Pl hunit hdd (VG_tau_int hp5 (GV_polyPart hA Pl) ?_) le_rfl
  exact (natDegree_polyPart_le A Pl).trans ((Nat.sub_le _ _).trans hdeg)

/-- Without a degree restriction `tauX` loses at most one power of `p`. -/
theorem GV_tauX_loss (hp5 : 5 ≤ p) {A : ℚ[X]} (hA : GV p A 0)
    (Pl : Finset ℤ) (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s)
    (hdd : ∀ r ∈ Pl, dd r < p) : GV p (tauX A Pl) (-1) :=
  GV_tauX_aux hA Pl hunit hdd (VG_tau hp5 (GV_polyPart hA Pl)) (by norm_num)

/-- **ZC05, (I3), finite form.**  Let `Pl ⊆ ℤ` have pairwise `p`-unit differences and harmonic
indices `d(r) < p` (so `T = ∏_{r ∈ Pl}(x - r)`), let `U_j ∈ ℤ_(p)[x]` with `deg U_0 ≤ p + 1`, and
`Y ∈ ℤ_(p)[X]`.  Then `τ_Y(∑_{j<J} p^j U_j / T) ∈ ℤ_(p)[X]`. -/
theorem tauX_I3 (hp5 : 5 ≤ p) (Pl : Finset ℤ)
    (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hdd : ∀ r ∈ Pl, dd r < p)
    (J : ℕ) (U : ℕ → ℚ[X]) (hU : ∀ j < J, GV p (U j) 0) (hU0 : (U 0).natDegree ≤ p + 1)
    (Y : ℚ[X]) (hY : GV p Y 0) :
    GV p ((tauX (∑ j ∈ range J, C ((p : ℚ) ^ j) * U j) Pl).comp Y) 0 := by
  rw [tauX_sum]
  have hterm : ∀ j ∈ range J, GV p (tauX (C ((p : ℚ) ^ j) * U j) Pl) 0 := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [tauX_C_mul]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using GV_tauX_int hp5 (hU 0 hj') hU0 Pl hunit hdd
    · have h1 : GV p (tauX (U j) Pl) (-1) := GV_tauX_loss hp5 (hU j hj') Pl hunit hdd
      have h2 : VG p ((p : ℚ) ^ j) j := by
        have := VG.primePow (p := p) (j : ℤ)
        simpa using this
      have := GV.C_mul h2 h1
      refine this.mono ?_
      have : (1 : ℚ) ≤ j := by exact_mod_cast hjpos
      linarith
  exact GV.comp (GV.sum _ hterm) hY

end Apery
