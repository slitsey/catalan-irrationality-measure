module

public import CatalanCore.Zeta5.Padic.Red

@[expose] public section

/-!
# ZC06(b), part 2: the distribution identity and the leading term of `τ` on the polynomial part

* `tau_dist`: `τ(P) = q^{-4} ∑_{c < q} τ(P(c + q x))` for every polynomial `P` and `q ≥ 1`
  (`τ - Φ` is invariant under `P ↦ P(x+1)` by `tau_shift`, and kills every `bin k`).
* `VG_coeff_bin_comp`: for `c < p` and `k < p²` the coefficients of `bin_k(c + p x)` are
  `p`-integral, and those of degree `≥ p + 1` lie in `p² ℤ_(p)`.
* `GV_local_poly`: hence for `Q` with `v_p(Q(m)) ≥ β` (`m ∈ ℕ`) and `deg Q < p²`, the local
  polynomial `R_c = p^{-β} Q(c + p x)` is in `ℤ_(p)[x]` with high coefficients in `p² ℤ_(p)`.
* `tau_lead_poly`: `p^{4-β} τ(Q)` is `p`-integral and reduces to `∑_{c < p} polySym (R_c mod p)`.
-/

open Finset Polynomial

namespace Apery

/-! ### The distribution identity -/

lemma iterate_derivative_comp_C_mul_X (S : ℚ[X]) (a : ℚ) (k : ℕ) :
    derivative^[k] (S.comp (C a * X)) = C (a ^ k) * (derivative^[k] S).comp (C a * X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', derivative_mul,
      derivative_C, zero_mul, zero_add, derivative_comp, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one, pow_succ, C_mul]
    ring

/-- `Φ_q(P) = q^{-4} ∑_{c < q} τ(P(c + q x))`. -/
noncomputable def tauPhi (q : ℕ) (P : ℚ[X]) : ℚ :=
  ((q : ℚ) ^ 4)⁻¹ * ∑ c ∈ range q, tau (P.comp (C (c : ℚ) + C (q : ℚ) * X))

lemma tauPhi_add (q : ℕ) (P Q : ℚ[X]) : tauPhi q (P + Q) = tauPhi q P + tauPhi q Q := by
  unfold tauPhi
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [add_comp, tau_add]

lemma tauPhi_C_mul (q : ℕ) (e : ℚ) (P : ℚ[X]) : tauPhi q (C e * P) = e * tauPhi q P := by
  unfold tauPhi
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comp, C_comp, tau_C_mul]; ring

lemma tauPhi_sum (q : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    tauPhi q (∑ i ∈ s, f i) = ∑ i ∈ s, tauPhi q (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tauPhi, tau, Lb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tauPhi_add, ih]

lemma tauPhi_shift (q : ℕ) (hq : 0 < q) (S : ℚ[X]) :
    tauPhi q (S.comp (X + 1)) - tauPhi q S = tau (S.comp (X + 1)) - tau S := by
  rw [tau_shift]
  unfold tauPhi
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hstep : ∀ c ∈ range q, tau ((S.comp (X + 1)).comp (C (c : ℚ) + C (q : ℚ) * X)) -
      tau (S.comp (C (c : ℚ) + C (q : ℚ) * X)) =
      tau (S.comp (C ((c + 1 : ℕ) : ℚ) + C (q : ℚ) * X)) -
        tau (S.comp (C (c : ℚ) + C (q : ℚ) * X)) := by
    intro c _
    rw [comp_assoc]
    congr 3
    simp only [add_comp, X_comp, one_comp]
    push_cast; rw [C_add, C_1]; ring
  rw [Finset.sum_congr rfl hstep,
    Finset.sum_range_sub (fun c => tau (S.comp (C (c : ℚ) + C (q : ℚ) * X))) q]
  set R := S.comp (C (q : ℚ) * X) with hR
  have h1 : S.comp (C ((q : ℕ) : ℚ) + C (q : ℚ) * X) = R.comp (X + 1) := by
    rw [hR, comp_assoc]; congr 1; simp only [mul_comp, C_comp, X_comp]; ring
  have h0 : S.comp (C (((0 : ℕ) : ℚ)) + C (q : ℚ) * X) = R := by
    rw [hR]; congr 1; simp
  beta_reduce
  rw [h1, h0, tau_shift, hR, iterate_derivative_comp_C_mul_X, eval_mul, eval_C, eval_comp]
  simp only [eval_mul, eval_C, eval_X, mul_zero]
  have hq0 : (q : ℚ) ^ 4 ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  field_simp

/-- **The distribution identity** `τ(P) = q^{-4} ∑_{c < q} τ(P(c + q x))`. -/
theorem tau_dist (q : ℕ) (hq : 0 < q) (P : ℚ[X]) : tau P = tauPhi q P := by
  have hbin : ∀ k, tau (bin k) = tauPhi q (bin k) := by
    intro k
    have h1 := tauPhi_shift q hq (bin (k + 1))
    rw [bin_comp_add_one, tau_add, tauPhi_add] at h1
    linarith
  rw [newton P le_rfl, tau_sum, tauPhi_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [tau_C_mul, tauPhi_C_mul, hbin]

/-! ### Coefficients of `bin_k(c + p x)` -/

section taylor
variable {p : ℕ} [hp : Fact p.Prime]

lemma coeff_mul_lin (N : ℚ[X]) (u v : ℚ) (j : ℕ) :
    (N * (C u + C v * X)).coeff j = u * N.coeff j + (if j = 0 then 0 else v * N.coeff (j - 1)) := by
  rw [mul_add, coeff_add, coeff_mul_C, show N * (C v * X) = C v * (N * X) by ring, coeff_C_mul]
  rcases j with _ | j
  · simp [mul_comm]
  · rw [coeff_mul_X]; simp; ring

/-- The coefficients of `(c + p x)(c - 1 + p x) ⋯ (c - k + 1 + p x)`. -/
lemma VG_coeff_desc_comp (c : ℕ) (hc : c < p) (k : ℕ) (j : ℕ) :
    VG p (((descPochhammer ℚ k).comp (C (c : ℚ) + C (p : ℚ) * X)).coeff j)
      (max (((k + (p - 1 - c)) / p : ℕ) : ℚ) (j : ℚ)) := by
  induction k generalizing j with
  | zero =>
    have h0 : (p - 1 - c) / p = 0 := Nat.div_eq_of_lt (by omega)
    simp only [descPochhammer_zero, one_comp, coeff_one, zero_add, h0]
    split_ifs with h
    · subst h; simpa using VG.one (p := p)
    · exact VG.zero _
  | succ k ih =>
    rw [descPochhammer_succ_right, mul_comp]
    have hlin : (X - ((k : ℕ) : ℚ[X])).comp (C (c : ℚ) + C (p : ℚ) * X) =
        C ((c : ℚ) - k) + C (p : ℚ) * X := by
      simp only [sub_comp, X_comp, natCast_comp]
      rw [show ((k : ℕ) : ℚ[X]) = C (k : ℚ) from (map_natCast C k).symm, C_sub]; ring
    rw [hlin, coeff_mul_lin]
    set A := (k + (p - 1 - c)) / p with hA
    have hsucc := Nat.succ_div (a := k + (p - 1 - c)) (b := p)
    rw [show k + (p - 1 - c) + 1 = k + 1 + (p - 1 - c) by omega] at hsucc
    have hpv : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
    by_cases hdvd : p ∣ k + 1 + (p - 1 - c)
    · rw [if_pos hdvd] at hsucc
      rw [hsucc]
      have hu : VG p ((c : ℚ) - k) 1 := by
        have : (p : ℤ) ∣ (c : ℤ) - k := by
          have h1 : (p : ℤ) ∣ ((k + 1 + (p - 1 - c) : ℕ) : ℤ) := by exact_mod_cast hdvd
          have h2 : ((k + 1 + (p - 1 - c) : ℕ) : ℤ) = (k : ℤ) - c + p := by
            push_cast [show c ≤ p - 1 by omega, show 1 ≤ p by omega]; ring
          rw [h2] at h1
          have h3 : (p : ℤ) ∣ (k : ℤ) - c := by
            have := dvd_sub h1 (dvd_refl (p : ℤ)); simpa using this
          have := dvd_neg.mpr h3; simpa using this
        have := VG_int_one this; simpa using this
      refine VG.add ((hu.mul (ih j)).mono ?_) ?_
      · push_cast; rw [max_le_iff]; constructor <;> [linarith [le_max_left (A : ℚ) (j : ℚ)];
          linarith [le_max_right (A : ℚ) (j : ℚ)]]
      · split_ifs with hj
        · exact VG.zero _
        · refine (hpv.mul (ih (j - 1))).mono ?_
          have : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by push_cast [Nat.one_le_iff_ne_zero.mpr hj]; ring
          rw [this]; push_cast; rw [max_le_iff]; constructor
          · linarith [le_max_left (A : ℚ) ((j : ℚ) - 1)]
          · linarith [le_max_right (A : ℚ) ((j : ℚ) - 1)]
    · rw [if_neg hdvd, add_zero] at hsucc
      rw [hsucc]
      have hu : VG p ((c : ℚ) - k) 0 := by
        have := VG.intCast (p := p) ((c : ℤ) - k); simpa using this
      refine VG.add ((hu.mul (ih j)).mono (by simp [hA])) ?_
      split_ifs with hj
      · exact VG.zero _
      · refine (hpv.mul (ih (j - 1))).mono ?_
        have : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by push_cast [Nat.one_le_iff_ne_zero.mpr hj]; ring
        rw [this, max_le_iff]; constructor
        · linarith [le_max_left (A : ℚ) ((j : ℚ) - 1)]
        · linarith [le_max_right (A : ℚ) ((j : ℚ) - 1)]

lemma padicValNat_factorial_lt_sq_div {k : ℕ} (hk : k < p ^ 2) : padicValNat p k.factorial = k / p := by
  rw [padicValNat_factorial (b := 2)]
  · simp
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp
    · exact Nat.log_lt_of_lt_pow h0.ne' hk

/-- **Coefficients of `bin_k(c + p x)`**, `c < p`, `k < p²`: integral, and in `p² ℤ_(p)` from
degree `p + 1` on. -/
theorem VG_coeff_bin_comp (c : ℕ) (hc : c < p) {k : ℕ} (hk : k < p ^ 2) (j : ℕ) :
    VG p (((bin k).comp (C (c : ℚ) + C (p : ℚ) * X)).coeff j) (if p + 1 ≤ j then 2 else 0) := by
  rw [bin, mul_comp, C_comp, coeff_C_mul]
  have hfac : VG p ((k.factorial : ℚ)⁻¹) (-((k / p : ℕ) : ℚ)) := by
    refine VG.inv (by exact_mod_cast (Nat.factorial_pos k).ne') ?_
    rw [padicValRat.of_nat, padicValNat_factorial_lt_sq_div hk, Int.cast_natCast]
  have := hfac.mul (VG_coeff_desc_comp c hc k j)
  refine this.mono ?_
  have hA : k / p ≤ (k + (p - 1 - c)) / p := Nat.div_le_div_right (by omega)
  have hA' : ((k / p : ℕ) : ℚ) ≤ (((k + (p - 1 - c)) / p : ℕ) : ℚ) := by exact_mod_cast hA
  have hkp : k / p ≤ p - 1 := by
    have : k / p < p := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos]; nlinarith
    omega
  have hkp' : ((k / p : ℕ) : ℚ) ≤ (p : ℚ) - 1 := by
    have : ((k / p : ℕ) : ℚ) ≤ ((p - 1 : ℕ) : ℚ) := by exact_mod_cast hkp
    rw [Nat.cast_sub hp.out.one_lt.le] at this; simpa using this
  split_ifs with hj
  · have hj' : ((p : ℚ) + 1) ≤ j := by exact_mod_cast hj
    linarith [le_max_right ((((k + (p - 1 - c)) / p : ℕ) : ℚ)) (j : ℚ)]
  · linarith [le_max_left ((((k + (p - 1 - c)) / p : ℕ) : ℚ)) (j : ℚ)]

/-- The local substitution `x = c + p X`. -/
noncomputable def Gc (p c : ℕ) : ℚ[X] := C (c : ℚ) + C (p : ℚ) * X

/-- **Local polynomials.**  If `v_p(Q(m)) ≥ β` for `m ∈ ℕ` and `deg Q < p²`, then
`R_c = p^{-β} Q(c + p X)` has `p`-integral coefficients, in `p² ℤ_(p)` from degree `p + 1` on. -/
theorem GV_local_poly {Q : ℚ[X]} (hdeg : Q.natDegree < p ^ 2) {β : ℤ}
    (hv : ∀ m : ℕ, VG p (Q.eval (m : ℚ)) β) (c : ℕ) (hc : c < p) (j : ℕ) :
    VG p ((C ((p : ℚ) ^ (-β)) * Q.comp (Gc p c)).coeff j) (if p + 1 ≤ j then 2 else 0) := by
  obtain ⟨e, he, hev⟩ := binRep_of_values (p := p) (le_refl Q.natDegree) (β := (β : ℚ))
    (fun m _ => hv m)
  rw [he, Polynomial.sum_comp, Finset.mul_sum, finsetSum_coeff]
  refine VG.sum _ fun k hk => ?_
  have hk' : k ≤ Q.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_comp, C_comp, ← mul_assoc, ← C_mul, coeff_C_mul]
  have h1 : VG p ((p : ℚ) ^ (-β) * e k) 0 := by
    have := (VG.primePow (p := p) (-β)).mul (hev k hk')
    refine this.mono (le_of_eq ?_); push_cast; ring
  have := h1.mul (VG_coeff_bin_comp c hc (lt_of_le_of_lt hk' hdeg) j)
  simpa [Gc] using this

/-- **The polynomial part of the leading term.**  Under the hypotheses of `GV_local_poly`, if the
local polynomials reduce to `W c`, then `p^{4-β} τ(Q)` is `p`-integral and reduces to
`∑_{c < p} polySym (W c)`. -/
theorem tau_lead_poly (hp5 : 5 ≤ p) {Q : ℚ[X]} (hdeg : Q.natDegree < p ^ 2) {β : ℤ}
    (hv : ∀ m : ℕ, VG p (Q.eval (m : ℚ)) β) (W : ℕ → (ZMod p)[X])
    (hW : ∀ c < p, redP p (C ((p : ℚ) ^ (-β)) * Q.comp (Gc p c)) = W c) :
    VG p ((p : ℚ) ^ (4 - β) * tau Q) 0 ∧
      (((p : ℚ) ^ (4 - β) * tau Q : ℚ) : ZMod p) = ∑ c ∈ range p, polySym p (W c) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set R : ℕ → ℚ[X] := fun c => C ((p : ℚ) ^ (-β)) * Q.comp (Gc p c) with hR
  have hRi : ∀ c < p, GV p (R c) 0 := fun c hc j =>
    (GV_local_poly hdeg hv c hc j).mono (by split_ifs <;> norm_num)
  -- `p^{4-β} τ(Q) = ∑_c τ(R_c)`
  have hsum : (p : ℚ) ^ (4 - β) * tau Q = ∑ c ∈ range p, tau (R c) := by
    rw [tau_dist p hp.out.pos Q, tauPhi, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hR]; simp only
    rw [tau_C_mul, Gc]
    have : (p : ℚ) ^ (4 - β) * ((p : ℚ) ^ 4)⁻¹ = (p : ℚ) ^ (-β) := by
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp0]; congr 1; push_cast; ring
    rw [← mul_assoc, this]
  -- each `τ(R_c)`
  have hterm : ∀ c < p, VG p (tau (R c)) 0 ∧ ((tau (R c) : ℚ) : ZMod p) = polySym p (W c) := by
    intro c hc
    set T : ℚ[X] := ∑ j ∈ range (p + 1), C ((R c).coeff j) * X ^ j with hT
    set H : ℚ[X] := R c - T with hH
    have hTc : ∀ j, T.coeff j = if j < p + 1 then (R c).coeff j else 0 := by
      intro j
      rw [hT, finsetSum_coeff]
      simp only [coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_range]
    have hTi : GV p T 0 := fun j => by
      rw [hTc]; split_ifs
      · exact hRi c hc j
      · exact VG.zero _
    have hTd : T.natDegree ≤ p := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      have hj' : p < j := by exact_mod_cast hj
      rw [hTc, if_neg (by omega)]
    have hH2 : GV p H 2 := fun j => by
      rw [hH, coeff_sub, hTc]
      split_ifs with hj
      · rw [sub_self]; exact VG.zero _
      · have := GV_local_poly hdeg hv c hc j
        rw [if_pos (by omega)] at this
        rw [sub_zero]; exact this
    have hHτ : VG p (tau H) 1 := by
      have h1 : GV p (C ((p : ℚ) ^ (-2 : ℤ)) * H) 0 := by
        have := GV.C_mul (VG.primePow (p := p) (-2)) hH2
        refine this.mono (le_of_eq ?_); push_cast; ring
      have h2 := VG_tau hp5 h1
      rw [tau_C_mul] at h2
      have h3 := (VG.primePow (p := p) 2).mul h2
      have e : (p : ℚ) ^ (2 : ℤ) * ((p : ℚ) ^ (-2 : ℤ) * tau H) = tau H := by
        rw [← mul_assoc, ← zpow_add₀ hp0]; simp
      rw [e] at h3
      refine h3.mono ?_; push_cast; norm_num
    have hTτ : VG p (tau T) 0 := VG_tau_int hp5 hTi (hTd.trans (Nat.le_succ p))
    have hRTH : R c = T + H := by rw [hH]; ring
    have hredT : redP p T = W c := by
      rw [← hW c hc]
      refine redP_congr hTi (hRi c hc) ?_
      have e : T - R c = -H := by rw [hH]; ring
      rw [e]; exact hH2.neg.mono (by norm_num)
    refine ⟨?_, ?_⟩
    · rw [hRTH, tau_add]; exact hTτ.add (hHτ.mono (by norm_num))
    · rw [hRTH, tau_add, red_add hTτ (hHτ.mono (by norm_num)), red_zero_of_VG_one hHτ, add_zero,
        polySym_red hp5 hTi hTd, hredT]
  rw [hsum]
  refine ⟨VG.sum _ fun c hc => (hterm c (Finset.mem_range.mp hc)).1, ?_⟩
  rw [red_sum _ _ fun c hc => (hterm c (Finset.mem_range.mp hc)).1]
  exact Finset.sum_congr rfl fun c hc => (hterm c (Finset.mem_range.mp hc)).2

end taylor

end Apery
