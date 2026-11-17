module

public import CatalanCore.Lai.ContentL2Jet
public import CatalanCore.Lai.ClassCount
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

open Finset Polynomial CatalanCore.Basic CatalanCore.Content

namespace CatalanCore.Lai

noncomputable section

variable {n p : ℕ} [hp : Fact p.Prime]

/-! ### Definitions -/

/-- Lift of a residue mod `p²` to `MPT` (through `ZMod.val`). -/
def lz (p : ℕ) (x : ZMod (p ^ 2)) : MPT := MvPolynomial.C ((x.val : ℤ) : ℚ)

/-- `σ_W(s) = ∑_{r ∈ W, r ≠ s} 1/(r - s)` in `ℤ/p²`. -/
def sigW (p : ℕ) (W : Finset ℕ) (s : ℕ) : ZMod (p ^ 2) :=
  ∑ r ∈ W.erase s, (((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))))⁻¹

/-- `A_{μ-1}` (zero for `μ = 0`). -/
def Aprev (A : MPT[X]) (μ : ℕ) : MPT := if μ = 0 then 0 else A.coeff (μ - 1)

/-- `E(x) = ∏_{r ∉ W} (r - x)^{2 μ'_r}` over `ℤ/p²`. -/
def Epoly (n p σW : ℕ) : (ZMod (p ^ 2))[X] :=
  ∏ r ∈ range p, (Polynomial.C (r : ZMod (p ^ 2)) - Polynomial.X) ^
    (if sig n p r = σW then 0 else gexp n p σW r)

/-- Reduction of an integer polynomial to `ℤ/p²`, composed with `x ↦ -x`: `V(-x)`. -/
def Vneg (p : ℕ) (V : ℤ[X]) : (ZMod (p ^ 2))[X] :=
  (V.map (Int.castRingHom (ZMod (p ^ 2)))).comp (-Polynomial.X)

/-! ### Row L2S-12 -/

/-- L2S-12. -/
theorem harm_refl (h3 : 3 ≤ p) {m : ℕ} (hm : m < p) : harm p (p - 1 - m) = harm p m :=
  CatalanCore.Arith.Hybrid.LemmaE.H_refl p h3 (by omega)

/-! ### Helpers: windows, flags, reduction mod `p` -/

section Helpers

/-- The window `{s < p : σ(s) = σ_W}` is an interval. -/
lemma window_Icc (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (hne : Wf.Nonempty) : ∃ w0 w1, Wf = Icc w0 w1 ∧ w1 < p := by
  refine ⟨Wf.min' hne, Wf.max' hne, ?_, ((hWf _).1 (Wf.max'_mem hne)).1⟩
  ext s
  simp only [Finset.mem_Icc]
  constructor
  · intro hs; exact ⟨Wf.min'_le _ hs, Wf.le_max' _ hs⟩
  · rintro ⟨h1, h2⟩
    have hmin := (hWf _).1 (Wf.min'_mem hne)
    have hmax := (hWf _).1 (Wf.max'_mem hne)
    refine (hWf s).2 ⟨by omega, ?_⟩
    have a := sig_mono n p h1
    have b := sig_mono n p h2
    omega

lemma bflag_le (n p s : ℕ) : bflag n p s = 0 ∨ bflag n p s = 1 := by
  unfold bflag; split_ifs <;> simp

lemma eflag_le (n p s : ℕ) : eflag n p s = 0 ∨ eflag n p s = 1 := by
  unfold eflag; split_ifs <;> simp

lemma flags_of_sig (n p s s' : ℕ) (hs : sig n p s = sig n p s') :
    bflag n p s = bflag n p s' ∧ eflag n p s = eflag n p s' := by
  have h1 := sig_eq_flags n p s
  have h2 := sig_eq_flags n p s'
  constructor <;>
  rcases bflag_le n p s with a | a <;> rcases bflag_le n p s' with b | b <;>
    rcases eflag_le n p s with c | c <;> rcases eflag_le n p s' with d | d <;> omega

end Helpers

section Reduce

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma rho_inv {x : ZMod (p ^ 2)} (hx : IsUnit x) : ρ x⁻¹ = (ρ x)⁻¹ := by
  have h := ZMod.mul_inv_of_unit x hx
  have h2 := congrArg ρ h
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_right h2

/-- `p z = 0` in `ℤ/p²` as soon as `z` reduces to `0` mod `p`. -/
lemma pmul_eq_zero {z : ZMod (p ^ 2)} (hz : ρ z = 0) : (p : ZMod (p ^ 2)) * z = 0 := by
  have h1 : ρ z = ((z.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  rw [h1, ZMod.natCast_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  rw [← ZMod.natCast_zmod_val z, hk]
  push_cast
  have := pp_sq (p := p)
  linear_combination (k : ZMod (p ^ 2)) * this

lemma rho_sigW (W : Finset ℕ) (hW : ∀ r ∈ W, r < p) (s : ℕ) (hs : s < p) :
    ρ (sigW p W s) = ∑ r ∈ W.erase s, (((r : ℕ) : ZMod p) - (s : ZMod p))⁻¹ := by
  unfold sigW
  rw [map_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_erase.1 hr
  rw [rho_inv (isUnit_sub_cast r s (hW r hr'.2) hs hr'.1.symm), map_sub, map_natCast, map_natCast]

lemma sigW_harm {w0 w1 s : ℕ} (hs : s ∈ Icc w0 w1) :
    ∑ r ∈ (Icc w0 w1).erase s, (((r : ℕ) : ZMod p) - (s : ZMod p))⁻¹ =
      harm p (w1 - s) - harm p (s - w0) := by
  have hs' := Finset.mem_Icc.1 hs
  have e : (Icc w0 w1).erase s = Ico w0 s ∪ Ioc s w1 := by
    ext r; simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ico,
      Finset.mem_Ioc]; omega
  have dis : Disjoint (Ico w0 s) (Ioc s w1) := by
    rw [Finset.disjoint_left]; intro r h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2; omega
  rw [e, Finset.sum_union dis]
  have h1 : ∑ r ∈ Ioc s w1, (((r : ℕ) : ZMod p) - (s : ZMod p))⁻¹ = harm p (w1 - s) := by
    have e : Ioc s w1 = Ico (s + 1) (w1 + 1) := by ext r; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega
    rw [e, Finset.sum_Ico_eq_sum_range]
    unfold harm CatalanCore.Arith.Hybrid.LemmaE.Gs
    have : w1 + 1 - (s + 1) = w1 - s := by omega
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast; ring
  have h2 : ∑ r ∈ Ico w0 s, (((r : ℕ) : ZMod p) - (s : ZMod p))⁻¹ = -harm p (s - w0) := by
    rw [Finset.sum_Ico_eq_sum_range]
    rw [← Finset.sum_range_reflect]
    unfold harm CatalanCore.Arith.Hybrid.LemmaE.Gs
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.1 hj
    have e1 : w0 + (s - w0 - 1 - j) + (j + 1) = s := by omega
    have : (((w0 + (s - w0 - 1 - j) : ℕ) : ZMod p)) - (s : ZMod p) = -(((j + 1 : ℕ) : ZMod p)) := by
      have := congrArg (fun z : ℕ => (z : ZMod p)) e1
      simp only [Nat.cast_add] at this ⊢
      linear_combination this
    rw [this, inv_neg]
  rw [h1, h2]; ring

/-- The weighted harmonic word of a window sums to its total weight times `∫G`. -/
lemma word_sum {G : (ZMod p)[X]} (hGd : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (W : Finset ℕ)
    (hne : W.Nonempty) (hW : ∀ s ∈ W, s < p)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : ZMod p) = 0)
    (hG' : ∀ m, m < p → m ∉ W → (Polynomial.derivative G).eval ((m : ℕ) : ZMod p) = 0)
    (r6 r2 b ε : ℕ) (hr6 : r6 < p) (hr2 : r2 < p)
    (hb : ∀ s ∈ W, (b = 0 ∧ s ≤ r6) ∨ (b = 1 ∧ r6 < s))
    (he : ∀ s ∈ W, (ε = 0 ∧ s + r2 < p) ∨ (ε = 1 ∧ p ≤ s + r2)) (A B C : ZMod p) :
    ∑ s ∈ W, G.eval ((s : ℕ) : ZMod p) *
        (A * harm p s + B * harm p (r6 + b * p - s) + C * harm p (r2 + s - ε * p)) =
      (A + B + C) * harmSum p G := by
  have hcast : ZMod.castHom (dvd_refl p) (ZMod p) = RingHom.id (ZMod p) := ZMod.castHom_self
  obtain ⟨s0, hs0⟩ := hne
  have T1 : ∑ s ∈ W, G.eval ((s : ℕ) : ZMod p) * harm p s = harmSum p G := by
    have := harmSum_window G hGd h5 W 0 (by omega) (fun s hs => by have := hW s hs; omega) hG hG'
    simpa [hcast] using this
  have T2 : ∑ s ∈ W, G.eval ((s : ℕ) : ZMod p) * harm p (r6 + b * p - s) = harmSum p G := by
    rcases hb s0 hs0 with ⟨hb0, _⟩ | ⟨hb1, hlt⟩
    · have := harmSum_window_refl G hGd h5 W r6 hr6
        (fun s hs => by rcases hb s hs with ⟨_, h⟩ | ⟨h, _⟩ <;> omega) hG hG'
      rw [← this]
      refine Finset.sum_congr rfl fun s hs => ?_
      rcases hb s hs with ⟨h0, _⟩ | ⟨h1, _⟩
      · subst hb0; simp [hcast]
      · omega
    · have := harmSum_window_neg G hGd h5 W (r6 + 1) (by have := hW s0 hs0; omega)
        (fun s hs => by have := hW s hs; rcases hb s hs with ⟨h, _⟩ | ⟨_, h⟩ <;> omega) hG hG'
      rw [← this]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' := hW s hs
      rcases hb s hs with ⟨h0, _⟩ | ⟨h1, hl⟩
      · omega
      · subst hb1
        have e := harm_refl (p := p) (by omega) (m := r6 + 1 * p - s) (by omega)
        have e2 : p - 1 - (r6 + 1 * p - s) = s - (r6 + 1) := by omega
        rw [e2] at e
        simp [hcast, e]
  have T3 : ∑ s ∈ W, G.eval ((s : ℕ) : ZMod p) * harm p (r2 + s - ε * p) = harmSum p G := by
    rcases he s0 hs0 with ⟨he0, _⟩ | ⟨he1, hlt⟩
    · have := harmSum_window G hGd h5 W r2 hr2
        (fun s hs => by rcases he s hs with ⟨_, h⟩ | ⟨h, _⟩ <;> omega) hG hG'
      rw [← this]
      refine Finset.sum_congr rfl fun s hs => ?_
      rcases he s hs with ⟨h0, _⟩ | ⟨h1, _⟩
      · subst he0; simp [hcast, add_comm]
      · omega
    · have hr2p : p - r2 < p := by have := hW s0 hs0; omega
      have := harmSum_window_neg G hGd h5 W (p - r2) hr2p
        (fun s hs => by have := hW s hs; rcases he s hs with ⟨h, _⟩ | ⟨_, h⟩ <;> omega) hG hG'
      rw [← this]
      refine Finset.sum_congr rfl fun s hs => ?_
      have hs' := hW s hs
      rcases he s hs with ⟨h0, _⟩ | ⟨h1, hl⟩
      · omega
      · subst he1
        simp only [hcast, RingHom.id_apply]
        congr 2
        omega
  have e : ∀ s ∈ W, G.eval ((s : ℕ) : ZMod p) *
        (A * harm p s + B * harm p (r6 + b * p - s) + C * harm p (r2 + s - ε * p)) =
      A * (G.eval ((s : ℕ) : ZMod p) * harm p s) +
        B * (G.eval ((s : ℕ) : ZMod p) * harm p (r6 + b * p - s)) +
        C * (G.eval ((s : ℕ) : ZMod p) * harm p (r2 + s - ε * p)) := fun s _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, T1, T2, T3]
  ring

lemma bflag_cases (n p s : ℕ) :
    (bflag n p s = 0 ∧ s ≤ r6 n p) ∨ (bflag n p s = 1 ∧ r6 n p < s) := by
  unfold bflag; split_ifs with h <;> [right; left] <;> omega

lemma eflag_cases (n p s : ℕ) (hr2 : r2 n p < p) (hs : s < p) :
    (eflag n p s = 0 ∧ s + r2 n p < p) ∨ (eflag n p s = 1 ∧ p ≤ s + r2 n p) := by
  unfold eflag; split_ifs with h <;> [right; left] <;> omega

lemma rho_XiE0 (h : Rng n p) {s : ℕ} (hs : s < p) :
    ρ (xiR n p s + e0Z n p s) =
      (((lam n p : ℤ) : ZMod p) - 1) * harm p s +
        (-2 * (q6 n p : ZMod p)) * harm p (r6 n p + bflag n p s * p - s) +
        (3 * (1 + (q2 n p : ZMod p))) * harm p (r2 n p + s - eflag n p s * p) := by
  have hr6 := r6_lt n p hp.out.pos
  have hr2 := r2_lt n p hp.out.pos
  have hq6 := h.q6_ge
  have hz : ∀ m, m < p → ρ (Hz p m) = harm p m := fun m hm => Hz_cast m hm
  unfold xiR e0Z
  simp only [map_add, map_sub, map_mul, map_intCast, map_natCast, map_ofNat, map_one, map_neg]
  have hq1 : ((q6 n p - 1 : ℕ) : ZMod p) = (q6 n p : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rcases bflag_cases n p s with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
  rcases eflag_cases n p s hr2 hs with ⟨he, he'⟩ | ⟨he, he'⟩ <;> rw [hb, he] <;>
  simp only [Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero, Nat.sub_zero, zero_add,
    sub_zero, mul_zero, sub_self, Nat.cast_add, hq1, mul_one, one_mul]
  · rw [hz s hs, hz (r6 n p - s) (by omega), hz (r2 n p + s) (by omega)]
    push_cast; ring
  · rw [hz s hs, hz (r6 n p - s) (by omega), hz (r2 n p + s - p) (by omega)]
    push_cast; ring
  · rw [hz s hs, hz (r6 n p + p - s) (by omega), hz (r2 n p + s) (by omega)]
    push_cast; ring
  · rw [hz s hs, hz (r6 n p + p - s) (by omega), hz (r2 n p + s - p) (by omega)]
    push_cast; ring

lemma rho_lam0 (h : Rng n p) {s : ℕ} (hs : s < p) :
    ρ (lam0Z n p s) = (-5) * harm p s + 2 * harm p (r6 n p + bflag n p s * p - s) +
        3 * harm p (r2 n p + s - eflag n p s * p) := by
  have hr6 := r6_lt n p hp.out.pos
  have hr2 := r2_lt n p hp.out.pos
  have hz : ∀ m, m < p → ρ (Hz p m) = harm p m := fun m hm => Hz_cast m hm
  unfold lam0Z
  simp only [map_add, map_sub, map_mul, map_natCast, map_ofNat, map_one, map_neg]
  rcases bflag_cases n p s with ⟨hb, hb'⟩ | ⟨hb, hb'⟩ <;>
  rcases eflag_cases n p s hr2 hs with ⟨he, he'⟩ | ⟨he, he'⟩ <;> rw [hb, he] <;>
  simp only [zero_mul, one_mul, add_zero, Nat.sub_zero]
  · rw [hz s hs, hz (r6 n p - s) (by omega), hz (r2 n p + s) (by omega)]; ring
  · rw [hz s hs, hz (r6 n p - s) (by omega), hz (r2 n p + s - p) (by omega)]; ring
  · rw [hz s hs, hz (r6 n p + p - s) (by omega), hz (r2 n p + s) (by omega)]; ring
  · rw [hz s hs, hz (r6 n p + p - s) (by omega), hz (r2 n p + s - p) (by omega)]; ring

end Reduce


/-! ### Integer lifts and congruence bookkeeping -/

section Lifts

lemma GV_intdvd (e : ℕ) {z : ℤ} (h : (p : ℤ) ^ e ∣ z) :
    GV p (e : ℤ) (MvPolynomial.C (z : ℚ) : MPT) := by
  obtain ⟨k, hk⟩ := h
  apply GV.const
  rw [hk]
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have : (p : ℚ) ^ (-(e : ℤ)) * (((p : ℤ) ^ e * k : ℤ) : ℚ) = (k : ℚ) := by
    push_cast
    rw [zpow_neg, zpow_natCast]
    field_simp
  rw [this]; exact int_mem_locRing k

lemma GV_zphi2 {z : ℤ} (h : (z : ZMod (p ^ 2)) = 0) : GV p 2 (zphi z) := by
  rw [zphi_apply]
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd z (p ^ 2)).1 h
  have := GV_intdvd (p := p) 2 (z := z) (by simpa using h')
  simpa using this

lemma GV_zphi1 {z : ℤ} (h : (z : ZMod p) = 0) : GV p 1 (zphi z) := by
  rw [zphi_apply]
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 h
  have := GV_intdvd (p := p) 1 (z := z) (by simpa using h')
  simpa using this

lemma GV0_zphi (z : ℤ) : GV p 0 (zphi z) := by
  rw [zphi_apply]; exact GV.const_int z

lemma GV0_lz (x : ZMod (p ^ 2)) : GV p 0 (lz p x) := by
  unfold lz; exact GV.const_int _

lemma lz_eq (x : ZMod (p ^ 2)) : lz p x = zphi (x.val : ℤ) := by
  unfold lz; rw [zphi_apply]

/-- If `z` lifts `x` modulo `p²`, then `zphi z ≡ lz x` modulo `p²`. -/
lemma GV_lz_sub2 (x : ZMod (p ^ 2)) {z : ℤ} (h : (z : ZMod (p ^ 2)) = x) :
    GV p 2 (zphi z - lz p x) := by
  rw [lz_eq, ← map_sub]
  apply GV_zphi2
  push_cast
  rw [ZMod.natCast_zmod_val, h, sub_self]

/-- Same modulo `p`, from agreement of the reductions. -/
lemma GV_lz_sub1 (x : ZMod (p ^ 2)) {z : ℤ}
    (h : (z : ZMod p) = ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) x) :
    GV p 1 (zphi z - lz p x) := by
  rw [lz_eq, ← map_sub]
  apply GV_zphi1
  push_cast
  have := ZMod.natCast_zmod_val x
  have h2 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) this
  rw [map_natCast] at h2
  rw [h2, h, sub_self]

lemma GV_Cpow (k : ℕ) : GV p (k : ℤ) (MvPolynomial.C ((p : ℚ) ^ k) : MPT) := by
  apply GV.const
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  rw [zpow_neg, zpow_natCast]
  have : ((p : ℚ) ^ k)⁻¹ * (p : ℚ) ^ k = 1 := inv_mul_cancel₀ (pow_ne_zero _ hp0)
  rw [this]; exact (LocRing p).one_mem

lemma GV.prod_cong_e (e : ℤ) {κ : Type*} {s : Finset κ} {f g : κ → MPT}
    (hf : ∀ k ∈ s, GV p 0 (f k)) (hg : ∀ k ∈ s, GV p 0 (g k)) (h : ∀ k ∈ s, GV p e (f k - g k)) :
    GV p e (∏ k ∈ s, f k - ∏ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GV.zero (p := p) (σ := TVar) e
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hP : GV p 0 (∏ k ∈ s, g k) := by
      have := GV.prod (p := p) (s := s) (e := fun _ => (0 : ℤ)) (f := g)
        (fun k hk => hg k (Finset.mem_insert_of_mem hk))
      simpa using this
    have hP' : GV p 0 (∏ k ∈ s, f k) := by
      have := GV.prod (p := p) (s := s) (e := fun _ => (0 : ℤ)) (f := f)
        (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa using this
    have e1 := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
      (fun k hk => hg k (Finset.mem_insert_of_mem hk)) (fun k hk => h k (Finset.mem_insert_of_mem hk))
    have a1 := (hf a (Finset.mem_insert_self a s)).mul e1
    have a2 := (h a (Finset.mem_insert_self a s)).mul hP
    rw [zero_add] at a1
    rw [add_zero] at a2
    have : f a * ∏ k ∈ s, f k - g a * ∏ k ∈ s, g k =
        f a * (∏ k ∈ s, f k - ∏ k ∈ s, g k) + (f a - g a) * ∏ k ∈ s, g k := by ring
    rw [this]; exact a1.add a2

lemma GV0_mul {f g : MPT} (hf : GV p 0 f) (hg : GV p 0 g) : GV p 0 (f * g) := by
  simpa using hf.mul hg

lemma GVm {e : ℤ} {f g : MPT} (hf : GV p e f) (hg : GV p 0 g) : GV p e (f * g) := by
  simpa using hf.mul hg

lemma GVm' {e : ℤ} {f g : MPT} (hf : GV p 0 f) (hg : GV p e g) : GV p e (f * g) := by
  simpa using hf.mul hg

lemma GV0_add {f g : MPT} (hf : GV p 0 f) (hg : GV p 0 g) : GV p 0 (f + g) := hf.add hg

lemma GV0_pow {f : MPT} (hf : GV p 0 f) (n : ℕ) : GV p 0 (f ^ n) := by
  simpa using hf.pow n

lemma GV0_two : GV p 0 (2 : MPT) := by
  have h := GV.const_int (σ := TVar) (p := p) 2
  have e : (MvPolynomial.C (((2 : ℤ) : ℚ)) : MPT) = 2 := by
    rw [show (((2 : ℤ) : ℚ)) = 2 by norm_num]; exact map_ofNat MvPolynomial.C 2
  rwa [e] at h

lemma GV0_natCast (j : ℕ) : GV p 0 (j : MPT) := by
  have h := GV.const_int (σ := TVar) (p := p) (j : ℤ)
  simpa using h

lemma GV0_Cp : GV p 0 (MvPolynomial.C (p : ℚ) : MPT) :=
  GV.mono (e := 1) (e' := 0) (by norm_num) (by simpa using GV_Cpow (p := p) 1)

lemma GV1_mul_Cp {f : MPT} (hf : GV p 0 f) : GV p 1 (MvPolynomial.C (p : ℚ) * f) := by
  have := (by simpa using GV_Cpow (p := p) 1 : GV p 1 (MvPolynomial.C (p : ℚ) : MPT)).mul hf
  simpa using this

end Lifts


/-! ### Values of the window factors at another residue -/

section ShiftEval

lemma sX_eval_res (r s : ℕ) :
    (sX r).eval (MvPolynomial.C (-(s : ℚ))) = zphi ((r : ℤ) - s) := by
  simp only [sX, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zphi_apply]
  rw [← map_add]; congr 1; push_cast; ring

lemma evk_shiftP_sum (μ r s : ℕ) (A : MPT[X]) :
    evk s (shiftP p μ r A) = ∑ j ∈ range (μ + 1),
      A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j)) * zphi ((r : ℤ) - s) ^ j := by
  unfold evk shiftP
  rw [Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, sX_eval_res]

lemma devk_shiftP_sum (μ r s : ℕ) (A : MPT[X]) :
    devk s (shiftP p μ r A) = ∑ j ∈ range (μ + 1),
      A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j)) * ((j : MPT) * zphi ((r : ℤ) - s) ^ (j - 1)) := by
  unfold devk shiftP
  rw [map_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hd : Polynomial.derivative (sX r) = 1 := by simp [sX]
  rw [Polynomial.derivative_C_mul, Polynomial.derivative_pow, hd, mul_one]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_natCast,
    sX_eval_res]

/-- `P_r(-s) ≡ Δ d^μ + p A_{μ-1} d^{μ-1}` modulo `p²` (`d = r - s`). -/
lemma evk_shiftP_res (μ r s : ℕ) {A : MPT[X]} (hA : PInt p A) :
    GV p 2 (evk s (shiftP p μ r A) -
      (A.coeff μ * zphi ((r : ℤ) - s) ^ μ +
        MvPolynomial.C (p : ℚ) * Aprev A μ * zphi ((r : ℤ) - s) ^ (μ - 1))) := by
  rw [evk_shiftP_sum]
  rcases μ with _ | m
  · simpa [Aprev] using GV.zero (p := p) (σ := TVar) 2
  · rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hT : ∀ j ∈ range m, GV p 2 (A.coeff j * MvPolynomial.C ((p : ℚ) ^ (m + 1 - j)) *
        zphi ((r : ℤ) - s) ^ j) := by
      intro j hj
      have hj' := Finset.mem_range.1 hj
      have h1 := ((hA j).mul (GV_Cpow (p := p) (m + 1 - j))).mul ((GV0_zphi (p := p) ((r : ℤ) - s)).pow j)
      have h2 : (0 : ℤ) + ((m + 1 - j : ℕ) : ℤ) + (j : ℤ) * 0 = ((m + 1 - j : ℕ) : ℤ) := by ring
      rw [h2] at h1
      refine GV.mono ?_ h1
      omega
    have h := GV.sum hT
    have e : (∑ j ∈ range m, A.coeff j * MvPolynomial.C ((p : ℚ) ^ (m + 1 - j)) * zphi ((r : ℤ) - s) ^ j +
          A.coeff m * MvPolynomial.C ((p : ℚ) ^ (m + 1 - m)) * zphi ((r : ℤ) - s) ^ m +
        A.coeff (m + 1) * MvPolynomial.C ((p : ℚ) ^ (m + 1 - (m + 1))) * zphi ((r : ℤ) - s) ^ (m + 1)) -
      (A.coeff (m + 1) * zphi ((r : ℤ) - s) ^ (m + 1) +
        MvPolynomial.C (p : ℚ) * Aprev A (m + 1) * zphi ((r : ℤ) - s) ^ (m + 1 - 1)) =
      ∑ j ∈ range m, A.coeff j * MvPolynomial.C ((p : ℚ) ^ (m + 1 - j)) * zphi ((r : ℤ) - s) ^ j := by
      simp only [Aprev, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.sub_self, pow_zero,
        map_one, pow_one, mul_one, show m + 1 - m = 1 by omega]
      ring
    rw [e]; exact h

lemma devk_shiftP_res (μ r s : ℕ) {A : MPT[X]} (hA : PInt p A) :
    GV p 1 (devk s (shiftP p μ r A) -
      ((μ : MPT) * A.coeff μ * zphi ((r : ℤ) - s) ^ (μ - 1))) := by
  rw [devk_shiftP_sum, Finset.sum_range_succ]
  have hT : ∀ j ∈ range μ, GV p 1 (A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j)) *
      ((j : MPT) * zphi ((r : ℤ) - s) ^ (j - 1))) := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hjn : GV p 0 ((j : MPT)) := by
      have := GV0_zphi (p := p) (j : ℤ)
      simpa [zphi_apply] using this
    have h1 := ((hA j).mul (GV_Cpow (p := p) (μ - j))).mul
      (hjn.mul ((GV0_zphi (p := p) ((r : ℤ) - s)).pow (j - 1)))
    have h2 : (0 : ℤ) + ((μ - j : ℕ) : ℤ) + (0 + ((j - 1 : ℕ) : ℤ) * 0) = ((μ - j : ℕ) : ℤ) := by ring
    rw [h2] at h1
    refine GV.mono ?_ h1
    omega
  have h := GV.sum hT
  have e : (∑ j ∈ range μ, A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j)) *
        ((j : MPT) * zphi ((r : ℤ) - s) ^ (j - 1)) +
      A.coeff μ * MvPolynomial.C ((p : ℚ) ^ (μ - μ)) * ((μ : MPT) * zphi ((r : ℤ) - s) ^ (μ - 1))) -
      ((μ : MPT) * A.coeff μ * zphi ((r : ℤ) - s) ^ (μ - 1)) =
      ∑ j ∈ range μ, A.coeff j * MvPolynomial.C ((p : ℚ) ^ (μ - j)) *
        ((j : MPT) * zphi ((r : ℤ) - s) ^ (j - 1)) := by
    simp only [Nat.sub_self, pow_zero, map_one, mul_one]
    ring
  rw [e]; exact h

end ShiftEval


/-! ### Products over the window -/

section ProdJet

lemma GV1_Cp : GV p 1 (MvPolynomial.C (p : ℚ) : MPT) := by
  simpa using GV_Cpow (p := p) 1

lemma prod_jet {κ : Type*} [DecidableEq κ] (S : Finset κ) (x y : κ → MPT)
    (hx : ∀ r ∈ S, GV p 0 (x r)) (hy : ∀ r ∈ S, GV p 0 (y r)) :
    GV p 2 (∏ r ∈ S, (x r + MvPolynomial.C (p : ℚ) * y r) -
      (∏ r ∈ S, x r + MvPolynomial.C (p : ℚ) * ∑ r ∈ S, y r * ∏ r' ∈ S.erase r, x r')) := by
  induction S using Finset.induction_on with
  | empty => simpa using GV.zero (p := p) (σ := TVar) 2
  | insert a S ha ih =>
    have hxS : ∀ r ∈ S, GV p 0 (x r) := fun r hr => hx r (Finset.mem_insert_of_mem hr)
    have hyS : ∀ r ∈ S, GV p 0 (y r) := fun r hr => hy r (Finset.mem_insert_of_mem hr)
    have ih' := ih hxS hyS
    have hQ0 : GV p 0 (∏ r ∈ S, x r) := by
      have := GV.prod (p := p) (s := S) (e := fun _ => (0 : ℤ)) (f := x) hxS
      simpa using this
    have hQ1 : GV p 0 (∑ r ∈ S, y r * ∏ r' ∈ S.erase r, x r') := by
      refine GV.sum fun r hr => ?_
      have h1 := (hyS r hr).mul (by
        have := GV.prod (p := p) (s := S.erase r) (e := fun _ => (0 : ℤ)) (f := x)
          (fun k hk => hxS k (Finset.mem_of_mem_erase hk))
        simpa using this)
      simpa using h1
    have hsum : ∑ r ∈ insert a S, y r * ∏ r' ∈ (insert a S).erase r, x r' =
        y a * ∏ r ∈ S, x r + x a * ∑ r ∈ S, y r * ∏ r' ∈ S.erase r, x r' := by
      rw [Finset.sum_insert ha, Finset.erase_insert ha, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne : a ≠ r := fun h => ha (h ▸ hr)
      rw [Finset.erase_insert_of_ne hne, Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [Finset.prod_insert ha, Finset.prod_insert ha, hsum]
    set Q := ∏ r ∈ S, (x r + MvPolynomial.C (p : ℚ) * y r) with hQ
    set Q0 := ∏ r ∈ S, x r with hQ0d
    set Q1 := ∑ r ∈ S, y r * ∏ r' ∈ S.erase r, x r' with hQ1d
    have hxa := hx a (Finset.mem_insert_self a S)
    have hya := hy a (Finset.mem_insert_self a S)
    have hQd : GV p 1 (Q - Q0) := by
      have e : Q - Q0 = (Q - (Q0 + MvPolynomial.C (p : ℚ) * Q1)) + MvPolynomial.C (p : ℚ) * Q1 := by ring
      rw [e]
      refine (GV.mono (by norm_num) ih').add ?_
      have := GV1_Cp.mul hQ1
      simpa using this
    have a1 := hxa.mul ih'
    have a2 := (GV1_Cp.mul hya).mul hQd
    rw [zero_add] at a1
    have e2 : (1 : ℤ) + 0 + 1 = 2 := by norm_num
    rw [e2] at a2
    have e : (x a + MvPolynomial.C (p : ℚ) * y a) * Q -
        (x a * Q0 + MvPolynomial.C (p : ℚ) * (y a * Q0 + x a * Q1)) =
        x a * (Q - (Q0 + MvPolynomial.C (p : ℚ) * Q1)) +
          MvPolynomial.C (p : ℚ) * y a * (Q - Q0) := by ring
    rw [e]; exact a1.add a2

end ProdJet


section ResU

/-- `∏_{r∈S} (r - s)^{2μ}`. -/
def Dz (S : Finset ℕ) (s μ : ℕ) : ℤ := ∏ r ∈ S, ((r : ℤ) - s) ^ (2 * μ)

/-- `∑_{r∈S} (r - s)^{2μ-1} ∏_{r'∈S∖r} (r' - s)^{2μ}`. -/
def Sz (S : Finset ℕ) (s μ : ℕ) : ℤ :=
  ∑ r ∈ S, ((r : ℤ) - s) ^ (2 * μ - 1) * Dz (S.erase r) s μ

lemma prod_sq_eq (T : Finset ℕ) (s μ : ℕ) (Δ : MPT) :
    ∏ r ∈ T, (Δ * zphi ((r : ℤ) - s) ^ μ) ^ 2 = Δ ^ (2 * T.card) * zphi (Dz T s μ) := by
  unfold Dz
  rw [map_prod]
  have : ∀ r ∈ T, (Δ * zphi ((r : ℤ) - s) ^ μ) ^ 2 = Δ ^ 2 * zphi (((r : ℤ) - s) ^ (2 * μ)) := by
    intro r _
    rw [map_pow, mul_pow, ← pow_mul, mul_comm μ 2]
  rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul]

lemma sum_sq_eq (S : Finset ℕ) (s μ : ℕ) (Δ A' : MPT) (hμ : μ = 0 → A' = 0) :
    ∑ r ∈ S, (2 * (Δ * zphi ((r : ℤ) - s) ^ μ) * (A' * zphi ((r : ℤ) - s) ^ (μ - 1))) *
        ∏ r' ∈ S.erase r, (Δ * zphi ((r' : ℤ) - s) ^ μ) ^ 2 =
      2 * Δ ^ (2 * S.card - 1) * A' * zphi (Sz S s μ) := by
  unfold Sz
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [prod_sq_eq, Finset.card_erase_of_mem hr, map_mul, map_pow]
  have hc : 1 ≤ S.card := Finset.card_pos.2 ⟨r, hr⟩
  rcases Nat.eq_zero_or_pos μ with h0 | hpos
  · subst h0; rw [hμ rfl]; ring
  · have e1 : 2 * (S.card - 1) + 1 = 2 * S.card - 1 := by omega
    have e2 : μ + (μ - 1) = 2 * μ - 1 := by omega
    have : Δ ^ (2 * S.card - 1) = Δ ^ (2 * (S.card - 1)) * Δ := by rw [← e1, pow_succ]
    rw [this, ← e2, pow_add]
    ring

lemma resU1 (S : Finset ℕ) (s μ : ℕ) {A : MPT[X]} (hA : PInt p A) :
    GV p 2 (∏ r ∈ S, evk s (shiftP p μ r A) ^ 2 -
      (A.coeff μ ^ (2 * S.card) * zphi (Dz S s μ) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * S.card - 1) * Aprev A μ * zphi (Sz S s μ))) := by
  classical
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hA' : GV p 0 (Aprev A μ) := by
    unfold Aprev; split_ifs
    · exact GV.zero _
    · exact hA _
  have hd : ∀ r : ℕ, GV p 0 (zphi ((r : ℤ) - s) ^ μ) := fun r => GV0_pow (GV0_zphi _) μ
  have hd' : ∀ r : ℕ, GV p 0 (zphi ((r : ℤ) - s) ^ (μ - 1)) := fun r => GV0_pow (GV0_zphi _) (μ - 1)
  set a : ℕ → MPT := fun r => A.coeff μ * zphi ((r : ℤ) - s) ^ μ with ha
  set c : ℕ → MPT := fun r => Aprev A μ * zphi ((r : ℤ) - s) ^ (μ - 1) with hc
  have ha0 : ∀ r, GV p 0 (a r) := fun r => GV0_mul hΔ (hd r)
  have hc0 : ∀ r, GV p 0 (c r) := fun r => GV0_mul hA' (hd' r)
  have hπ : ∀ r, GV p 2 (evk s (shiftP p μ r A) - (a r + MvPolynomial.C (p : ℚ) * c r)) := by
    intro r
    have := evk_shiftP_res (p := p) μ r s hA
    have e : A.coeff μ * zphi ((r : ℤ) - s) ^ μ +
        MvPolynomial.C (p : ℚ) * Aprev A μ * zphi ((r : ℤ) - s) ^ (μ - 1) =
        a r + MvPolynomial.C (p : ℚ) * c r := by simp only [ha, hc]; ring
    rwa [e] at this
  have hπ0 : ∀ r, GV p 0 (evk s (shiftP p μ r A)) := by
    intro r
    have e : evk s (shiftP p μ r A) = (evk s (shiftP p μ r A) - (a r + MvPolynomial.C (p : ℚ) * c r)) +
        (a r + MvPolynomial.C (p : ℚ) * c r) := by ring
    rw [e]
    exact (GV.mono (by norm_num) (hπ r)).add ((ha0 r).add (GV.mono (by norm_num) (GV1_mul_Cp (hc0 r))))
  have hsq : ∀ r ∈ S, GV p 2 (evk s (shiftP p μ r A) ^ 2 -
      (a r ^ 2 + MvPolynomial.C (p : ℚ) * (2 * a r * c r))) := by
    intro r _
    have e : evk s (shiftP p μ r A) ^ 2 - (a r ^ 2 + MvPolynomial.C (p : ℚ) * (2 * a r * c r)) =
        (evk s (shiftP p μ r A) - (a r + MvPolynomial.C (p : ℚ) * c r)) *
          (evk s (shiftP p μ r A) + (a r + MvPolynomial.C (p : ℚ) * c r)) +
        (MvPolynomial.C (p : ℚ) * MvPolynomial.C (p : ℚ)) * c r ^ 2 := by ring
    rw [e]
    have g1 : GV p 0 (evk s (shiftP p μ r A) + (a r + MvPolynomial.C (p : ℚ) * c r)) :=
      (hπ0 r).add ((ha0 r).add (GV.mono (by norm_num) (GV1_mul_Cp (hc0 r))))
    have s1 := (hπ r).mul g1
    have s2 := (GV1_Cp.mul GV1_Cp).mul (GV0_pow (hc0 r) 2)
    simp only [add_zero, mul_zero] at s1 s2
    have e2 : (1 : ℤ) + 1 = 2 := by norm_num
    rw [e2] at s2
    exact s1.add s2
  have h1 := GV.prod_cong_e 2 (s := S) (f := fun r => evk s (shiftP p μ r A) ^ 2)
    (g := fun r => a r ^ 2 + MvPolynomial.C (p : ℚ) * (2 * a r * c r))
    (fun r _ => GV0_pow (hπ0 r) 2)
    (fun r _ => GV0_add (GV0_pow (ha0 r) 2)
      (GV.mono (by norm_num) (GV1_mul_Cp (GV0_mul (GV0_mul GV0_two (ha0 r)) (hc0 r)))))
    hsq
  have h2 := prod_jet S (fun r => a r ^ 2) (fun r => 2 * a r * c r)
    (fun r _ => GV0_pow (ha0 r) 2)
    (fun r _ => by
      exact GV0_mul (GV0_mul GV0_two (ha0 r)) (hc0 r))
  have e1 : ∏ r ∈ S, a r ^ 2 = A.coeff μ ^ (2 * S.card) * zphi (Dz S s μ) :=
    prod_sq_eq S s μ _
  have e2 : ∑ r ∈ S, 2 * a r * c r * ∏ r' ∈ S.erase r, a r' ^ 2 =
      2 * A.coeff μ ^ (2 * S.card - 1) * Aprev A μ * zphi (Sz S s μ) :=
    sum_sq_eq S s μ _ _ (fun h0 => by simp [Aprev, h0])
  rw [e1, e2] at h2
  have e3 : ∏ r ∈ S, evk s (shiftP p μ r A) ^ 2 -
      (A.coeff μ ^ (2 * S.card) * zphi (Dz S s μ) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * S.card - 1) * Aprev A μ * zphi (Sz S s μ)) =
      (∏ r ∈ S, evk s (shiftP p μ r A) ^ 2 - ∏ r ∈ S, (a r ^ 2 + MvPolynomial.C (p : ℚ) * (2 * a r * c r))) +
      (∏ r ∈ S, (a r ^ 2 + MvPolynomial.C (p : ℚ) * (2 * a r * c r)) -
        (A.coeff μ ^ (2 * S.card) * zphi (Dz S s μ) +
          MvPolynomial.C (p : ℚ) * (2 * A.coeff μ ^ (2 * S.card - 1) * Aprev A μ * zphi (Sz S s μ)))) := by
    ring
  rw [e3]
  exact h1.add h2

end ResU


section ResUd

lemma evk_prod (k : ℕ) {κ : Type*} (S : Finset κ) (F : κ → MPT[X]) :
    evk k (∏ r ∈ S, F r) = ∏ r ∈ S, evk k (F r) := by
  unfold evk; rw [Polynomial.eval_prod]

lemma devk_prod (k : ℕ) {κ : Type*} [DecidableEq κ] (S : Finset κ) (F : κ → MPT[X]) :
    devk k (∏ r ∈ S, F r) = ∑ r ∈ S, (∏ r' ∈ S.erase r, evk k (F r')) * devk k (F r) := by
  unfold devk
  rw [Polynomial.derivative_prod_finset, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  rfl

lemma sum_sq_eq_d (S : Finset ℕ) (s μ : ℕ) (Δ : MPT) :
    ∑ r ∈ S, (2 * (Δ * zphi ((r : ℤ) - s) ^ μ) * ((μ : MPT) * Δ * zphi ((r : ℤ) - s) ^ (μ - 1))) *
        ∏ r' ∈ S.erase r, (Δ * zphi ((r' : ℤ) - s) ^ μ) ^ 2 =
      2 * (μ : MPT) * Δ ^ (2 * S.card) * zphi (Sz S s μ) := by
  unfold Sz
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [prod_sq_eq, Finset.card_erase_of_mem hr, map_mul, map_pow]
  have hc : 1 ≤ S.card := Finset.card_pos.2 ⟨r, hr⟩
  rcases Nat.eq_zero_or_pos μ with h0 | hpos
  · subst h0; simp
  · have e1 : 2 * (S.card - 1) + 2 = 2 * S.card := by omega
    have e2 : μ + (μ - 1) = 2 * μ - 1 := by omega
    have : Δ ^ (2 * S.card) = Δ ^ (2 * (S.card - 1)) * Δ ^ 2 := by rw [← e1, pow_add]
    rw [this, ← e2, pow_add]
    ring

lemma resU1d (S : Finset ℕ) (s μ : ℕ) {A : MPT[X]} (hA : PInt p A) :
    GV p 1 (devk s (∏ r ∈ S, shiftP p μ r A ^ 2) -
      2 * (μ : MPT) * A.coeff μ ^ (2 * S.card) * zphi (Sz S s μ)) := by
  classical
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hd : ∀ r : ℕ, GV p 0 (zphi ((r : ℤ) - s) ^ μ) := fun r => GV0_pow (GV0_zphi _) μ
  have hd' : ∀ r : ℕ, GV p 0 (zphi ((r : ℤ) - s) ^ (μ - 1)) := fun r => GV0_pow (GV0_zphi _) (μ - 1)
  have hA' : GV p 0 (Aprev A μ) := by
    unfold Aprev; split_ifs
    · exact GV.zero _
    · exact hA _
  obtain ⟨a, ha⟩ : ∃ a : ℕ → MPT, ∀ r, a r = A.coeff μ * zphi ((r : ℤ) - s) ^ μ := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → MPT, ∀ r, b r = (μ : MPT) * A.coeff μ * zphi ((r : ℤ) - s) ^ (μ - 1) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ → MPT, ∀ r, c r = Aprev A μ * zphi ((r : ℤ) - s) ^ (μ - 1) := ⟨_, fun _ => rfl⟩
  have ha0 : ∀ r, GV p 0 (a r) := fun r => by rw [ha]; exact GV0_mul hΔ (hd r)
  have hb0 : ∀ r, GV p 0 (b r) := fun r => by
    rw [hb]; exact GV0_mul (GV0_mul (GV0_natCast μ) hΔ) (hd' r)
  have hc0 : ∀ r, GV p 0 (c r) := fun r => by rw [hc]; exact GV0_mul hA' (hd' r)
  obtain ⟨π, hπd⟩ : ∃ π : ℕ → MPT, ∀ r, π r = evk s (shiftP p μ r A) := ⟨_, fun _ => rfl⟩
  obtain ⟨π', hπ'd⟩ : ∃ π' : ℕ → MPT, ∀ r, π' r = devk s (shiftP p μ r A) := ⟨_, fun _ => rfl⟩
  have hπ : ∀ r, GV p 2 (π r - (a r + MvPolynomial.C (p : ℚ) * c r)) := by
    intro r
    have := evk_shiftP_res (p := p) μ r s hA
    have e : A.coeff μ * zphi ((r : ℤ) - s) ^ μ +
        MvPolynomial.C (p : ℚ) * Aprev A μ * zphi ((r : ℤ) - s) ^ (μ - 1) =
        a r + MvPolynomial.C (p : ℚ) * c r := by rw [ha, hc]; ring
    rw [e, ← hπd] at this; exact this
  have hπ1 : ∀ r, GV p 1 (π r - a r) := by
    intro r
    have e : π r - a r = (π r - (a r + MvPolynomial.C (p : ℚ) * c r)) + MvPolynomial.C (p : ℚ) * c r := by ring
    rw [e]
    exact (GV.mono (by norm_num) (hπ r)).add (GV1_mul_Cp (hc0 r))
  have hπ0 : ∀ r, GV p 0 (π r) := by
    intro r
    have e : π r = (π r - a r) + a r := by ring
    rw [e]; exact (GV.mono (by norm_num) (hπ1 r)).add (ha0 r)
  have hπ' : ∀ r, GV p 1 (π' r - b r) := by
    intro r
    have := devk_shiftP_res (p := p) μ r s hA
    have e : (μ : MPT) * A.coeff μ * zphi ((r : ℤ) - s) ^ (μ - 1) = b r := by rw [hb]
    rw [e, ← hπ'd] at this; exact this
  have hπ'0 : ∀ r, GV p 0 (π' r) := by
    intro r
    have e : π' r = (π' r - b r) + b r := by ring
    rw [e]; exact (GV.mono (by norm_num) (hπ' r)).add (hb0 r)
  have hsq : ∀ r ∈ S, GV p 1 (π r ^ 2 - a r ^ 2) := by
    intro r _
    have e : π r ^ 2 - a r ^ 2 = (π r - a r) * (π r + a r) := by ring
    rw [e]
    exact GVm (hπ1 r) (GV0_add (hπ0 r) (ha0 r))
  rw [devk_prod]
  have hev : ∀ r', evk s (shiftP p μ r' A ^ 2) = π r' ^ 2 := fun r' => by
    rw [hπd]; unfold evk; rw [Polynomial.eval_pow]
  have hdv : ∀ r, devk s (shiftP p μ r A ^ 2) = 2 * π r * π' r := fun r => by
    rw [pow_two, devk_mul, hπd, hπ'd]; unfold evk; ring
  simp only [hev, hdv]
  have hS := sum_sq_eq_d S s μ (A.coeff μ)
  have hS' : ∑ r ∈ S, (2 * a r * b r) * ∏ r' ∈ S.erase r, a r' ^ 2 =
      2 * (μ : MPT) * A.coeff μ ^ (2 * S.card) * zphi (Sz S s μ) := by
    simp only [ha, hb]; exact hS
  rw [← hS', ← Finset.sum_sub_distrib]
  refine GV.sum fun r hr => ?_
  have hP : GV p 1 (∏ r' ∈ S.erase r, π r' ^ 2 - ∏ r' ∈ S.erase r, a r' ^ 2) :=
    GV.prod_cong (fun k hk => GV0_pow (hπ0 k) 2) (fun k hk => GV0_pow (ha0 k) 2)
      (fun k hk => hsq k (Finset.mem_of_mem_erase hk))
  have hQ : GV p 1 (2 * π r * π' r - 2 * a r * b r) := by
    have e : 2 * π r * π' r - 2 * a r * b r = 2 * π r * (π' r - b r) + 2 * (π r - a r) * b r := by ring
    rw [e]
    exact (GVm' (GV0_mul GV0_two (hπ0 r)) (hπ' r)).add (GVm (GVm' GV0_two (hπ1 r)) (hb0 r))
  have hX : GV p 0 (∏ r' ∈ S.erase r, π r' ^ 2) := by
    simpa using GV.prod (p := p) (s := S.erase r) (e := fun _ => (0 : ℤ)) (f := fun k => π k ^ 2)
      (fun k _ => GV0_pow (hπ0 k) 2)
  have hY' : GV p 0 (2 * a r * b r) := GV0_mul (GV0_mul GV0_two (ha0 r)) (hb0 r)
  have e : (∏ r' ∈ S.erase r, π r' ^ 2) * (2 * π r * π' r) -
      2 * a r * b r * ∏ r' ∈ S.erase r, a r' ^ 2 =
      (∏ r' ∈ S.erase r, π r' ^ 2) * (2 * π r * π' r - 2 * a r * b r) +
        (∏ r' ∈ S.erase r, π r' ^ 2 - ∏ r' ∈ S.erase r, a r' ^ 2) * (2 * a r * b r) := by ring
  rw [e]
  exact (GVm' hX hQ).add (GVm hP hY')

end ResUd


/-! ### The unit `K` and the polynomial data at a window residue -/

section Star

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma Epoly_eval (σW s : ℕ) :
    (Epoly n p σW).eval (s : ZMod (p ^ 2)) =
      ∏ r ∈ range p, ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^
        (if sig n p r = σW then 0 else gexp n p σW r) := by
  simp only [Epoly, Polynomial.eval_prod, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X]

lemma isUnit_Epoly (σW s : ℕ) (hs : s < p) (hsW : sig n p s = σW) :
    IsUnit ((Epoly n p σW).eval (s : ZMod (p ^ 2))) := by
  rw [Epoly_eval]
  refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one fun r hr => ?_
  by_cases h : sig n p r = σW
  · simp [h]
  · rw [if_neg h]
    have hr' := Finset.mem_range.1 hr
    refine (isUnit_sub_cast r s hr' hs ?_).pow _
    rintro rfl; exact h hsW

lemma Vneg_eval (V : ℤ[X]) (s : ℕ) :
    (Vneg p V).eval (s : ZMod (p ^ 2)) = ((V.eval (-(s : ℤ)) : ℤ) : ZMod (p ^ 2)) := by
  unfold Vneg
  rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, Polynomial.eval_map]
  have := Polynomial.eval₂_at_apply (Int.castRingHom (ZMod (p ^ 2))) (-(s : ℤ)) (p := V)
  simpa using this

lemma Pe_split (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (s : ℕ) (hs : s ∈ Wf) :
    Pe p (gexp n p σW) s =
      ((Dz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) * (Epoly n p σW).eval (s : ZMod (p ^ 2)) := by
  classical
  rw [Epoly_eval]
  unfold Pe Dz
  push_cast
  have hterm : ∀ r ∈ range p,
      (if r = s then (1 : ZMod (p ^ 2)) else ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ gexp n p σW r) =
      (if r ∈ Wf.erase s then ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^ (2 * μ) else 1) *
        ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^ (if sig n p r = σW then 0 else gexp n p σW r) := by
    intro r hr
    have hr' := Finset.mem_range.1 hr
    have hsig := ((hWf s).1 hs).2
    have hev : ∀ m : ℕ, ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ (2 * m) =
        ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^ (2 * m) := fun m => by
      rw [pow_mul, pow_mul, sq, sq]; ring
    by_cases hrs : r = s
    · subst hrs
      simp [hsig]
    · by_cases hrW : r ∈ Wf
      · have hmem : r ∈ Wf.erase s := Finset.mem_erase.2 ⟨hrs, hrW⟩
        have hsr := ((hWf r).1 hrW).2
        have hg : gexp n p σW r = 2 * μ := by
          unfold gexp; rw [hμ r hrW]; simp [hsr]
        rw [if_neg hrs, if_pos hmem, hg, hev, if_pos hsr, pow_zero, mul_one]
      · have hmem : r ∉ Wf.erase s := fun h => hrW (Finset.mem_of_mem_erase h)
        have hsr : ¬ sig n p r = σW := fun h => hrW ((hWf r).2 ⟨hr', h⟩)
        have hg : gexp n p σW r = 2 * (mu n p r + 1) := by
          unfold gexp; simp [hsr]; ring
        rw [if_neg hrs, if_neg hmem, if_neg hsr, hg, hev]; simp
  rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib]
  congr 1
  refine (Finset.prod_subset (fun r hr => Finset.mem_range.2 (((hWf r).1 (Finset.mem_of_mem_erase hr)).1))
    (fun r _ hr => if_neg hr)).symm.trans ?_
  exact Finset.prod_congr rfl fun r hr => if_pos hr

/-- The unit `K` and the polynomial data: `c̄_s · D · v = K · g · jetp(Ξ + e₀)` whenever
`g · E(s) = Q̂(s) · v`. -/
lemma star_cbar (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s))
    (s : ℕ) (hs : s ∈ Wf) (v : ℤ) (g : ZMod (p ^ 2))
    (hg : g * (Epoly n p σW).eval (s : ZMod (p ^ 2)) = Qhat n p σW s * (v : ZMod (p ^ 2))) :
    ((cbarZ n p s * Dz (Wf.erase s) s μ * v : ℤ) : ZMod (p ^ 2)) =
      Kz * g * jetp p (xiR n p s + e0Z n p s) := by
  have hsp := ((hWf s).1 hs).1
  have hsig := ((hWf s).1 hs).2
  have hU := isUnit_Epoly (n := n) σW s hsp hsig
  have hcb : ((cbarZ n p s : ℤ) : ZMod (p ^ 2)) =
      Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * jetp p (e0Z n p s) := by
    unfold cbarZ; push_cast; rw [ZMod.natCast_zmod_val]
  have hf := hK s hs
  unfold fR at hf
  rw [Pe_split σW Wf hWf μ hμ s hs] at hf
  apply hU.mul_right_cancel
  push_cast
  rw [hcb]
  have e1 : jetp p (xiR n p s + e0Z n p s) = jetp p (xiR n p s) * jetp p (e0Z n p s) := by
    rw [jetp_mul]
  rw [e1]
  linear_combination (jetp p (e0Z n p s) * (v : ZMod (p ^ 2))) * hf + (Kz * jetp p (xiR n p s) * jetp p (e0Z n p s)) * (-1 : ZMod (p ^ 2)) * hg

lemma Dz_cast (T : Finset ℕ) (s μ : ℕ) :
    ((Dz T s μ : ℤ) : ZMod (p ^ 2)) = ∏ r ∈ T, ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^ (2 * μ) := by
  unfold Dz; push_cast; rfl

lemma Sz_cast (Wf : Finset ℕ) (hWp : ∀ r ∈ Wf, r < p) (s : ℕ) (hsW : s ∈ Wf) (μ : ℕ) (hμ : 1 ≤ μ) :
    ((Sz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) =
      ((Dz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) * sigW p Wf s := by
  have hs := hWp s hsW
  unfold Sz sigW
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_erase.1 hr
  have hu : IsUnit ((r : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) := isUnit_sub_cast r s (hWp r hr'.2) hs hr'.1.symm
  have hD := Finset.mul_prod_erase (Wf.erase s) (fun r' => ((r' : ZMod (p ^ 2)) - (s : ZMod (p ^ 2))) ^ (2 * μ)) hr
  have hDz : ((Dz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) =
      ((r : ZMod (p ^ 2)) - s) ^ (2 * μ) *
        ((Dz ((Wf.erase s).erase r) s μ : ℤ) : ZMod (p ^ 2)) := by
    rw [Dz_cast, Dz_cast]; exact hD.symm
  rw [hDz]
  have hinv := ZMod.mul_inv_of_unit _ hu
  obtain ⟨m, hm1, hm2⟩ : ∃ m, 2 * μ - 1 = m ∧ 2 * μ = m + 1 := ⟨2 * μ - 1, rfl, by omega⟩
  rw [hm1, hm2, pow_succ ((r : ZMod (p ^ 2)) - s) m]
  linear_combination (((r : ZMod (p ^ 2)) - s) ^ m * ((Dz ((Wf.erase s).erase r) s μ : ℤ) : ZMod (p ^ 2))) * (-1 : ZMod (p ^ 2)) * hinv

lemma evk_pow (k : ℕ) (F : MPT[X]) (m : ℕ) : evk k (F ^ m) = evk k F ^ m := by
  unfold evk; rw [Polynomial.eval_pow]

lemma evk_map_zphi (V : ℤ[X]) (s : ℕ) : evk s (V.map zphi) = zphi (V.eval (-(s : ℤ))) := by
  unfold evk
  have : (MvPolynomial.C (-(s : ℚ)) : MPT) = zphi (-(s : ℤ)) := by simp [zphi_apply]
  rw [this, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply zphi (-(s : ℤ))

lemma devk_map_zphi (V : ℤ[X]) (s : ℕ) :
    devk s (V.map zphi) = zphi ((Polynomial.derivative V).eval (-(s : ℤ))) := by
  unfold devk
  have : (MvPolynomial.C (-(s : ℚ)) : MPT) = zphi (-(s : ℤ)) := by simp [zphi_apply]
  rw [this, Polynomial.derivative_map, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply zphi (-(s : ℤ))

end Star


/-! ### Lifting lemmas for the window sums -/

section WinLemmas

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma lz_add2 (x y : ZMod (p ^ 2)) : GV p 2 (lz p (x + y) - (lz p x + lz p y)) := by
  have h := GV_lz_sub2 (p := p) (x + y) (z := (x.val : ℤ) + (y.val : ℤ)) (by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have e : lz p (x + y) - (lz p x + lz p y) = -(zphi ((x.val : ℤ) + (y.val : ℤ)) - lz p (x + y)) := by
    rw [lz_eq x, lz_eq y, map_add]; ring
  rw [e]; exact h.neg

lemma lz_mul2 (x y : ZMod (p ^ 2)) : GV p 2 (lz p (x * y) - lz p x * lz p y) := by
  have h := GV_lz_sub2 (p := p) (x * y) (z := (x.val : ℤ) * (y.val : ℤ)) (by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have e : lz p (x * y) - lz p x * lz p y = -(zphi ((x.val : ℤ) * (y.val : ℤ)) - lz p (x * y)) := by
    rw [lz_eq x, lz_eq y, map_mul]; ring
  rw [e]; exact h.neg

lemma lz_zero : lz p (0 : ZMod (p ^ 2)) = 0 := by
  unfold lz; simp

lemma lz_sum (S : Finset ℕ) (x : ℕ → ZMod (p ^ 2)) :
    GV p 2 (lz p (∑ s ∈ S, x s) - ∑ s ∈ S, lz p (x s)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa [lz_zero] using GV.zero (p := p) (σ := TVar) 2
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e : lz p (x a + ∑ s ∈ S, x s) - (lz p (x a) + ∑ s ∈ S, lz p (x s)) =
        (lz p (x a + ∑ s ∈ S, x s) - (lz p (x a) + lz p (∑ s ∈ S, x s))) +
          (lz p (∑ s ∈ S, x s) - ∑ s ∈ S, lz p (x s)) := by ring
    rw [e]; exact (lz_add2 _ _).add ih

lemma lz_congr1 {x y : ZMod (p ^ 2)} (h : ρ x = ρ y) : GV p 1 (lz p x - lz p y) := by
  rw [lz_eq x]
  apply GV_lz_sub1
  rw [← h]
  have := ZMod.natCast_zmod_val x
  have h2 := congrArg ρ this
  rw [map_natCast] at h2
  push_cast
  exact h2

lemma GV1_lz_of_rho {x : ZMod (p ^ 2)} (h : ρ x = 0) : GV p 1 (lz p x) := by
  have := lz_congr1 (x := x) (y := 0) (by rw [h, map_zero])
  rwa [lz_zero, sub_zero] at this

lemma GV0_evk {R : MPT[X]} (hR : PInt p R) (k : ℕ) : GV p 0 (evk k R) :=
  GV_eval hR ((LocRing p).neg_mem (natq_mem k))

lemma GV0_devk {R : MPT[X]} (hR : PInt p R) (k : ℕ) : GV p 0 (devk k R) :=
  GV_eval (PInt_derivative hR) ((LocRing p).neg_mem (natq_mem k))

end WinLemmas


section WinLocal

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma GV0_linM {F : MPT[X]} (hF : PInt p F) {m : ℕ → MPT} (hm : ∀ i, GV p 0 (m i)) :
    GV p 0 (linM m F) := by
  unfold linM
  rw [Polynomial.sum_def]
  exact GV.sum fun i _ => GV0_mul (hF i) (hm i)

lemma GV0_locUtau (L : ℕ) {τu : ℕ → ℚ} (hτu : ∀ l, τu l ∈ LocRing p) {Φ : MPT[X]} (hΦ : PInt p Φ) :
    GV p 0 (locUtau L τu Φ) := by
  unfold locUtau
  refine GV.sum fun l _ => GV0_mul ((GV.var (p := p) _).sub (GV.const_loc (hτu _))) ?_
  exact GV0_evk hΦ (l + 1)

lemma uaL_mem (l : ℕ) (hl : l < p) : uaL l ∈ LocRing p := by
  unfold uaL
  exact (LocRing p).mul_mem (by simpa using (LocRing p).neg_mem ((LocRing p).add_mem
    ((LocRing p).add_mem ((LocRing p).one_mem) ((LocRing p).one_mem)) ((LocRing p).one_mem)))
    (Hq_mem 2 l hl)

lemma vaL_mem {n : ℕ} (h8 : 8 * n < p ^ 2) (k l : ℕ) (hk : k ≤ 6 * n) (hl : l < p) :
    vaL n p k l ∈ LocRing p := by
  unfold vaL
  have h3 : ((-3 : ℚ)) ∈ LocRing p := by
    simpa using (LocRing p).neg_mem ((LocRing p).add_mem
      ((LocRing p).add_mem ((LocRing p).one_mem) ((LocRing p).one_mem)) ((LocRing p).one_mem))
  refine (LocRing p).mul_mem h3 ((LocRing p).add_mem ((LocRing p).mul_mem (delta_mem n k h8 hk) (Hq_mem 2 l hl))
    ((LocRing p).mul_mem ?_ (Hq_mem 3 l hl)))
  simpa using (LocRing p).add_mem ((LocRing p).one_mem) ((LocRing p).one_mem)

lemma GV0_locAk {n : ℕ} (h8 : 8 * n < p ^ 2) (s L : ℕ) (hL : s + L * p ≤ 6 * n) {kap : ℕ → ℚ}
    (hkap : ∀ l, kap l ∈ LocRing p) {Φ : MPT[X]} (hΦ : PInt p Φ) :
    GV p 0 (locAk n p s L kap Φ) := by
  have hLp : L < p := by
    by_contra hc
    push_neg at hc
    have : p * p ≤ L * p := Nat.mul_le_mul_right p hc
    nlinarith [pow_two p]
  unfold locAk
  refine GV.sum fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  refine GV0_mul (GV.const_loc (hkap _)) (GV0_add (GV0_mul (GV.const_loc (uaL_mem _ (by omega))) ?_)
    (GV0_mul (GV.const_loc (vaL_mem h8 _ _ ?_ (by omega))) ?_))
  · exact GV0_devk hΦ (l + 1)
  · have : (l + 1) * p ≤ L * p := Nat.mul_le_mul_right p (by omega)
    omega
  · exact GV0_evk hΦ (l + 1)

lemma node_div_mod (s l : ℕ) (hs : s < p) : (s + l * p) / p = l ∧ (s + l * p) % p = s := by
  have hp0 := hp.out.pos
  constructor
  · rw [Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hs, zero_add]
  · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]

lemma locAk_const {n : ℕ} (h8 : 8 * n < p ^ 2) (s s' L : ℕ) (hs : s < p) (hs' : s' < p)
    (hL : s + L * p ≤ 6 * n) (hL' : s' + L * p ≤ 6 * n)
    (hb : bflag n p s = bflag n p s') (he : eflag n p s = eflag n p s') (Φ : MPT[X]) :
    locAk n p s L (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) Φ =
      locAk n p s' L (fun l => (kapZ n p (bflag n p s') (eflag n p s') l : ℚ)) Φ := by
  unfold locAk
  rw [hb, he]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  have hk : s + (l + 1) * p ≤ 6 * n := by
    have : (l + 1) * p ≤ L * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hk' : s' + (l + 1) * p ≤ 6 * n := by
    have : (l + 1) * p ≤ L * p := Nat.mul_le_mul_right p (by omega)
    omega
  have e1 := laiDelta_digits (p := p) (n := n) hk
  have e2 := laiDelta_digits (p := p) (n := n) hk'
  obtain ⟨d1, m1⟩ := node_div_mod (p := p) s (l + 1) hs
  obtain ⟨d2, m2⟩ := node_div_mod (p := p) s' (l + 1) hs'
  rw [d1, m1] at e1
  rw [d2, m2] at e2
  rw [hb, he] at e1
  have : vaL n p (s + (l + 1) * p) (l + 1) = vaL n p (s' + (l + 1) * p) (l + 1) := by
    unfold vaL
    rw [e1, e2]
  rw [this]

end WinLocal


section Bridge

lemma inv_term (m : ℕ) (hm : m + 1 < p) :
    GV p 2 (MvPolynomial.C (1 / ((m : ℚ) + 1)) -
      lz p ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹)) := by
  set u : ℕ := ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹).val with hu
  have hunit := isUnit_cast_p2 (p := p) (i := m + 1) (by omega) hm
  have hmul : (((m + 1 : ℕ) : ZMod (p ^ 2))) * ((m + 1 : ℕ) : ZMod (p ^ 2))⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ hunit
  have hcast : (((m + 1 : ℕ) : ℤ) * (u : ℤ) - 1 : ℤ) = ((p : ℤ) ^ 2) * ((((m + 1 : ℕ) : ℤ) * (u : ℤ) - 1) / (p : ℤ) ^ 2) := by
    have hz : ((((m + 1 : ℕ) : ℤ) * (u : ℤ) - 1 : ℤ) : ZMod (p ^ 2)) = 0 := by
      have e1 : ((((m + 1 : ℕ) : ℤ) * (u : ℤ) - 1 : ℤ) : ZMod (p ^ 2)) =
          ((m + 1 : ℕ) : ZMod (p ^ 2)) * ((u : ℕ) : ZMod (p ^ 2)) - 1 := by push_cast; ring
      rw [e1, hu, ZMod.natCast_zmod_val, hmul]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 hz
    have h2 : ((p ^ 2 : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
    rw [h2] at this
    exact (Int.mul_ediv_cancel' this).symm
  rw [lz_eq, ← hu, zphi_apply, ← map_sub]
  apply GV.const
  set k : ℤ := (((m + 1 : ℕ) : ℤ) * (u : ℤ) - 1) / (p : ℤ) ^ 2 with hk
  have hq : ((m : ℚ) + 1) * (u : ℚ) - 1 = (p : ℚ) ^ 2 * (k : ℚ) := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hcast
    push_cast at this
    linarith
  have hpq : (p : ℚ) ≠ 0 := p_ne_zero
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hnd : ¬ p ∣ (m + 1) := fun h => by have := Nat.le_of_dvd (by omega) h; omega
  have hmem := inv_natCast_mem_locRing (ℓ := p) hnd
  have e : (p : ℚ) ^ (-(2 : ℤ)) * (1 / ((m : ℚ) + 1) - (((u : ℤ)) : ℚ)) = -((k : ℚ) * ((m + 1 : ℕ) : ℚ)⁻¹) := by
    have hu' : (((u : ℤ)) : ℚ) = (u : ℚ) := by simp
    rw [hu']
    have : 1 / ((m : ℚ) + 1) - (u : ℚ) = -((p : ℚ) ^ 2 * (k : ℚ)) / ((m : ℚ) + 1) := by
      field_simp
      linarith
    rw [this]
    push_cast
    rw [zpow_neg, zpow_ofNat]
    field_simp
  rw [e]
  exact (LocRing p).neg_mem ((LocRing p).mul_mem (int_mem_locRing k) hmem)

lemma Hq_Hz (m : ℕ) (hm : m < p) :
    GV p 1 (MvPolynomial.C (Hq 1 m) - lz p (Hz p m)) := by
  induction m with
  | zero => simpa [Hq_zero, Hz_zero, lz_zero] using GV.zero (p := p) (σ := TVar) 1
  | succ m ih =>
    have ih' := ih (by omega)
    rw [Hq_succ, Hz_succ, map_add]
    have h1 := inv_term (p := p) m hm
    have h2 := lz_add2 (p := p) (Hz p m) ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹)
    have e : MvPolynomial.C (Hq 1 m) + MvPolynomial.C (1 / ((m : ℚ) + 1) ^ 1) -
        lz p (Hz p m + ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹)) =
        (MvPolynomial.C (Hq 1 m) - lz p (Hz p m)) +
          (MvPolynomial.C (1 / ((m : ℚ) + 1)) - lz p ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹)) -
          (lz p (Hz p m + ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹)) -
            (lz p (Hz p m) + lz p ((((m + 1 : ℕ) : ZMod (p ^ 2)))⁻¹))) := by
      rw [pow_one]; ring
    rw [e]
    exact (ih'.add (GV.mono (by norm_num) h1)).sub (GV.mono (by norm_num) h2)

end Bridge


section Lam0Bridge

lemma lam0_bridge (n : ℕ) (s : ℕ) (hs : s < p) :
    GV p 1 (MvPolynomial.C (lam0 n p s) - lz p (lam0Z n p s)) := by
  have hr6 := r6_lt n p hp.out.pos
  have hr2 := r2_lt n p hp.out.pos
  have ha : r2 n p + s - eflag n p s * p < p := by
    rcases eflag_cases n p s hr2 hs with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] <;> omega
  have hb : r6 n p + bflag n p s * p - s < p := by
    rcases bflag_cases n p s with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] <;> omega
  have h1 := Hq_Hz (p := p) _ ha
  have h2 := Hq_Hz (p := p) _ hb
  have h3 := Hq_Hz (p := p) _ hs
  have hz := GV_lz_sub2 (p := p) (lam0Z n p s)
    (z := 3 * ((Hz p (r2 n p + s - eflag n p s * p)).val : ℤ) +
      2 * ((Hz p (r6 n p + bflag n p s * p - s)).val : ℤ) - 5 * ((Hz p s).val : ℤ)) (by
      unfold lam0Z
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  have e : MvPolynomial.C (lam0 n p s) - lz p (lam0Z n p s) =
      (3 * (MvPolynomial.C (Hq 1 (r2 n p + s - eflag n p s * p)) - lz p (Hz p (r2 n p + s - eflag n p s * p))) +
        2 * (MvPolynomial.C (Hq 1 (r6 n p + bflag n p s * p - s)) - lz p (Hz p (r6 n p + bflag n p s * p - s))) -
        5 * (MvPolynomial.C (Hq 1 s) - lz p (Hz p s))) +
      (zphi (3 * ((Hz p (r2 n p + s - eflag n p s * p)).val : ℤ) +
        2 * ((Hz p (r6 n p + bflag n p s * p - s)).val : ℤ) - 5 * ((Hz p s).val : ℤ)) - lz p (lam0Z n p s)) := by
    unfold lam0
    simp only [map_add, map_sub, map_mul, map_ofNat, lz_eq]
    ring
  rw [e]
  have g3 : GV p 0 (3 : MPT) := by simpa using GV0_natCast (p := p) 3
  have g5 : GV p 0 (5 : MPT) := by simpa using GV0_natCast (p := p) 5
  exact GV.add (((GVm' g3 h1).add (GVm' GV0_two h2)).sub (GVm' g5 h3)) (GV.mono (by norm_num) hz)

end Lam0Bridge


section WSum

/-- The cofactor `R_s = (∏_{r ∈ W, r ≠ s} P_r²) · V` of `P_s²` in the pair product. -/
def Rres (p μ : ℕ) (Wf : Finset ℕ) (A : MPT[X]) (V : ℤ[X]) (s : ℕ) : MPT[X] :=
  (∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi

lemma PInt_map_zphi (V : ℤ[X]) : PInt p (V.map zphi : MPT[X]) := by
  intro i
  rw [Polynomial.coeff_map]
  exact GV0_zphi _

lemma PInt_Rres (μ : ℕ) (Wf : Finset ℕ) {A : MPT[X]} (hA : PInt p A) (V : ℤ[X]) (s : ℕ) :
    PInt p (Rres p μ Wf A V s) :=
  (PInt.prod fun r _ => (PInt_shiftP μ r hA).pow 2).mul (PInt_map_zphi V)

lemma Rres_eq (μ : ℕ) (Wf : Finset ℕ) (A : MPT[X]) (V : ℤ[X]) {s : ℕ} (hs : s ∈ Wf) :
    (∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi = shiftP p μ s A ^ 2 * Rres p μ Wf A V s := by
  unfold Rres
  rw [← Finset.mul_prod_erase Wf (fun r => shiftP p μ r A) hs, mul_pow, Finset.prod_pow]
  ring

lemma sum_comb (S : Finset ℕ) (P Q T : ℕ → MPT) (bT cp aT Lt Lx Lu La : MPT) :
    ∑ s ∈ S, (bT * (P s * Lt + cp * (Q s - T s) * Lx + cp * T s * Lu) + cp * aT * P s * La) =
      bT * ((∑ s ∈ S, P s) * Lt + cp * ((∑ s ∈ S, Q s) - ∑ s ∈ S, T s) * Lx +
        cp * (∑ s ∈ S, T s) * Lu) + cp * aT * (∑ s ∈ S, P s) * La := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, ih]
    ring

lemma wsum_core {n : ℕ} (h : Rng n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (L : ℕ)
    (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (hτu : ∀ l, τu l ∈ LocRing p)
    (hL : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p)
    (hKn : ∀ s ∈ Wf, s ∉ K ∧ ∀ l, 1 ≤ l → l ≤ L →
      (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ) (V : ℤ[X]) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2)
    (hb1 : GV p (m : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)))
    (hb2 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)))
    (hb3 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s))) :
    GV p ((σW : ℤ) + 2 * μ - 4 + m)
      (∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p)
        ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)) := by
  classical
  rcases Wf.eq_empty_or_nonempty with hW0 | ⟨s0, hs0⟩
  · subst hW0; simpa using GV.zero (p := p) (σ := TVar) _
  have h8 := h.h8
  have h3 : 3 ≤ p := by have := h.p5; omega
  have hsig : ∀ s ∈ Wf, (sig n p s : ℤ) = σW := fun s hs => by rw [((hWf s).1 hs).2]
  have hlt : ∀ s ∈ Wf, s < p := fun s hs => ((hWf s).1 hs).1
  -- Step A: the node sums against the jets (Lemma P)
  have hA2 : ∀ s ∈ Wf, GV p ((σW : ℤ) + 2 * μ - 2)
      (∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p)
          ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) -
        resJet n p s L μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A
          (Rres p μ Wf A V s)) := by
    intro s hs
    have := res_second n K σ cl τu τv h8 h3 s (hlt s hs) L (hL s hs).1 (hL s hs).2
      (fun l h1 h2 => (hKn s hs).2 l h1 h2) (hKn s hs).1 μ A hA hAd (Rres p μ Wf A V s)
      (PInt_Rres μ Wf hA V s)
    rw [hsig s hs] at this
    rw [Rres_eq μ Wf A V hs]
    exact this
  have hsumA := GV.sum (s := Wf) hA2
  rw [Finset.sum_sub_distrib] at hsumA
  -- Step B: the jet main terms
  have hAsq : PInt p (A ^ 2) := hA.pow 2
  have hXA : PInt p (Polynomial.X * A ^ 2) := PInt_X.mul hAsq
  have Lt0 : GV p 0 (linM (cLoc L) (A ^ 2)) := GV0_linM hAsq (fun i => GV_cLoc L i)
  have Lx0 : GV p 0 (linM (cLoc L) (Polynomial.X * A ^ 2)) := GV0_linM hXA (fun i => GV_cLoc L i)
  have Lu0 : GV p 0 (locUtau L τu (A ^ 2)) := GV0_locUtau L hτu hAsq
  have La0 : GV p 0 (locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2)) :=
    GV0_locAk h8 s0 L (hL s0 hs0).1 (fun l => int_mem_locRing _) hAsq
  have hres : ∀ s ∈ Wf, resJet n p s L μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A
        (Rres p μ Wf A V s) =
      MvPolynomial.C ((p : ℚ) ^ ((σW : ℤ) + 2 * μ - 4)) *
        (bT * (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) * linM (cLoc L) (A ^ 2) +
            MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
              zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
              linM (cLoc L) (Polynomial.X * A ^ 2) +
            MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
              evk s (Rres p μ Wf A V s)) * locUtau L τu (A ^ 2)) +
          MvPolynomial.C (p : ℚ) * aT * (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) *
            locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2)) := by
    intro s hs
    have hsig' : sig n p s = sig n p s0 := ((hWf s).1 hs).2.trans ((hWf s0).1 hs0).2.symm
    obtain ⟨hb, he⟩ := flags_of_sig n p s s0 hsig'
    unfold resJet
    rw [locAk_const h8 s s0 L (hlt s hs) (hlt s0 hs0) (hL s hs).1 (hL s0 hs0).1 hb he, hsig s hs]
    simp only [map_mul, zphi_apply, evk, devk]
    ring
  rw [Finset.sum_congr rfl hres, ← Finset.mul_sum] at hsumA
  have hcomb := sum_comb Wf (fun s => zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s))
    (fun s => zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s))
    (fun s => zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s))
    bT (MvPolynomial.C (p : ℚ)) aT (linM (cLoc L) (A ^ 2)) (linM (cLoc L) (Polynomial.X * A ^ 2))
    (locUtau L τu (A ^ 2))
    (locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2))
  rw [hcomb] at hsumA
  have hbT : GV p 0 bT := GV.var _
  have haT : GV p 0 aT := GV.var _
  have hm1' : (1 : ℤ) + ((m : ℤ) - 1) = m := by ring
  have t1 := GVm hb1 Lt0
  have hd := hb2.sub hb3
  have t2 : GV p (m : ℤ) (MvPolynomial.C (p : ℚ) * (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
      ∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
      linM (cLoc L) (Polynomial.X * A ^ 2)) := by
    have := GVm (GV1_Cp.mul hd) Lx0
    rwa [hm1'] at this
  have t3 : GV p (m : ℤ) (MvPolynomial.C (p : ℚ) * (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s)) * locUtau L τu (A ^ 2)) := by
    have := GVm (GV1_Cp.mul hb3) Lu0
    rwa [hm1'] at this
  have t4 : GV p (m : ℤ) (MvPolynomial.C (p : ℚ) * aT * (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) *
      locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2)) := by
    have := GVm ((GVm GV1_Cp haT).mul hb1) La0
    exact GV.mono (by omega) this
  have hB : GV p (m : ℤ) (bT * ((∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) * linM (cLoc L) (A ^ 2) +
      MvPolynomial.C (p : ℚ) * (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
        ∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
        linM (cLoc L) (Polynomial.X * A ^ 2) +
      MvPolynomial.C (p : ℚ) * (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
        evk s (Rres p μ Wf A V s)) * locUtau L τu (A ^ 2)) +
      MvPolynomial.C (p : ℚ) * aT * (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) *
        locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2)) := by
    exact (GVm' hbT ((t1.add t2).add t3)).add t4
  have hJ := (GV.const_zpow_mul_iff (p := p) (σ := TVar) (e := (m : ℤ)) (k := (σW : ℤ) + 2 * μ - 4)).2 hB
  have hfin := (GV.mono (e := (σW : ℤ) + 2 * μ - 2) (e' := (σW : ℤ) + 2 * μ - 4 + m) (by omega) hsumA).add
    (GV.mono (e := (m : ℤ) + ((σW : ℤ) + 2 * μ - 4)) (e' := (σW : ℤ) + 2 * μ - 4 + m) (by omega) hJ)
  simpa using hfin

end WSum

/-! ### Rows -/


section Row17

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

/-- L2S-17. -/
theorem scalar_second (h : Rng n p) (hx2 : 0 < xtwo n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (hne : Wf.Nonempty)
    (G Hr : (ZMod (p ^ 2))[X]) (hGd : G.natDegree ≤ p - 4) (hHd : Hr.natDegree ≤ p - 2)
    (hG : ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0)
    (hG' : ∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0)
    (hH : ∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0) :
    (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) = 0) ∧
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
      (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * sigW p Wf s) = 0 ∧
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
      (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * lam0Z n p s) = 0 ∧
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (∑ s ∈ Wf, Hr.eval (s : ZMod (p ^ 2))) = 0 ∧
    ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2))) = 0 := by
  classical
  have h5 := h.p5
  have hr6 := r6_lt n p hp.out.pos
  have hr2 := r2_lt n p hp.out.pos
  obtain ⟨w0, w1, hIcc, hw1⟩ := window_Icc σW Wf hWf hne
  obtain ⟨s0, hs0⟩ := hne
  have hne' : Wf.Nonempty := ⟨s0, hs0⟩
  have hWp : ∀ s ∈ Wf, s < p := fun s hs => ((hWf s).1 hs).1
  have hflag : ∀ s ∈ Wf, bflag n p s = bflag n p s0 ∧ eflag n p s = eflag n p s0 := fun s hs =>
    flags_of_sig n p s s0 (((hWf s).1 hs).2.trans ((hWf s0).1 hs0).2.symm)
  have hbc : ∀ s ∈ Wf, (bflag n p s0 = 0 ∧ s ≤ r6 n p) ∨ (bflag n p s0 = 1 ∧ r6 n p < s) := by
    intro s hs; rw [← (hflag s hs).1]; exact bflag_cases n p s
  have hec : ∀ s ∈ Wf, (eflag n p s0 = 0 ∧ s + r2 n p < p) ∨ (eflag n p s0 = 1 ∧ p ≤ s + r2 n p) := by
    intro s hs; rw [← (hflag s hs).2]; exact eflag_cases n p s hr2 (hWp s hs)
  -- reduction mod p of polynomials
  have hev : ∀ (F : (ZMod (p ^ 2))[X]) (m : ℕ),
      (F.map ρ).eval ((m : ℕ) : ZMod p) = ρ (F.eval (m : ZMod (p ^ 2))) := by
    intro F m
    rw [← map_natCast ρ m, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have hGb : (G.map ρ).natDegree ≤ p - 4 := Polynomial.natDegree_map_le.trans hGd
  have hGv : ∀ m, m < p → m ∉ Wf → (G.map ρ).eval ((m : ℕ) : ZMod p) = 0 := by
    intro m hm hmW; rw [hev, hG m hm hmW, map_zero]
  have hGv' : ∀ m, m < p → m ∉ Wf → (Polynomial.derivative (G.map ρ)).eval ((m : ℕ) : ZMod p) = 0 := by
    intro m hm hmW; rw [Polynomial.derivative_map, hev, hG' m hm hmW, map_zero]
  have hlam : ((lam n p : ℤ) : ZMod p) = 2 * (q6 n p : ZMod p) - 3 * (q2 n p : ZMod p) - 3 := by
    have := (law_second_level h hx2).1
    rw [this]; push_cast; ring
  have hrhs : ∀ (A B C : ZMod p) (f : ℕ → ZMod (p ^ 2)),
      (∀ s ∈ Wf, ρ (f s) = A * harm p s + B * harm p (r6 n p + bflag n p s0 * p - s) +
        C * harm p (r2 n p + s - eflag n p s0 * p)) →
      ρ (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * f s) = (A + B + C) * harmSum p (G.map ρ) := by
    intro A B C f hf
    rw [map_sum, ← word_sum hGb h5 Wf hne' hWp hGv hGv' (r6 n p) (r2 n p) (bflag n p s0)
      (eflag n p s0) hr6 hr2 hbc hec A B C]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [map_mul, ← hev, hf s hs]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- S₀
    obtain ⟨y, hy1, hy2⟩ := faulhaber_bridge G (by omega : G.natDegree ≤ p - 2)
    have hy := hy2 (ZMod p) ρ
    have hsub : ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) = ∑ s ∈ range p, G.eval (s : ZMod (p ^ 2)) := by
      refine Finset.sum_subset (fun s hs => Finset.mem_range.2 (hWp s hs)) (fun m hm hmW => ?_)
      exact hG m (Finset.mem_range.1 hm) hmW
    have hS : ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) =
        (p : ZMod (p ^ 2)) * (y + ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s)) := by
      unfold jetp
      have e : ∀ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * (1 + (p : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s)) =
          G.eval (s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) *
            (G.eval (s : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s)) := fun s _ => by ring
      rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, hsub, hy1, mul_add]
    rw [hS]
    apply pmul_eq_zero
    rw [map_add, hy, hrhs ((lam n p : ZMod p) - 1) (-2 * (q6 n p : ZMod p)) (3 * (1 + (q2 n p : ZMod p)))
      (fun s => xiR n p s + e0Z n p s) (fun s hs => by
        rw [rho_XiE0 h (hWp s hs), (hflag s hs).1, (hflag s hs).2])]
    have : ((lam n p : ZMod p) - 1) + -2 * (q6 n p : ZMod p) + 3 * (1 + (q2 n p : ZMod p)) = -1 := by
      rw [hlam]; ring
    rw [this]; ring
  · -- S₁
    have hcast : ZMod.castHom (dvd_refl p) (ZMod p) = RingHom.id (ZMod p) := ZMod.castHom_self
    have e : ∀ s ∈ Wf, ρ (G.eval (s : ZMod (p ^ 2)) * sigW p Wf s) =
        (G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (w1 - s) -
          (G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (s - w0) := by
      intro s hs
      have hs' : s ∈ Icc w0 w1 := hIcc ▸ hs
      rw [map_mul, ← hev, rho_sigW Wf hWp s (hWp s hs), hIcc, sigW_harm hs', mul_sub]
    rw [map_sum, Finset.sum_congr rfl e, Finset.sum_sub_distrib]
    have hw0 : w0 < p := by
      have := Finset.mem_Icc.1 (hIcc ▸ hs0 : s0 ∈ Icc w0 w1); omega
    have r1 := harmSum_window_refl (G.map ρ) hGb h5 Wf w1 hw1
      (fun s hs => (Finset.mem_Icc.1 (hIcc ▸ hs : s ∈ Icc w0 w1)).2) hGv hGv'
    have r2 := harmSum_window_neg (G.map ρ) hGb h5 Wf w0 hw0
      (fun s hs => ⟨(Finset.mem_Icc.1 (hIcc ▸ hs : s ∈ Icc w0 w1)).1, hWp s hs⟩) hGv hGv'
    simp only [hcast, RingHom.id_apply] at r1 r2
    rw [r1, r2]; ring
  · have := hrhs (-5) 2 3 (fun s => lam0Z n p s) (fun s hs => by
      rw [rho_lam0 h (hWp s hs), (hflag s hs).1, (hflag s hs).2])
    rw [this]; ring
  · have := sum_window_poly_zero (Hr.map ρ) (Polynomial.natDegree_map_le.trans hHd) Wf hWp
      (fun m hm hmW => by rw [hev, hH m hm hmW, map_zero])
    rw [map_sum]
    simpa [hev] using this
  · have := sum_window_poly_zero (G.map ρ) (by omega) Wf hWp hGv
    rw [map_sum]
    simpa [hev] using this

end Row17

section Row1415

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

/-- The values of `G`, `H` at a window residue against the polynomial identities. -/
lemma poly_ident_eval (σW : ℕ) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V) (s : ℕ) :
    G.eval (s : ZMod (p ^ 2)) * (Epoly n p σW).eval (s : ZMod (p ^ 2)) =
      Qhat n p σW s * ((V.eval (-(s : ℤ)) : ℤ) : ZMod (p ^ 2)) := by
  have := congrArg (Polynomial.eval (s : ZMod (p ^ 2))) hGE
  rwa [Polynomial.eval_mul, Polynomial.eval_mul, QhatPoly_eval, Vneg_eval] at this

lemma Aprev_GV0 {A : MPT[X]} (hA : PInt p A) (μ : ℕ) : GV p 0 (Aprev A μ) := by
  unfold Aprev; split_ifs
  · exact GV.zero _
  · exact hA _

/-- L2S-14, Lemma Q(i). -/
theorem resprod_p2 (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V)
    (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s))
    (s : ℕ) (hs : s ∈ Wf) :
    GV p 2 (zphi (cbarZ n p s) *
        evk s ((∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi) -
      (A.coeff μ ^ (2 * Wf.card - 2) *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by
  classical
  have hWp : ∀ r ∈ Wf, r < p := fun r hr => ((hWf r).1 hr).1
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hA' := Aprev_GV0 hA μ
  have hc1 : 1 ≤ Wf.card := Finset.card_pos.2 ⟨s, hs⟩
  have hcard : (Wf.erase s).card = Wf.card - 1 := Finset.card_erase_of_mem hs
  have e2 : 2 * Wf.card - 2 = 2 * (Wf.erase s).card := by omega
  have e3 : 2 * Wf.card - 3 = 2 * (Wf.erase s).card - 1 := by omega
  rw [e2, e3]
  have hev : evk s ((∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi) =
      (∏ r ∈ Wf.erase s, evk s (shiftP p μ r A) ^ 2) * zphi (V.eval (-(s : ℤ))) := by
    rw [evk_mul, evk_prod, evk_map_zphi]
    congr 1
    exact Finset.prod_congr rfl fun r _ => evk_pow _ _ _
  rw [hev]
  have hstar := star_cbar σW Wf hWf μ hμ Kz hK s hs (V.eval (-(s : ℤ))) _
    (poly_ident_eval σW V G hGE s)
  have h1 := resU1 (Wf.erase s) s μ hA
  have h3 := GV_lz_sub2 (p := p) (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) hstar
  generalize hP : ∏ r ∈ Wf.erase s, evk s (shiftP p μ r A) ^ 2 = Pr at h1 ⊢
  generalize hv : V.eval (-(s : ℤ)) = v at hstar h3 ⊢
  have h2 : GV p 2 (zphi (cbarZ n p s) * (Pr * zphi v) - zphi (cbarZ n p s * v) *
      (A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
          zphi (Sz (Wf.erase s) s μ))) := by
    have e : zphi (cbarZ n p s) * (Pr * zphi v) - zphi (cbarZ n p s * v) *
      (A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
          zphi (Sz (Wf.erase s) s μ)) = zphi (cbarZ n p s * v) * (Pr - (A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
          zphi (Sz (Wf.erase s) s μ))) := by
      rw [map_mul]; ring
    rw [e]; exact GVm' (GV0_zphi _) h1
  have h4 : GV p 2 (2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
      (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
        lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by
    by_cases hμ0 : μ = 0
    · simp [Aprev, hμ0]; exact GV.zero _
    · have hμ1 : 1 ≤ μ := Nat.one_le_iff_ne_zero.2 hμ0
      have hz : ρ ((cbarZ n p s * v * Sz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) =
          ρ (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s) := by
        have : ((cbarZ n p s * v * Sz (Wf.erase s) s μ : ℤ) : ZMod (p ^ 2)) =
            ((cbarZ n p s * Dz (Wf.erase s) s μ * v : ℤ) : ZMod (p ^ 2)) * sigW p Wf s := by
          push_cast
          have := Sz_cast Wf hWp s hs μ hμ1
          push_cast at this
          rw [this]; ring
        rw [this, hstar]
        simp only [map_mul, jetp_cast_one, mul_one]
      have hd1 : GV p 1 (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)) := by
        apply GV_lz_sub1
        rw [← hz, map_intCast]
      have c0 : GV p 0 (2 * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ) :=
        GV0_mul (GV0_mul GV0_two (GV0_pow hΔ _)) hA'
      have hCd : GV p 2 (MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by
        have := GV1_Cp.mul hd1
        rwa [show (1 : ℤ) + 1 = 2 by norm_num] at this
      have e : 2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
          (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
            lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)) =
          (2 * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ) *
            (MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
              lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by ring
      rw [e]; exact GVm' c0 hCd
  have hc0 : GV p 0 (A.coeff μ ^ (2 * (Wf.erase s).card)) := GV0_pow hΔ _
  have e : zphi (cbarZ n p s) * (Pr * zphi v) -
      (A.coeff μ ^ (2 * (Wf.erase s).card) *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)) =
      (zphi (cbarZ n p s) * (Pr * zphi v) - zphi (cbarZ n p s * v) *
        (A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) +
          2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
            zphi (Sz (Wf.erase s) s μ))) +
      A.coeff μ ^ (2 * (Wf.erase s).card) *
        (zphi (cbarZ n p s * Dz (Wf.erase s) s μ * v) -
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s))) +
      2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
        (zphi (cbarZ n p s * v * Sz (Wf.erase s) s μ) -
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)) := by
    simp only [map_mul]; ring
  rw [e]
  exact (h2.add (GVm' hc0 h3)).add h4

/-- L2S-15, Lemma Q(ii). -/
theorem resderiv_p (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G Hr : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V)
    (hHE : Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V))
    (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s))
    (s : ℕ) (hs : s ∈ Wf) :
    GV p 1 (zphi (cbarZ n p s) *
        devk s ((∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi) -
      A.coeff μ ^ (2 * Wf.card - 2) *
        lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
          Hr.eval (s : ZMod (p ^ 2))))) := by
  classical
  have hWp : ∀ r ∈ Wf, r < p := fun r hr => ((hWf r).1 hr).1
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hA' := Aprev_GV0 hA μ
  have hc1 : 1 ≤ Wf.card := Finset.card_pos.2 ⟨s, hs⟩
  have hcard : (Wf.erase s).card = Wf.card - 1 := Finset.card_erase_of_mem hs
  have e2 : 2 * Wf.card - 2 = 2 * (Wf.erase s).card := by omega
  rw [e2]
  have hdv : devk s ((∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi) =
      devk s (∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * zphi (V.eval (-(s : ℤ))) +
        (∏ r ∈ Wf.erase s, evk s (shiftP p μ r A) ^ 2) *
          zphi ((Polynomial.derivative V).eval (-(s : ℤ))) := by
    rw [devk_mul, evk_prod, evk_map_zphi, devk_map_zphi]
    congr 2
    exact Finset.prod_congr rfl fun r _ => evk_pow _ _ _
  rw [hdv]
  have hstarG := star_cbar σW Wf hWf μ hμ Kz hK s hs (V.eval (-(s : ℤ))) _
    (poly_ident_eval σW V G hGE s)
  have hstarH := star_cbar σW Wf hWf μ hμ Kz hK s hs ((Polynomial.derivative V).eval (-(s : ℤ))) _
    (poly_ident_eval σW (Polynomial.derivative V) Hr hHE s)
  have h1d := resU1d (Wf.erase s) s μ hA
  have h1 := resU1 (Wf.erase s) s μ hA
  generalize hP : ∏ r ∈ Wf.erase s, evk s (shiftP p μ r A) ^ 2 = Pr at h1 ⊢
  generalize hU : devk s (∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) = dU at h1d ⊢
  generalize hv : V.eval (-(s : ℤ)) = v at hstarG ⊢
  generalize hv' : (Polynomial.derivative V).eval (-(s : ℤ)) = v' at hstarH ⊢
  have hz : ρ (((2 * (μ : ℤ)) * (cbarZ n p s * v * Sz (Wf.erase s) s μ) +
        cbarZ n p s * Dz (Wf.erase s) s μ * v' : ℤ) : ZMod (p ^ 2)) =
      ρ (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
        Hr.eval (s : ZMod (p ^ 2)))) := by
    rcases Nat.eq_zero_or_pos μ with h0 | hpos
    · subst h0
      have e : (((2 * ((0 : ℕ) : ℤ)) * (cbarZ n p s * v * Sz (Wf.erase s) s 0) +
          cbarZ n p s * Dz (Wf.erase s) s 0 * v' : ℤ) : ZMod (p ^ 2)) =
          ((cbarZ n p s * Dz (Wf.erase s) s 0 * v' : ℤ) : ZMod (p ^ 2)) := by simp
      rw [e, hstarH]
      simp only [map_mul, jetp_cast_one, mul_one, Nat.cast_zero, mul_zero, zero_mul, zero_add]
    · have hSz := Sz_cast Wf hWp s hs μ hpos
      have e : (((2 * (μ : ℤ)) * (cbarZ n p s * v * Sz (Wf.erase s) s μ) +
          cbarZ n p s * Dz (Wf.erase s) s μ * v' : ℤ) : ZMod (p ^ 2)) =
          (2 * (μ : ZMod (p ^ 2))) * (((cbarZ n p s * Dz (Wf.erase s) s μ * v : ℤ) : ZMod (p ^ 2)) *
            sigW p Wf s) + ((cbarZ n p s * Dz (Wf.erase s) s μ * v' : ℤ) : ZMod (p ^ 2)) := by
        push_cast at hSz ⊢
        rw [hSz]; ring
      rw [e, hstarG, hstarH]
      push_cast
      simp only [map_mul, map_add, jetp_cast_one, mul_one, map_natCast, map_ofNat]
      ring
  have hzG : GV p 1 (zphi ((2 * (μ : ℤ)) * (cbarZ n p s * v * Sz (Wf.erase s) s μ) +
        cbarZ n p s * Dz (Wf.erase s) s μ * v') -
      lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
        Hr.eval (s : ZMod (p ^ 2))))) := by
    apply GV_lz_sub1
    rw [← hz, map_intCast]
  have hXp : GV p 1 (Pr - A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ)) := by
    have e : Pr - A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) =
        (Pr - (A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ) +
          2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
            zphi (Sz (Wf.erase s) s μ))) +
        MvPolynomial.C (p : ℚ) * (2 * A.coeff μ ^ (2 * (Wf.erase s).card - 1) * Aprev A μ *
            zphi (Sz (Wf.erase s) s μ)) := by ring
    rw [e]
    exact (GV.mono (by norm_num) h1).add (GV1_mul_Cp
      (GV0_mul (GV0_mul (GV0_mul GV0_two (GV0_pow hΔ _)) hA') (GV0_zphi _)))
  have hc0 : GV p 0 (A.coeff μ ^ (2 * (Wf.erase s).card)) := GV0_pow hΔ _
  have e : zphi (cbarZ n p s) * (dU * zphi v + Pr * zphi v') -
      A.coeff μ ^ (2 * (Wf.erase s).card) *
        lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
          Hr.eval (s : ZMod (p ^ 2)))) =
      zphi (cbarZ n p s * v) * (dU - 2 * (μ : MPT) * A.coeff μ ^ (2 * (Wf.erase s).card) *
          zphi (Sz (Wf.erase s) s μ)) +
      zphi (cbarZ n p s * v') * (Pr - A.coeff μ ^ (2 * (Wf.erase s).card) * zphi (Dz (Wf.erase s) s μ)) +
      A.coeff μ ^ (2 * (Wf.erase s).card) *
        (zphi ((2 * (μ : ℤ)) * (cbarZ n p s * v * Sz (Wf.erase s) s μ) +
            cbarZ n p s * Dz (Wf.erase s) s μ * v') -
          lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
            Hr.eval (s : ZMod (p ^ 2))))) := by
    simp only [map_mul, map_add, map_natCast, map_ofNat]; ring
  rw [e]
  exact ((GVm' (GV0_zphi _) h1d).add (GVm' (GV0_zphi _) hXp)).add (GVm' hc0 hzG)

end Row1415

section Rows1618

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma sumG_rho (Wf : Finset ℕ) (hWp : ∀ s ∈ Wf, s < p) (G : (ZMod (p ^ 2))[X]) (hGd : G.natDegree ≤ p - 2)
    (hG : ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) :
    ρ (∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2))) = 0 := by
  have hev : ∀ (F : (ZMod (p ^ 2))[X]) (m : ℕ),
      (F.map ρ).eval ((m : ℕ) : ZMod p) = ρ (F.eval (m : ZMod (p ^ 2))) := by
    intro F m
    rw [← map_natCast ρ m, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have := sum_window_poly_zero (G.map ρ) (Polynomial.natDegree_map_le.trans hGd) Wf hWp
    (fun m hm hmW => by rw [hev, hG m hm hmW, map_zero])
  rw [map_sum]
  simpa [hev] using this

/-- Each residue contribution `c̄_s R_s(-s)` is `Δ^{2w-2} K G(s)` modulo `p`. -/
lemma Wcong1 (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s))
    (s : ℕ) (hs : s ∈ Wf) :
    GV p 1 (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
      A.coeff μ ^ (2 * Wf.card - 2) * lz p (Kz * G.eval (s : ZMod (p ^ 2)))) := by
  have h := resprod_p2 σW Wf hWf μ hμ A hA hAd V G hGE Kz hK s hs
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hA' := Aprev_GV0 hA μ
  have hj : GV p 1 (lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) -
      lz p (Kz * G.eval (s : ZMod (p ^ 2)))) :=
    lz_congr1 (by simp only [map_mul, jetp_cast_one, mul_one])
  have e : zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
      A.coeff μ ^ (2 * Wf.card - 2) * lz p (Kz * G.eval (s : ZMod (p ^ 2))) =
      (zphi (cbarZ n p s) * evk s ((∏ r ∈ Wf.erase s, shiftP p μ r A ^ 2) * V.map zphi) -
        (A.coeff μ ^ (2 * Wf.card - 2) *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) +
      A.coeff μ ^ (2 * Wf.card - 2) * (lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) -
        lz p (Kz * G.eval (s : ZMod (p ^ 2)))) +
      MvPolynomial.C (p : ℚ) * (2 * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)) := by
    unfold Rres; ring
  rw [e]
  exact ((GV.mono (by norm_num) h).add (GVm' (GV0_pow hΔ _) hj)).add
    (GV1_mul_Cp (GV0_mul (GV0_mul (GV0_mul GV0_two (GV0_pow hΔ _)) hA') (GV0_lz _)))

lemma lam0_GV0 (n s : ℕ) (hs : s < p) : GV p 0 (MvPolynomial.C (lam0 n p s) : MPT) := by
  have h := lam0_bridge (p := p) n s hs
  have e : (MvPolynomial.C (lam0 n p s) : MPT) = (MvPolynomial.C (lam0 n p s) - lz p (lam0Z n p s)) +
      lz p (lam0Z n p s) := by ring
  rw [e]; exact (GV.mono (by norm_num) h).add (GV0_lz _)

/-- L2S-16, Lemma W1. -/
theorem wsum_first (h : Rng n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (L : ℕ)
    (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (hτu : ∀ l, τu l ∈ LocRing p)
    (hL : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p)
    (hKn : ∀ s ∈ Wf, s ∉ K ∧ ∀ l, 1 ≤ l → l ≤ L →
      (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V)
    (hGd : G.natDegree ≤ p - 2)
    (hG : ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0)
    (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s)) :
    GV p ((σW : ℤ) + 2 * μ - 3)
      (∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p)
        ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)) := by
  classical
  have hWp : ∀ r ∈ Wf, r < p := fun r hr => ((hWf r).1 hr).1
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hR : ∀ s, PInt p (Rres p μ Wf A V s) := fun s => PInt_Rres μ Wf hA V s
  have hb1 : GV p ((1 : ℕ) : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) := by
    have h1 : GV p 1 (∑ s ∈ Wf, (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
        A.coeff μ ^ (2 * Wf.card - 2) * lz p (Kz * G.eval (s : ZMod (p ^ 2))))) :=
      GV.sum fun s hs => Wcong1 σW Wf hWf μ hμ A hA hAd V G hGE Kz hK s hs
    have h2 : GV p 1 (A.coeff μ ^ (2 * Wf.card - 2) *
        (∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2))))) := by
      have e : ∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2))) =
          lz p (∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2))) -
            (lz p (∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2))) - ∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2)))) := by ring
      have hz : ρ (∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2))) = 0 := by
        rw [← Finset.mul_sum, map_mul, sumG_rho Wf hWp G hGd hG, mul_zero]
      rw [e]
      exact GVm' (GV0_pow hΔ _) ((GV1_lz_of_rho hz).sub
        (GV.mono (by norm_num) (lz_sum Wf (fun s => Kz * G.eval (s : ZMod (p ^ 2))))))
    have := h1.add h2
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    simpa using this
  have hb2 : GV p (((1 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) := by
    have : (((1 : ℕ) : ℤ) - 1) = 0 := by norm_num
    rw [this]
    exact GV.sum fun s _ => GV0_mul (GV0_zphi _) (GV0_devk (hR s) s)
  have hb3 : GV p (((1 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s)) := by
    have : (((1 : ℕ) : ℤ) - 1) = 0 := by norm_num
    rw [this]
    exact GV.sum fun s hs => GV0_mul (GV0_mul (GV0_zphi _) (lam0_GV0 n s (hWp s hs))) (GV0_evk (hR s) s)
  have := wsum_core h σW Wf hWf μ L K σ cl τu τv hτu hL hKn A hA hAd V 1 le_rfl (by norm_num) hb1 hb2 hb3
  convert this using 2
  push_cast; ring


lemma a3_term (σW : ℕ) (Wf : Finset ℕ) (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s))
    (s : ℕ) (hs : s ∈ Wf) :
    GV p 1 (zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s) -
      A.coeff μ ^ (2 * Wf.card - 2) * lz p (lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2))))) := by
  have hsp := ((hWf s).1 hs).1
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hR : PInt p (Rres p μ Wf A V s) := PInt_Rres μ Wf hA V s
  have hu := Wcong1 σW Wf hWf μ hμ A hA hAd V G hGE Kz hK s hs
  have hδ := lam0_bridge (p := p) n s hsp
  have hW0 : GV p 0 (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) :=
    GV0_mul (GV0_zphi _) (GV0_evk hR s)
  have hm2 := lz_mul2 (p := p) (lam0Z n p s) (Kz * G.eval (s : ZMod (p ^ 2)))
  have e : zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s) -
      A.coeff μ ^ (2 * Wf.card - 2) * lz p (lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2)))) =
      (MvPolynomial.C (lam0 n p s) - lz p (lam0Z n p s)) *
        (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) +
      lz p (lam0Z n p s) * (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
        A.coeff μ ^ (2 * Wf.card - 2) * lz p (Kz * G.eval (s : ZMod (p ^ 2)))) -
      A.coeff μ ^ (2 * Wf.card - 2) *
        (lz p (lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2)))) -
          lz p (lam0Z n p s) * lz p (Kz * G.eval (s : ZMod (p ^ 2)))) := by ring
  rw [e]
  exact ((GVm hδ hW0).add (GVm' (GV0_lz _) hu)).sub
    (GVm' (GV0_pow hΔ _) (GV.mono (by norm_num) hm2))


lemma sum_lz_GV1 (S : Finset ℕ) (x : ℕ → ZMod (p ^ 2)) (h : ρ (∑ s ∈ S, x s) = 0) :
    GV p 1 (∑ s ∈ S, lz p (x s)) := by
  have e : ∑ s ∈ S, lz p (x s) = lz p (∑ s ∈ S, x s) - (lz p (∑ s ∈ S, x s) - ∑ s ∈ S, lz p (x s)) := by ring
  rw [e]
  exact (GV1_lz_of_rho h).sub (GV.mono (by norm_num) (lz_sum S x))

lemma sum_lz_GV2 (S : Finset ℕ) (x : ℕ → ZMod (p ^ 2)) (h : ∑ s ∈ S, x s = 0) :
    GV p 2 (∑ s ∈ S, lz p (x s)) := by
  have := (lz_sum (p := p) S x).neg
  rw [h, lz_zero] at this
  simpa using this

/-- L2S-18, Lemma W2. -/
theorem wsum_second (h : Rng n p) (hx2 : 0 < xtwo n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (hne : Wf.Nonempty)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ) (L : ℕ)
    (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (hτu : ∀ l, τu l ∈ LocRing p)
    (hL : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p)
    (hKn : ∀ s ∈ Wf, s ∉ K ∧ ∀ l, 1 ≤ l → l ≤ L →
      (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G Hr : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V)
    (hHE : Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V))
    (hGd : G.natDegree ≤ p - 4) (hHd : Hr.natDegree ≤ p - 2)
    (hG : ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0)
    (hG' : ∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0)
    (hH : ∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0)
    (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s)) :
    GV p ((σW : ℤ) + 2 * μ - 2)
      (∑ s ∈ Wf, ∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p)
        ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)) := by
  classical
  obtain ⟨hS0, hS1, hSl, hSH, hSG⟩ := scalar_second h hx2 σW Wf hWf hne G Hr hGd hHd hG hG' hH
  have hWp : ∀ r ∈ Wf, r < p := fun r hr => ((hWf r).1 hr).1
  have hΔ : GV p 0 (A.coeff μ) := hA μ
  have hA' := Aprev_GV0 hA μ
  have hR : ∀ s, PInt p (Rres p μ Wf A V s) := fun s => PInt_Rres μ Wf hA V s
  have hKrho : ∀ (c : ZMod (p ^ 2)) (f : ℕ → ZMod (p ^ 2)),
      ρ (∑ s ∈ Wf, f s) = 0 → ρ (∑ s ∈ Wf, Kz * (c * f s)) = 0 := by
    intro c f hf
    rw [← Finset.mul_sum, ← Finset.mul_sum, map_mul, map_mul, hf, mul_zero, mul_zero]
  -- a1
  have hb1 : GV p ((2 : ℕ) : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) := by
    have h1 : GV p 2 (∑ s ∈ Wf, (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
        (A.coeff μ ^ (2 * Wf.card - 2) *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) +
        2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
          lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s)))) :=
      GV.sum fun s hs => resprod_p2 σW Wf hWf μ hμ A hA hAd V G hGE Kz hK s hs
    have hx : ∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) = 0 := by
      have : ∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) =
          Kz * ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, hS0, mul_zero]
    have hy : ρ (∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s) = 0 := by
      have : ∑ s ∈ Wf, Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s =
          Kz * ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * sigW p Wf s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, map_mul, hS1, mul_zero]
    have h2 := sum_lz_GV2 Wf _ hx
    have h3 := sum_lz_GV1 Wf _ hy
    have c0 : GV p 0 (2 * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ) :=
      GV0_mul (GV0_mul GV0_two (GV0_pow hΔ _)) hA'
    have h4 : GV p 2 (A.coeff μ ^ (2 * Wf.card - 2) *
        (∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s))) +
      MvPolynomial.C (p : ℚ) * (2 * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
        ∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by
      refine (GVm' (GV0_pow hΔ _) h2).add ?_
      have := GV1_Cp.mul (GVm' c0 h3)
      rwa [show (1 : ℤ) + 1 = 2 by norm_num] at this
    have e : ∑ s ∈ Wf, (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
          (A.coeff μ ^ (2 * Wf.card - 2) *
            lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s)) +
          2 * MvPolynomial.C (p : ℚ) * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
            lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) =
        ∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) -
        (A.coeff μ ^ (2 * Wf.card - 2) *
          (∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s))) +
        MvPolynomial.C (p : ℚ) * (2 * A.coeff μ ^ (2 * Wf.card - 3) * Aprev A μ *
          ∑ s ∈ Wf, lz p (Kz * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    rw [e] at h1
    have := h1.add h4
    simpa using this
  -- a2
  have hb2 : GV p (((2 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) := by
    have h1 : GV p 1 (∑ s ∈ Wf, (zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
        A.coeff μ ^ (2 * Wf.card - 2) *
          lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
            Hr.eval (s : ZMod (p ^ 2)))))) :=
      GV.sum fun s hs => resderiv_p σW Wf hWf μ hμ A hA hAd V G Hr hGE hHE Kz hK s hs
    have hz : ρ (∑ s ∈ Wf, Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s +
          Hr.eval (s : ZMod (p ^ 2)))) = 0 := by
      rw [← Finset.mul_sum, map_mul, Finset.sum_add_distrib]
      have : ∑ s ∈ Wf, ((2 * μ : ℕ) : ZMod (p ^ 2)) * G.eval (s : ZMod (p ^ 2)) * sigW p Wf s =
          ((2 * μ : ℕ) : ZMod (p ^ 2)) * ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * sigW p Wf s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, map_add, map_mul, hS1, hSH, mul_zero, add_zero, mul_zero]
    have h2 := sum_lz_GV1 Wf _ hz
    have h3 : GV p 1 (A.coeff μ ^ (2 * Wf.card - 2) * ∑ s ∈ Wf, lz p (Kz * (((2 * μ : ℕ) : ZMod (p ^ 2)) *
        G.eval (s : ZMod (p ^ 2)) * sigW p Wf s + Hr.eval (s : ZMod (p ^ 2))))) := GVm' (GV0_pow hΔ _) h2
    have := h1.add h3
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    simpa using this
  -- a3
  have hb3 : GV p (((2 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s)) := by
    have h1 : GV p 1 (∑ s ∈ Wf, (zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s) -
        A.coeff μ ^ (2 * Wf.card - 2) * lz p (lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2)))))) :=
      GV.sum fun s hs => a3_term σW Wf hWf μ hμ A hA hAd V G hGE Kz hK s hs
    have hz : ρ (∑ s ∈ Wf, lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2)))) = 0 := by
      have : ∑ s ∈ Wf, lam0Z n p s * (Kz * G.eval (s : ZMod (p ^ 2))) =
          Kz * ∑ s ∈ Wf, G.eval (s : ZMod (p ^ 2)) * lam0Z n p s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, map_mul, hSl, mul_zero]
    have h2 := sum_lz_GV1 Wf _ hz
    have := h1.add (GVm' (GV0_pow hΔ (2 * Wf.card - 2)) h2)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    simpa using this
  have := wsum_core h σW Wf hWf μ L K σ cl τu τv hτu hL hKn A hA hAd V 2 (by norm_num) le_rfl hb1 hb2 hb3
  convert this using 2
  push_cast; ring

end Rows1618

end

end CatalanCore.Lai

#print axioms CatalanCore.Lai.harm_refl
#print axioms CatalanCore.Lai.scalar_second
#print axioms CatalanCore.Lai.resprod_p2
#print axioms CatalanCore.Lai.resderiv_p
#print axioms CatalanCore.Lai.wsum_first
#print axioms CatalanCore.Lai.wsum_second
