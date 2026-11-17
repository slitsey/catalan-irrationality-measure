module

public import CatalanCore.Lai.ContentBasisT
public import CatalanCore.Lai.ContentLemmaR
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `CatalanCore.Lai.ContentL2Jet`: node jets (Theorem L2 by node jets, rows L2S-01..11 and 13)

Paper: `L2-SIMPLE-2026-11-16.md` (Lemmas H, G2, J0, J, P, O).  Everything is stated over the generic
functional `L_T` on `MPT = ℚ[a, b, X, T]`.

* digit harmonics: `harm_digit`, `Hq_digit_lead`, `laiH_digits`;
* unit part modulo `p²`: `laiCoef_kc_p2`, `clZ_split`, `clZ_split_Q`;
* jet valuation `JetGE` (`ν_k(F) ≥ e`): submultiplicative, values of the window factors;
* Lemma J: `nd_jet`, `nodeT_jet`, `nd0_jet`; Taylor step `taylor_p2`;
* Lemma P `res_second` (per-residue formula) and Lemma O `own_pair`.
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid

namespace CatalanCore.Lai

noncomputable section

/-! ### Part 1: harmonic digits -/

section HarmDigit

variable {p : ℕ} [hp : Fact p.Prime]

lemma redQ_Hq (m : ℕ) (hm : m < p) :
    redQ p (⟨Hq 1 m, Hq_mem 1 m hm⟩ : LocRing p) = harm p m := by
  induction m with
  | zero =>
    have : (⟨Hq 1 0, Hq_mem 1 0 hm⟩ : LocRing p) = 0 := Subtype.ext (by simp [Hq_zero])
    rw [this, map_zero, harm_zero]
  | succ m ih =>
    have hm' : m < p := by omega
    have hnd : ¬ p ∣ (m + 1) := fun h => by
      have := Nat.le_of_dvd (by omega) h; omega
    have hy : (1 / ((m : ℚ) + 1) : ℚ) ∈ LocRing p := by
      have := inv_pow_mem (p := p) hnd 1
      simpa using this
    set y : LocRing p := ⟨1 / ((m : ℚ) + 1), hy⟩ with hydef
    have hsum : (⟨Hq 1 (m + 1), Hq_mem 1 (m + 1) hm⟩ : LocRing p) = ⟨Hq 1 m, Hq_mem 1 m hm'⟩ + y := by
      apply Subtype.ext
      simp only [Subring.coe_add, hydef]
      rw [Hq_succ]; simp
    have hmul : y * ((m + 1 : ℕ) : LocRing p) = 1 := by
      apply Subtype.ext
      simp only [hydef, Subring.coe_mul, Subring.coe_natCast, Subring.coe_one]
      push_cast
      field_simp
    have h1 := congrArg (redQ p) hmul
    rw [map_mul, map_natCast, map_one] at h1
    rw [hsum, map_add, ih hm', harm_succ]
    congr 1
    exact eq_inv_of_mul_eq_one_left h1

lemma Hq_pm1 (h3 : 3 ≤ p) : (p : ℚ)⁻¹ * Hq 1 (p - 1) ∈ LocRing p := by
  have hlt : p - 1 < p := by have := hp.out.pos; omega
  set x : LocRing p := ⟨Hq 1 (p - 1), Hq_mem 1 (p - 1) hlt⟩ with hx
  have h0 : redQ p x = 0 := by rw [hx, redQ_Hq (p - 1) hlt, harm_top h3]
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p x).1 h0
  have hq : Hq 1 (p - 1) = (p : ℚ) * (y : ℚ) := by
    have := congrArg Subtype.val hy
    simpa [hx] using this
  rw [hq]
  have hp0 := p_ne_zero' (p := p)
  have : (p : ℚ)⁻¹ * ((p : ℚ) * (y : ℚ)) = (y : ℚ) := by field_simp
  rw [this]; exact y.2

/-- **L2S-01** (harmonic digit lemma, Lemma H(i)). -/
theorem harm_digit (h3 : 3 ≤ p) (m : ℕ) :
    (p : ℚ)⁻¹ * (Hq 1 m - (p : ℚ)⁻¹ * Hq 1 (m / p) - Hq 1 (m % p)) ∈ LocRing p := by
  have hpp := hp.out.pos
  have hp0 := p_ne_zero' (p := p)
  induction m with
  | zero => simp [Hq_zero]
  | succ m ih =>
    by_cases hd : p ∣ m + 1
    · obtain ⟨t, ht⟩ := hd
      have ht0 : 0 < t := by
        rcases Nat.eq_zero_or_pos t with h | h
        · subst h; omega
        · exact h
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have hm : m = (p - 1) + p * t' := by
        have h2 : m + 1 = p * t' + p := by rw [ht]; ring
        omega
      have hdiv : m / p = t' := by
        rw [hm, Nat.add_mul_div_left _ _ hpp, Nat.div_eq_of_lt (by omega)]
        simp
      have hmod : m % p = p - 1 := by
        rw [hm, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
      have hdiv1 : (m + 1) / p = t' + 1 := by
        rw [ht]; exact Nat.mul_div_cancel_left _ hpp
      have hmod1 : (m + 1) % p = 0 := by rw [ht]; exact Nat.mul_mod_right _ _
      rw [hdiv, hmod] at ih
      rw [hdiv1, hmod1, Hq_succ, Hq_succ]
      have hcast : ((m : ℚ) + 1) = p * ((t' : ℚ) + 1) := by exact_mod_cast ht
      have hq : 1 / ((m : ℚ) + 1) ^ 1 = (p : ℚ)⁻¹ * (1 / ((t' : ℚ) + 1) ^ 1) := by
        rw [hcast]
        have : ((t' : ℚ) + 1) ≠ 0 := by positivity
        field_simp
      have key : (p : ℚ)⁻¹ * (Hq 1 m + 1 / ((m : ℚ) + 1) ^ 1 -
          (p : ℚ)⁻¹ * (Hq 1 t' + 1 / ((t' : ℚ) + 1) ^ 1) - Hq 1 0) =
          (p : ℚ)⁻¹ * (Hq 1 m - (p : ℚ)⁻¹ * Hq 1 t' - Hq 1 (p - 1)) + (p : ℚ)⁻¹ * Hq 1 (p - 1) := by
        rw [hq, Hq_zero]; ring
      rw [key]
      exact (LocRing p).add_mem ih (Hq_pm1 h3)
    · have hdiv : (m + 1) / p = m / p := Nat.succ_div_of_not_dvd hd
      have hdm := Nat.div_add_mod m p
      have hdm1 := Nat.div_add_mod (m + 1) p
      have hmlt := Nat.mod_lt m hpp
      have hlt : m % p + 1 < p := by
        by_contra hc
        apply hd
        refine ⟨m / p + 1, ?_⟩
        rw [hdiv] at hdm1
        have : m % p + 1 = p := by omega
        nlinarith
      have hmod : (m + 1) % p = m % p + 1 := by
        rw [hdiv] at hdm1
        omega
      rw [hdiv, hmod, Hq_succ, Hq_succ (j := 1) (m := m % p)]
      have hnd1 : ¬ p ∣ (m % p + 1) := fun h => by
        have := Nat.le_of_dvd (by omega) h; omega
      have hc1 := inv_pow_mem (p := p) hd 1
      have hc2 := inv_pow_mem (p := p) hnd1 1
      have hcast : ((m : ℚ) + 1) = p * ((m / p : ℕ) : ℚ) + ((m % p : ℕ) : ℚ) + 1 := by
        have : (m : ℚ) = ((p * (m / p) + m % p : ℕ) : ℚ) := by rw [hdm]
        push_cast at this
        linarith
      have key : (p : ℚ)⁻¹ * (Hq 1 m + 1 / ((m : ℚ) + 1) ^ 1 - (p : ℚ)⁻¹ * Hq 1 (m / p) -
            (Hq 1 (m % p) + 1 / ((m % p : ℕ) + 1 : ℚ) ^ 1)) =
          (p : ℚ)⁻¹ * (Hq 1 m - (p : ℚ)⁻¹ * Hq 1 (m / p) - Hq 1 (m % p)) +
            (-((m / p : ℕ) : ℚ)) * (1 / ((m + 1 : ℕ) : ℚ) ^ 1) * (1 / ((m % p + 1 : ℕ) : ℚ) ^ 1) := by
        have hA : ((m + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hB : ((m % p + 1 : ℕ) : ℚ) ≠ 0 := by positivity
        have hA' : ((m : ℚ) + 1) = ((m + 1 : ℕ) : ℚ) := by push_cast; ring
        have hB' : ((m % p : ℕ) + 1 : ℚ) = ((m % p + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [hA', hB']
        have hcast' : ((m + 1 : ℕ) : ℚ) = p * ((m / p : ℕ) : ℚ) + ((m % p + 1 : ℕ) : ℚ) := by
          rw [hA'.symm, hcast]; push_cast; ring
        field_simp
        rw [hcast']
        ring
      rw [key]
      refine (LocRing p).add_mem ih ((LocRing p).mul_mem ((LocRing p).mul_mem ((LocRing p).neg_mem (natq_mem _)) ?_) ?_)
      · simpa using hc1
      · simpa using hc2

/-- **L2S-02**: `H_k(j) - p^{-j} H_ℓ(j)` is `p`-integral. -/
theorem Hq_digit_lead (j k : ℕ) : Hq j k - ((p : ℚ) ^ j)⁻¹ * Hq j (k / p) ∈ LocRing p :=
  Hq_split j k

end HarmDigit

/-! ### Part 2: definitions -/

/-- `a` as an element of `MPT`. -/
def aT : MPT := MvPolynomial.X (Sum.inl 0)

/-- `u^a_ℓ = -3 H_ℓ(2)`. -/
def uaL (l : ℕ) : ℚ := -3 * Hq 2 l

/-- `v^a_ℓ = -3 (δ H_ℓ(2) + 2 H_ℓ(3))` at the node `k`, `ℓ = k / p`. -/
def vaL (n p k l : ℕ) : ℚ := -3 * (laiDelta n p k * Hq 2 l + 2 * Hq 3 l)

/-- `λ₀(s) = 3 H_{r₂+s-εp} + 2 H_{r₆-s+bp} - 5 H_s`. -/
def lam0 (n p s : ℕ) : ℚ :=
  3 * Hq 1 (r2 n p + s - eflag n p s * p) + 2 * Hq 1 (r6 n p + bflag n p s * p - s) - 5 * Hq 1 s

/-- `λ₀(s)` in `ZMod (p^2)`. -/
def lam0Z (n p s : ℕ) : ZMod (p ^ 2) :=
  3 * Hz p (r2 n p + s - eflag n p s * p) + 2 * Hz p (r6 n p + bflag n p s * p - s) - 5 * Hz p s

/-- `e₀(s) = -2 (q₆-b) H_{r₆-s+bp} + 3 (q₂+ε) H_{r₂+s-εp}` in `ZMod (p^2)`. -/
def e0Z (n p s : ℕ) : ZMod (p ^ 2) :=
  -2 * ((q6 n p - bflag n p s : ℕ) : ZMod (p ^ 2)) * Hz p (r6 n p + bflag n p s * p - s) +
    3 * ((q2 n p + eflag n p s : ℕ) : ZMod (p ^ 2)) * Hz p (r2 n p + s - eflag n p s * p)

/-- The integer lift `c̄_s` of `Cs(s) (1 + p e₀(s))`. -/
def cbarZ (n p s : ℕ) : ℤ :=
  ((Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * jetp p (e0Z n p s)).val : ℤ)

/-- Node data at `k ∈ K`, with the `p²` unit part. -/
def NodeData2 (p n : ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) : Prop :=
  1 ≤ k / p ∧ σ k = (sig n p (k % p) : ℤ) ∧ cl k = (clZ n p (k / p) (k % p) : ℚ) ∧
    τu (k / p) = (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * uL (k / p) ∧
    τv (k / p) = (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * vL n p k (k / p)

/-- Main term of `nd_k F` (Lemma J), `f0 = F(-k)`, `f1 = p F'(-k)`. -/
def ndJet (n p k u : ℕ) (f0 f1 : MPT) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) *
    (bT * (MvPolynomial.C (uL (k / p)) * f1 +
        MvPolynomial.C (vL n p k (k / p) - (p : ℚ) * lam0 n p (k % p) * uL (k / p)) * f0) +
      MvPolynomial.C (p : ℚ) * aT *
        (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0))

/-- Main term of `nodeT_k F` at a modified node (Lemma J, `T`-form). -/
def nodeJet (n p k : ℕ) (f0 f1 : MPT) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * (clZ n p (k / p) (k % p) : ℚ)) *
    (bT * (Tu (k / p) * f1 + Tv (k / p) * f0 -
        MvPolynomial.C ((p : ℚ) * (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) *
          lam0 n p (k % p) * uL (k / p)) * f0) +
      MvPolynomial.C (p : ℚ) * aT *
        MvPolynomial.C (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) *
        (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0))

/-- `𝓛ᵘ_{T-τ}(Φ) = ∑_{ℓ=1}^{L} (T^u_ℓ - τ^u_ℓ) Φ(-ℓ)`. -/
def locUtau (L : ℕ) (τu : ℕ → ℚ) (Φ : MPT[X]) : MPT :=
  ∑ l ∈ range L, (Tu (l + 1) - MvPolynomial.C (τu (l + 1))) *
    Φ.eval (MvPolynomial.C (-((l + 1 : ℕ) : ℚ)))

/-- `𝓛^a(Φ) = ∑_{ℓ=1}^{L} κ_ℓ [u^a_ℓ Φ'(-ℓ) + v^a_ℓ Φ(-ℓ)]`, nodes `k = s + ℓ p`. -/
def locAk (n p s L : ℕ) (kap : ℕ → ℚ) (Φ : MPT[X]) : MPT :=
  ∑ l ∈ range L, MvPolynomial.C (kap (l + 1)) *
    (MvPolynomial.C (uaL (l + 1)) * (Polynomial.derivative Φ).eval (MvPolynomial.C (-((l + 1 : ℕ) : ℚ))) +
      MvPolynomial.C (vaL n p (s + (l + 1) * p) (l + 1)) * Φ.eval (MvPolynomial.C (-((l + 1 : ℕ) : ℚ))))

/-- Main term of Lemma P: the right-hand side of `res_second`. -/
def resJet (n p s L μ : ℕ) (τu : ℕ → ℚ) (kap : ℕ → ℚ) (A R : MPT[X]) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 4) * (cbarZ n p s : ℚ)) *
    (bT * (R.eval (MvPolynomial.C (-(s : ℚ))) * linM (cLoc L) (A ^ 2) +
        MvPolynomial.C (p : ℚ) * ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) -
            MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ)))) *
          linM (cLoc L) (Polynomial.X * A ^ 2) +
        MvPolynomial.C (p : ℚ) * MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) *
          locUtau L τu (A ^ 2)) +
      MvPolynomial.C (p : ℚ) * aT * R.eval (MvPolynomial.C (-(s : ℚ))) *
        locAk n p s L kap (A ^ 2))

/-! ### Part 3: digits of the coefficient and of `λ₀` -/

section Digits

variable {p : ℕ} [hp : Fact p.Prime]

lemma lam0_args_lt (n s : ℕ) (hs : s < p) :
    r2 n p + s - eflag n p s * p < p ∧ r6 n p + bflag n p s * p - s < p := by
  have hpp := hp.out.pos
  have h2 : r2 n p < p := Nat.mod_lt _ hpp
  have h6 : r6 n p < p := Nat.mod_lt _ hpp
  unfold eflag bflag
  split_ifs <;> omega

lemma lam0_mem (n s : ℕ) (hs : s < p) : lam0 n p s ∈ LocRing p := by
  obtain ⟨h1, h2⟩ := lam0_args_lt (p := p) n s hs
  unfold lam0
  exact (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).mul_mem l3 (Hq_mem 1 _ h1))
    ((LocRing p).mul_mem l2 (Hq_mem 1 _ h2))) ((LocRing p).mul_mem l5 (Hq_mem 1 _ hs))

/-- **L2S-03** (Lemma H(iii)). -/
theorem laiH_digits (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) :
    (p : ℚ)⁻¹ * (laiH n k + (p : ℚ)⁻¹ * laiDelta n p k - lam0 n p (k % p)) ∈ LocRing p := by
  have hpp := hp.out.pos
  obtain ⟨hsd1, hsd2, hsd3⟩ := sub_div_mod p (6 * n) k hpp hk
  obtain ⟨had1, had2⟩ := add_div_mod p k (2 * n) hpp
  have hb : bflag n p (k % p) = if 6 * n % p < k % p then 1 else 0 := rfl
  have he : eflag n p (k % p) = if p - 2 * n % p ≤ k % p then 1 else 0 := rfl
  have d4 : (2 * n + k) % p = r2 n p + k % p - eflag n p (k % p) * p := by
    rw [add_comm, had2, he]; unfold r2; split_ifs with h1 h2 h2 <;> omega
  have d2 : (6 * n - k) % p = r6 n p + bflag n p (k % p) * p - k % p := by
    rw [hsd3, hb]; unfold r6; split_ifs with h1 <;> omega
  have e1 := harm_digit (p := p) h3 (2 * n + k)
  have e2 := harm_digit (p := p) h3 (6 * n - k)
  have e3 := harm_digit (p := p) h3 k
  rw [d4] at e1
  rw [d2] at e2
  have := (LocRing p).sub_mem ((LocRing p).add_mem ((LocRing p).mul_mem l3 e1) ((LocRing p).mul_mem l2 e2))
    ((LocRing p).mul_mem l5 e3)
  convert this using 1
  unfold laiH laiDelta lam0
  ring

lemma cast_val_p2 (x : ZMod (p ^ 2)) : (((x.val : ℕ) : ℤ) : ZMod (p ^ 2)) = x := by
  rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val x

/-- **L2S-04**: the unit part of `c_k` modulo `p²`, in terms of the integer lifts. -/
theorem laiCoef_kc_p2 {n : ℕ} (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (k : ℕ) (hk : k ≤ 6 * n) :
    ∃ u : ℕ, laiCoef n k = p ^ sig n p (k % p) * u ∧
      (u : ZMod (p ^ 2)) =
        (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ZMod (p ^ 2)) *
          (clZ n p (k / p) (k % p) : ZMod (p ^ 2)) := by
  obtain ⟨u, hu, hU⟩ := laiCoef_mod_p2 (p := p) h8 h3 k hk
  refine ⟨u, hu, ?_⟩
  unfold kapZ clZ
  rw [cast_val_p2, cast_val_p2, hU]
  ring

theorem cbarZ_cast (n s : ℕ) :
    (cbarZ n p s : ZMod (p ^ 2)) = Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * jetp p (e0Z n p s) := by
  unfold cbarZ; exact cast_val_p2 _

/-- `NodeData2` implies the mod `p` node data of `ContentBasisT` (extra lemma; `h8`, `h3`, `hk` added). -/
theorem NodeData2.toNodeData {n : ℕ} {σ : ℕ → ℤ} {cl τu τv : ℕ → ℚ} {k : ℕ} (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hd : NodeData2 p n σ cl τu τv k) : NodeData p n σ cl τu τv k := by
  obtain ⟨hl, hσ, hcl, hτu, hτv⟩ := hd
  obtain ⟨u, hu, hU⟩ := laiCoef_kc_p2 (p := p) h8 h3 k hk
  refine ⟨hl, hσ, u, clZ n p (k / p) (k % p), kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p),
    by exact_mod_cast hu, ?_, hcl, hτu, hτv⟩
  have h0 : (((u : ℤ) - clZ n p (k / p) (k % p) *
      kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℤ) : ZMod (p ^ 2)) = 0 := by
    push_cast; rw [hU]; ring
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 h0
  have h2 : ((p : ℤ)) ∣ (p : ℤ) ^ 2 := dvd_pow_self _ two_ne_zero
  exact h2.trans (by simpa using this)

/-- **L2S-05**: `cl_k ≡ c̄_s (1 + p ℓ λ₀(s))` in `ZMod (p²)`. -/
theorem clZ_split (n ℓ s : ℕ) (hℓ : ℓ + bflag n p s ≤ q6 n p) :
    (clZ n p ℓ s : ZMod (p ^ 2)) = (cbarZ n p s : ZMod (p ^ 2)) * jetp p ((ℓ : ZMod (p ^ 2)) * lam0Z n p s) := by
  rw [cbarZ_cast, mul_assoc, jetp_mul]
  unfold clZ
  rw [cast_val_p2]
  have h1 : ((q6 n p - ℓ - bflag n p s : ℕ) : ZMod (p ^ 2)) =
      ((q6 n p - bflag n p s : ℕ) : ZMod (p ^ 2)) - ℓ := by
    rw [show q6 n p - ℓ - bflag n p s = (q6 n p - bflag n p s) - ℓ by omega, Nat.cast_sub (by omega)]
  have h2 : ((q2 n p + ℓ + eflag n p s : ℕ) : ZMod (p ^ 2)) =
      ((q2 n p + eflag n p s : ℕ) : ZMod (p ^ 2)) + ℓ := by
    push_cast; ring
  unfold Es jetp e0Z lam0Z
  rw [h1, h2]
  ring

lemma redQ_lam0 (n s : ℕ) (hs : s < p) :
    redQ p (⟨lam0 n p s, lam0_mem n s hs⟩ : LocRing p) =
      ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) (lam0Z n p s) := by
  obtain ⟨h1, h2⟩ := lam0_args_lt (p := p) n s hs
  have e : (⟨lam0 n p s, lam0_mem n s hs⟩ : LocRing p) =
      3 * ⟨Hq 1 (r2 n p + s - eflag n p s * p), Hq_mem 1 _ h1⟩ +
        2 * ⟨Hq 1 (r6 n p + bflag n p s * p - s), Hq_mem 1 _ h2⟩ - 5 * ⟨Hq 1 s, Hq_mem 1 s hs⟩ :=
    Subtype.ext (by simp [lam0]; rfl)
  rw [e]
  simp only [map_sub, map_add, map_mul, map_ofNat, redQ_Hq _ h1, redQ_Hq _ h2, redQ_Hq _ hs]
  unfold lam0Z
  simp only [map_sub, map_add, map_mul, map_ofNat, Hz_cast _ h1, Hz_cast _ h2, Hz_cast _ hs]

/-- **L2S-05b**: the rational form of `clZ_split` (`cl_k ≡ c̄_s (1 + p ℓ λ₀(s))` modulo `p²`). -/
theorem clZ_split_Q (n ℓ s : ℕ) (hs : s < p) (h3 : 3 ≤ p) (hℓ : ℓ + bflag n p s ≤ q6 n p) :
    ((p : ℚ) ^ 2)⁻¹ * ((clZ n p ℓ s : ℚ) - (cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s)) ∈ LocRing p := by
  have hp0 := p_ne_zero' (p := p)
  set z : ℤ := ((lam0Z n p s).val : ℤ) with hz
  have hzc : (z : ZMod (p ^ 2)) = lam0Z n p s := cast_val_p2 _
  have h1 : ((p : ℤ) ^ 2) ∣ clZ n p ℓ s - cbarZ n p s * (1 + (p : ℤ) * ℓ * z) := by
    have h0 : (((clZ n p ℓ s - cbarZ n p s * (1 + (p : ℤ) * ℓ * z) : ℤ)) : ZMod (p ^ 2)) = 0 := by
      push_cast
      rw [clZ_split n ℓ s hℓ, hzc]
      unfold jetp; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 h0
    simpa using this
  obtain ⟨w, hw⟩ := h1
  have hX : redQ p (⟨lam0 n p s, lam0_mem n s hs⟩ - (z : LocRing p)) = 0 := by
    rw [map_sub, redQ_lam0 n s hs, ← hzc, map_intCast, map_intCast, sub_self]
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p _).1 hX
  have hyq : lam0 n p s - (z : ℚ) = (p : ℚ) * (y : ℚ) := by
    have := congrArg Subtype.val hy
    simpa using this
  have hwq : (clZ n p ℓ s : ℚ) - (cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * (z : ℚ)) = (p : ℚ) ^ 2 * (w : ℚ) := by
    exact_mod_cast hw
  have key : (clZ n p ℓ s : ℚ) - (cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s) =
      (p : ℚ) ^ 2 * ((w : ℚ) - (cbarZ n p s : ℚ) * ℓ * (y : ℚ)) := by
    linear_combination hwq - (cbarZ n p s : ℚ) * (p : ℚ) * ℓ * hyq
  rw [key, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hp0), one_mul]
  exact (LocRing p).sub_mem (by exact_mod_cast int_mem_locRing (ℓ := p) w)
    ((LocRing p).mul_mem ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (cbarZ n p s))
      (natq_mem ℓ)) y.2)

end Digits

/-! ### Part 4: jet valuations (L2S-06) -/

section Jet

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ν_k(F) ≥ e`: the jet valuation, `min (v F(-k)) (v pF'(-k)) ≥ e`. -/
def JetGE (p : ℕ) [Fact p.Prime] (k : ℕ) (e : ℤ) (F : MPT[X]) : Prop :=
  GV p e (evk k F) ∧ GV p e (MvPolynomial.C (p : ℚ) * devk k F)

theorem JetGE.mono {k : ℕ} {e e' : ℤ} {F : MPT[X]} (h : JetGE p k e F) (he : e' ≤ e) :
    JetGE p k e' F := ⟨h.1.mono he, h.2.mono he⟩

lemma evk_mul (k : ℕ) (F G : MPT[X]) : evk k (F * G) = evk k F * evk k G := by
  unfold evk; rw [Polynomial.eval_mul]

lemma devk_mul (k : ℕ) (F G : MPT[X]) :
    devk k (F * G) = devk k F * evk k G + evk k F * devk k G := by
  unfold devk evk
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]

theorem JetGE.mul {k : ℕ} {e e' : ℤ} {F G : MPT[X]} (hF : JetGE p k e F) (hG : JetGE p k e' G) :
    JetGE p k (e + e') (F * G) := by
  refine ⟨?_, ?_⟩
  · rw [evk_mul]; exact hF.1.mul hG.1
  · have : MvPolynomial.C (p : ℚ) * devk k (F * G) =
        (MvPolynomial.C (p : ℚ) * devk k F) * evk k G + evk k F * (MvPolynomial.C (p : ℚ) * devk k G) := by
      rw [devk_mul]; ring
    rw [this]
    exact (hF.2.mul hG.1).add (hF.1.mul hG.2)

lemma PInt_derivative {F : MPT[X]} (hF : PInt p F) : PInt p (Polynomial.derivative F) := by
  intro i
  rw [Polynomial.coeff_derivative]
  have hc : GV p 0 ((i : MPT) + 1) := by
    have : ((i : MPT) + 1) = MvPolynomial.C (((i + 1 : ℕ) : ℤ) : ℚ) := by push_cast; simp
    rw [this]; exact GV.const_int _
  simpa using (hF (i + 1)).mul hc

lemma GV_Cp_mul {e : ℤ} {f : MPT} (hf : GV p e f) : GV p (e + 1) (MvPolynomial.C (p : ℚ) * f) := by
  have hp0 := p_ne_zero' (p := p)
  refine GV.const_mul (e := 1) (e' := e) (x := (p : ℚ)) ?_ hf |>.mono (by omega)
  have : (p : ℚ) ^ (-(1 : ℤ)) * (p : ℚ) = 1 := by rw [zpow_neg_one]; field_simp
  rw [this]; exact (LocRing p).one_mem

theorem JetGE.of_pint {k : ℕ} {F : MPT[X]} (hF : PInt p F) : JetGE p k 0 F := by
  have hk : (-(k : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem k)
  refine ⟨GV_eval hF hk, ?_⟩
  have := GV_Cp_mul (GV_eval (PInt_derivative hF) hk)
  exact this.mono (by norm_num)

lemma JetGE_sX_aux (s l : ℕ) : JetGE p (s + l * p) 1 (sX s) := by
  have hp0 := p_ne_zero' (p := p)
  constructor
  · unfold evk
    rw [sX_eval_node, ← map_mul]
    apply GV.const
    have : (p : ℚ) ^ (-(1 : ℤ)) * ((p : ℚ) * (-(l : ℚ))) = -(l : ℚ) := by
      rw [zpow_neg_one]; field_simp
    rw [this]; exact (LocRing p).neg_mem (natq_mem l)
  · have hd : devk (s + l * p) (sX s) = 1 := by unfold devk sX; simp
    rw [hd, mul_one]
    apply GV.const
    have : (p : ℚ) ^ (-(1 : ℤ)) * (p : ℚ) = 1 := by rw [zpow_neg_one]; field_simp
    rw [this]; exact (LocRing p).one_mem

theorem JetGE.sX_self (k : ℕ) : JetGE p k 1 (sX (k % p)) := by
  have := JetGE_sX_aux (p := p) (k % p) (k / p)
  rwa [Nat.mod_add_div'] at this

theorem JetGE.shiftP (μ s l : ℕ) {A : MPT[X]} (hA : PInt p A) (hAd : A.natDegree ≤ μ) :
    JetGE p (s + l * p) μ (CatalanCore.Lai.shiftP p μ s A) := by
  have hp0 := p_ne_zero' (p := p)
  have hl : (-(l : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem l)
  have hc : GV p (μ : ℤ) (MvPolynomial.C ((p : ℚ) ^ μ) : MPT) := by
    apply GV.const
    rw [← zpow_natCast, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero]; exact (LocRing p).one_mem
  constructor
  · rw [show evk (s + l * p) (CatalanCore.Lai.shiftP p μ s A) = _ from shiftP_eval p μ s l A hAd]
    simpa using hc.mul (GV_eval hA hl)
  · rw [shiftP_deriv p μ s l A hAd]
    simpa using hc.mul (GV_eval (PInt_derivative hA) hl)

end Jet

/-! ### Part 5: Lemma J (L2S-07) and its variants (L2S-08, L2S-09) -/

section LemmaJ

variable {p : ℕ} [hp : Fact p.Prime]

/-- `X` as an element of `MPT`. -/
def xT : MPT := MvPolynomial.X (Sum.inl 2)

lemma ren_X (i : Fin 3) : ren (MvPolynomial.X i : MP) = (MvPolynomial.X (Sum.inl i) : MPT) := by
  unfold ren; simp

lemma ren_laiU (k : ℕ) :
    ren (laiU k) = MvPolynomial.C (-3 * Hq 2 k) * aT + MvPolynomial.C (-2 * Hq 3 k) * bT := by
  unfold laiU aT bT
  simp only [map_add, map_mul, ren_C, ren_X]

lemma ren_laiV (n k : ℕ) :
    ren (laiV n k) = MvPolynomial.C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * aT +
      MvPolynomial.C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * bT + MvPolynomial.C 6 * xT := by
  unfold laiV aT bT xT
  simp only [map_add, map_mul, map_sub, ren_C, ren_X, map_ofNat]
  ring

/-- Product of a constant of valuation `e₀`, a generator and an element of valuation `e`. -/
lemma GV_term {e₀ e : ℤ} (x : ℚ) (hx : (p : ℚ) ^ (-e₀) * x ∈ LocRing p) {v f : MPT}
    (hv : GV p 0 v) (hf : GV p e f) : GV p (e₀ + e) (MvPolynomial.C x * (v * f)) := by
  have := GV.const_mul hx (hv.mul hf)
  simpa using this

/-- the coefficient bound `p^{σ-4} u · p³ m = p^{σ-1} (u m)`. -/
lemma coef_loc (σ' : ℤ) (u m c w : ℚ) (hc : c = (p : ℚ) ^ (σ' - 4) * u) (hw : w = (p : ℚ) ^ 3 * m)
    (hu : u ∈ LocRing p) (hm : m ∈ LocRing p) : (p : ℚ) ^ (-(σ' - 1)) * (c * w) ∈ LocRing p := by
  have hp0 := p_ne_zero' (p := p)
  have h1 : (p : ℚ) ^ (-(σ' - 1)) * (p : ℚ) ^ (σ' - 4) * (p : ℚ) ^ 3 = 1 := by
    rw [← zpow_add₀ hp0, show (p : ℚ) ^ 3 = (p : ℚ) ^ ((3 : ℕ) : ℤ) by rw [zpow_natCast], ← zpow_add₀ hp0]
    have : -(σ' - 1) + (σ' - 4) + ((3 : ℕ) : ℤ) = 0 := by push_cast; ring
    rw [this, zpow_zero]
  have : (p : ℚ) ^ (-(σ' - 1)) * (c * w) = u * m := by
    rw [hc, hw]
    calc (p : ℚ) ^ (-(σ' - 1)) * ((p : ℚ) ^ (σ' - 4) * u * ((p : ℚ) ^ 3 * m))
        = ((p : ℚ) ^ (-(σ' - 1)) * (p : ℚ) ^ (σ' - 4) * (p : ℚ) ^ 3) * (u * m) := by ring
      _ = u * m := by rw [h1, one_mul]
  rw [this]; exact (LocRing p).mul_mem hu hm

/-- The pure field identities behind Lemma J. -/
lemma nd_coeffs {q δ lam E h2 h3 h4 I2 I3 I4 H Hk2 Hk3 Hk4 : ℚ} (hq : q ≠ 0)
    (eH : H = -(q⁻¹ * δ) + lam + q * E) (e2 : Hk2 = (q ^ 2)⁻¹ * h2 + I2)
    (e3 : Hk3 = (q ^ 3)⁻¹ * h3 + I3) (e4 : Hk4 = (q ^ 4)⁻¹ * h4 + I4) :
    q ^ 4 * (-3 * Hk2) - q ^ 2 * (-3 * h2) = q ^ 3 * (-3 * q * I2) ∧
    q ^ 4 * (-2 * Hk3) - q * (-2 * h3) = q ^ 3 * (-2 * q * I3) ∧
    q ^ 5 * (3 * H * Hk2 - 6 * Hk3) - q ^ 2 * (-3 * (δ * h2 + 2 * h3)) =
      q ^ 3 * (3 * (-(q * δ * I2) + lam * h2 + q ^ 2 * lam * I2 + q * E * h2 + q ^ 3 * E * I2) -
        6 * q ^ 2 * I3) ∧
    q ^ 5 * (2 * H * Hk3 - 6 * Hk4) - q * (-2 * (h3 * δ + 3 * h4) - q * lam * (-2 * h3)) =
      q ^ 3 * (2 * (-(q * δ * I3) + q ^ 2 * lam * I3 + E * h3 + q ^ 3 * E * I3) - 6 * q ^ 2 * I4) := by
  subst eH e2 e3 e4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (field_simp; ring)

/-- **L2S-07, Lemma J (node jet lemma).** -/
theorem nd_jet (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (u : ℕ) (hu : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u)
    (F : MPT[X]) (e : ℤ) (hF : JetGE p k e F) :
    GV p ((sig n p (k % p) : ℤ) - 2 + e)
      (ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hsp : k % p < p := Nat.mod_lt _ hpp
  have hδ : laiDelta n p k ∈ LocRing p := delta_mem n k h8 hk
  have hlam := lam0_mem (p := p) n (k % p) hsp
  obtain ⟨E, hE, eH⟩ : ∃ E ∈ LocRing p,
      laiH n k = -((p : ℚ)⁻¹ * laiDelta n p k) + lam0 n p (k % p) + p * E :=
    ⟨(p : ℚ)⁻¹ * (laiH n k + (p : ℚ)⁻¹ * laiDelta n p k - lam0 n p (k % p)),
      laiH_digits n k h8 h3 hk, by field_simp; ring⟩
  obtain ⟨I2, hI2, e2⟩ : ∃ I ∈ LocRing p, Hq 2 k = ((p : ℚ) ^ 2)⁻¹ * Hq 2 (k / p) + I :=
    ⟨_, Hq_digit_lead 2 k, by ring⟩
  obtain ⟨I3, hI3, e3⟩ : ∃ I ∈ LocRing p, Hq 3 k = ((p : ℚ) ^ 3)⁻¹ * Hq 3 (k / p) + I :=
    ⟨_, Hq_digit_lead 3 k, by ring⟩
  obtain ⟨I4, hI4, e4⟩ : ∃ I ∈ LocRing p, Hq 4 k = ((p : ℚ) ^ 4)⁻¹ * Hq 4 (k / p) + I :=
    ⟨_, Hq_digit_lead 4 k, by ring⟩
  have hh2 := Hq_mem (p := p) 2 (k / p) hkp
  have hh3 := Hq_mem (p := p) 3 (k / p) hkp
  have hh4 := Hq_mem (p := p) 4 (k / p) hkp
  obtain ⟨c1, c2, c3, c4⟩ := nd_coeffs (q := (p : ℚ)) (δ := laiDelta n p k) (lam := lam0 n p (k % p))
    (E := E) (h2 := Hq 2 (k / p)) (h3 := Hq 3 (k / p)) (h4 := Hq 4 (k / p)) (I2 := I2) (I3 := I3)
    (I4 := I4) (H := laiH n k) (Hk2 := Hq 2 k) (Hk3 := Hq 3 k) (Hk4 := Hq 4 k) hp0 eH e2 e3 e4
  -- the p-integral multipliers
  obtain ⟨m1, hm1, hm1e⟩ : ∃ m ∈ LocRing p, m = -3 * (p : ℚ) * I2 :=
    ⟨-3 * (p : ℚ) * I2, (LocRing p).mul_mem ((LocRing p).mul_mem lm3 lp) hI2, rfl⟩
  obtain ⟨m2, hm2, hm2e⟩ : ∃ m ∈ LocRing p, m = -2 * (p : ℚ) * I3 :=
    ⟨-2 * (p : ℚ) * I3, (LocRing p).mul_mem ((LocRing p).mul_mem lm2 lp) hI3, rfl⟩
  obtain ⟨m3, hm3, hm3e⟩ : ∃ m ∈ LocRing p, m = 3 * (-((p : ℚ) * laiDelta n p k * I2) +
      lam0 n p (k % p) * Hq 2 (k / p) + (p : ℚ) ^ 2 * lam0 n p (k % p) * I2 + (p : ℚ) * E * Hq 2 (k / p) +
      (p : ℚ) ^ 3 * E * I2) - 6 * (p : ℚ) ^ 2 * I3 := by
    refine ⟨3 * (-((p : ℚ) * laiDelta n p k * I2) + lam0 n p (k % p) * Hq 2 (k / p) +
      (p : ℚ) ^ 2 * lam0 n p (k % p) * I2 + (p : ℚ) * E * Hq 2 (k / p) + (p : ℚ) ^ 3 * E * I2) -
      6 * (p : ℚ) ^ 2 * I3, ?_, rfl⟩
    have hp1 := lp (p := p)
    have hp2 := natPow_mem (p := p) 2
    have hp3 := natPow_mem (p := p) 3
    refine (LocRing p).sub_mem ((LocRing p).mul_mem l3 ?_) ((LocRing p).mul_mem
      ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) hp2) hI3)
    refine (LocRing p).add_mem ((LocRing p).add_mem ((LocRing p).add_mem ((LocRing p).add_mem ?_
      ((LocRing p).mul_mem hlam hh2)) ((LocRing p).mul_mem ((LocRing p).mul_mem hp2 hlam) hI2))
      ((LocRing p).mul_mem ((LocRing p).mul_mem hp1 hE) hh2))
      ((LocRing p).mul_mem ((LocRing p).mul_mem hp3 hE) hI2)
    exact (LocRing p).neg_mem ((LocRing p).mul_mem ((LocRing p).mul_mem hp1 hδ) hI2)
  obtain ⟨m4, hm4, hm4e⟩ : ∃ m ∈ LocRing p, m = 2 * (-((p : ℚ) * laiDelta n p k * I3) +
      (p : ℚ) ^ 2 * lam0 n p (k % p) * I3 + E * Hq 3 (k / p) + (p : ℚ) ^ 3 * E * I3) -
      6 * (p : ℚ) ^ 2 * I4 := by
    refine ⟨2 * (-((p : ℚ) * laiDelta n p k * I3) + (p : ℚ) ^ 2 * lam0 n p (k % p) * I3 +
      E * Hq 3 (k / p) + (p : ℚ) ^ 3 * E * I3) - 6 * (p : ℚ) ^ 2 * I4, ?_, rfl⟩
    have hp1 := lp (p := p)
    have hp2 := natPow_mem (p := p) 2
    have hp3 := natPow_mem (p := p) 3
    refine (LocRing p).sub_mem ((LocRing p).mul_mem l2 ?_) ((LocRing p).mul_mem
      ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) hp2) hI4)
    refine (LocRing p).add_mem ((LocRing p).add_mem ((LocRing p).add_mem ?_
      ((LocRing p).mul_mem ((LocRing p).mul_mem hp2 hlam) hI3)) ((LocRing p).mul_mem hE hh3))
      ((LocRing p).mul_mem ((LocRing p).mul_mem hp3 hE) hI3)
    exact (LocRing p).neg_mem ((LocRing p).mul_mem ((LocRing p).mul_mem hp1 hδ) hI3)
  obtain ⟨m5, hm5, hm5e⟩ : ∃ m ∈ LocRing p, m = 6 * (p : ℚ) ^ 2 :=
    ⟨6 * (p : ℚ) ^ 2, (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6)
      (natPow_mem (p := p) 2), rfl⟩
  -- exact power bookkeeping
  have hc0 : (laiCoef n k : ℚ) = ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * (p : ℚ) ^ 4 := by
    rw [hu, mul_assoc, mul_comm (u : ℚ), ← mul_assoc]
    congr 1
    rw [← zpow_natCast (p : ℚ) 4, ← zpow_add₀ hp0, ← zpow_natCast (p : ℚ) (sig n p (k % p))]
    congr 1; push_cast; ring
  have hu0 : (u : ℚ) ∈ LocRing p := natq_mem u
  -- the key identity (all constants are pushed through `C`)
  have key : MvPolynomial.C (p : ℚ) *
      (ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) =
      MvPolynomial.C (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m1)) *
          (aT * (MvPolynomial.C (p : ℚ) * devk k F)) +
        MvPolynomial.C (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m2)) *
          (bT * (MvPolynomial.C (p : ℚ) * devk k F)) +
        MvPolynomial.C (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m3)) *
          (aT * evk k F) +
        MvPolynomial.C (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m4)) *
          (bT * evk k F) +
        MvPolynomial.C (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m5)) *
          (xT * evk k F) := by
    rw [hm1e, hm2e, hm3e, hm4e, hm5e, ← c1, ← c2, ← c3, ← c4]
    unfold ndT ndJet uaL vaL uL vL
    rw [ren_C, ren_laiU, ren_laiV, hc0]
    simp only [map_mul, map_add, map_sub, map_pow, map_neg, map_ofNat]
    ring
  have hD : GV p ((sig n p (k % p) : ℤ) - 1 + e)
      (MvPolynomial.C (p : ℚ) *
        (ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F))) := by
    rw [key]
    have ha : GV p 0 aT := GV.var _
    have hb : GV p 0 bT := GV.var _
    have hx : GV p 0 xT := GV.var _
    have hf0 := hF.1
    have hf1 := hF.2
    have cl : ∀ m : ℚ, m ∈ LocRing p → ((p : ℚ) ^ (-((sig n p (k % p) : ℤ) - 1)) *
        (((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * u) * ((p : ℚ) ^ 3 * m)) ∈ LocRing p) :=
      fun m hm => coef_loc _ u m _ _ rfl rfl hu0 hm
    exact ((((GV_term _ (cl m1 hm1) ha hf1).add (GV_term _ (cl m2 hm2) hb hf1)).add
      (GV_term _ (cl m3 hm3) ha hf0)).add (GV_term _ (cl m4 hm4) hb hf0)).add
      (GV_term _ (cl m5 hm5) hx hf0)
  have hinv : (MvPolynomial.C ((p : ℚ)⁻¹) : MPT) * (MvPolynomial.C (p : ℚ) *
      (ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F))) =
      ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, one_mul]
  have := GV.const_mul (e := -1) (x := (p : ℚ)⁻¹) (by
    simp [mul_inv_cancel₀ hp0, (LocRing p).one_mem]) hD
  rw [hinv] at this
  exact this.mono (le_of_eq (by ring))

lemma GV_C_eq {σ : Type*} {e : ℤ} {x y : ℚ} (hx : x = (p : ℚ) ^ e * y) (hy : y ∈ LocRing p) :
    GV p e (MvPolynomial.C x : MvPolynomial σ ℚ) := by
  apply GV.const
  rw [hx, ← mul_assoc, ← zpow_add₀ (p_ne_zero' (p := p)), neg_add_cancel, zpow_zero, one_mul]
  exact hy

lemma GV_Cmul {e : ℤ} {x : ℚ} (hx : x ∈ LocRing p) {f : MPT} (hf : GV p e f) :
    GV p e (MvPolynomial.C x * f) := by
  have := GV.const_mul (e := 0) (e' := e) (x := x) (by simpa using hx) hf
  simpa using this

lemma GV_Cinv_mul {e : ℤ} {f : MPT} (hf : GV p e f) :
    GV p (e - 1) (MvPolynomial.C ((p : ℚ)⁻¹) * f) := by
  have hp0 := p_ne_zero' (p := p)
  have := GV.const_mul (e := -1) (e' := e) (x := (p : ℚ)⁻¹) (by
    simp [mul_inv_cancel₀ hp0, (LocRing p).one_mem]) hf
  exact this.mono (le_of_eq (by ring))

/-- The bracket of the jet main terms is of valuation `≥ e` when `(f0, f1)` is. -/
lemma GV_bracket (n k : ℕ) (h8 : 8 * n < p ^ 2) (hk : k ≤ 6 * n) (hkp : k / p < p) (hsp : k % p < p)
    {e : ℤ} {f0 f1 : MPT} (hf0 : GV p e f0) (hf1 : GV p e f1) :
    GV p e (bT * (MvPolynomial.C (uL (k / p)) * f1 +
        MvPolynomial.C (vL n p k (k / p) - (p : ℚ) * lam0 n p (k % p) * uL (k / p)) * f0) +
      MvPolynomial.C (p : ℚ) * aT *
        (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0)) := by
  have huL := uL_mem (p := p) _ hkp
  have hvL := vL_mem (p := p) n k _ h8 hk hkp
  have hlam := lam0_mem (p := p) n (k % p) hsp
  have hh2 := Hq_mem (p := p) 2 (k / p) hkp
  have hh3 := Hq_mem (p := p) 3 (k / p) hkp
  have hδ := delta_mem (p := p) n k h8 hk
  have hb : GV p 0 bT := GV.var _
  have ha : GV p 0 aT := GV.var _
  have hpa : GV p 0 (MvPolynomial.C (p : ℚ) * aT : MPT) := by simpa using GV_Cmul (lp (p := p)) ha
  have h1 := (GV_Cmul huL hf1).add (GV_Cmul ((LocRing p).sub_mem hvL ((LocRing p).mul_mem
    ((LocRing p).mul_mem lp hlam) huL)) hf0)
  have h2 : GV p e (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0) := by
    refine (GV_Cmul ?_ hf1).add (GV_Cmul ?_ hf0)
    · unfold uaL; exact (LocRing p).mul_mem lm3 hh2
    · unfold vaL
      exact (LocRing p).mul_mem lm3 ((LocRing p).add_mem ((LocRing p).mul_mem hδ hh2)
        ((LocRing p).mul_mem l2 hh3))
  have := (hb.mul h1).add (hpa.mul h2)
  simpa using this

/-- **L2S-08**: Lemma J for the modified nodes `k ∈ K`. -/
theorem nodeT_jet (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (k : ℕ) (hk : k ≤ 6 * n) (hkK : k ∈ K) (hd : NodeData2 p n σ cl τu τv k)
    (F : MPT[X]) (e : ℤ) (hF : JetGE p k e F) :
    GV p ((sig n p (k % p) : ℤ) - 2 + e)
      (nodeT (p := p) n K σ cl τu τv k F -
        nodeJet n p k (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  obtain ⟨hl, hσ, hcl, hτu, hτv⟩ := hd
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hsp : k % p < p := Nat.mod_lt _ hpp
  obtain ⟨u, hu, hU⟩ := laiCoef_kc_p2 (p := p) h8 h3 k hk
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u := by exact_mod_cast hu
  have h1 := nd_jet n k h8 h3 hk hl u hu' F e hF
  obtain ⟨w, hw⟩ : ((p : ℤ) ^ 2) ∣ (u : ℤ) - kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) *
      clZ n p (k / p) (k % p) := by
    have h0 : (((u : ℤ) - kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) *
        clZ n p (k / p) (k % p) : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast; rw [hU]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 h0
    simpa using this
  have hwq : (u : ℚ) - (kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) *
      (clZ n p (k / p) (k % p) : ℚ) = (p : ℚ) ^ 2 * (w : ℚ) := by exact_mod_cast hw
  have hnode : nodeT (p := p) n K σ cl τu τv k F = ndT n k F +
      modNdT p (sig n p (k % p) : ℤ) (clZ n p (k / p) (k % p) : ℚ)
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * uL (k / p))
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * vL n p k (k / p))
        (k / p) k F := by
    unfold nodeT; rw [if_pos hkK, hσ, hcl, hτu, hτv]
  have hz3 : (p : ℚ) ^ ((sig n p (k % p) : ℤ) - 3) = (p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * p := by
    rw [show ((sig n p (k % p) : ℤ) - 3) = ((sig n p (k % p) : ℤ) - 4) + 1 by ring, zpow_add₀ hp0, zpow_one]
  have hz2 : (p : ℚ) ^ ((sig n p (k % p) : ℤ) - 4) * ((p : ℚ) ^ 2 * (w : ℚ)) =
      (p : ℚ) ^ ((sig n p (k % p) : ℤ) - 2) * (w : ℚ) := by
    rw [← mul_assoc, show (p : ℚ) ^ 2 = (p : ℚ) ^ ((2 : ℕ) : ℤ) by rw [zpow_natCast], ← zpow_add₀ hp0]
    congr 2; push_cast; ring
  have hid : ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) +
      modNdT p (sig n p (k % p) : ℤ) (clZ n p (k / p) (k % p) : ℚ)
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * uL (k / p))
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * vL n p k (k / p))
        (k / p) k F -
      nodeJet n p k (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) =
      MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 2) * (w : ℚ)) *
        (bT * (MvPolynomial.C (uL (k / p)) * (MvPolynomial.C (p : ℚ) * devk k F) +
            MvPolynomial.C (vL n p k (k / p) - (p : ℚ) * lam0 n p (k % p) * uL (k / p)) * evk k F) +
          MvPolynomial.C (p : ℚ) * aT * (MvPolynomial.C (uaL (k / p)) * (MvPolynomial.C (p : ℚ) * devk k F) +
            MvPolynomial.C (vaL n p k (k / p)) * evk k F)) := by
    rw [← hz2, ← hwq]
    unfold ndJet modNdT nodeJet
    rw [hz3]
    simp only [map_mul, map_add, map_sub, map_pow, map_natCast]
    ring
  have h2 : GV p ((sig n p (k % p) : ℤ) - 2 + e)
      (MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 2) * (w : ℚ)) *
        (bT * (MvPolynomial.C (uL (k / p)) * (MvPolynomial.C (p : ℚ) * devk k F) +
            MvPolynomial.C (vL n p k (k / p) - (p : ℚ) * lam0 n p (k % p) * uL (k / p)) * evk k F) +
          MvPolynomial.C (p : ℚ) * aT * (MvPolynomial.C (uaL (k / p)) * (MvPolynomial.C (p : ℚ) * devk k F) +
            MvPolynomial.C (vaL n p k (k / p)) * evk k F))) := by
    have hc : GV p ((sig n p (k % p) : ℤ) - 2)
        (MvPolynomial.C ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 2) * (w : ℚ)) : MPT) := by
      apply GV.const
      have : (p : ℚ) ^ (-((sig n p (k % p) : ℤ) - 2)) * ((p : ℚ) ^ ((sig n p (k % p) : ℤ) - 2) * (w : ℚ)) =
          (w : ℚ) := by
        rw [← mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]
      rw [this]; exact_mod_cast int_mem_locRing (ℓ := p) w
    exact hc.mul (GV_bracket n k h8 hk hkp hsp hF.1 hF.2)
  have hgoal : nodeT (p := p) n K σ cl τu τv k F -
        nodeJet n p k (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) =
      (ndT n k F - ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) +
      (ndJet n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) +
        modNdT p (sig n p (k % p) : ℤ) (clZ n p (k / p) (k % p) : ℚ)
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * uL (k / p))
        ((kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) : ℚ) * vL n p k (k / p))
        (k / p) k F -
      nodeJet n p k (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) := by
    rw [hnode]; ring
  rw [hgoal, hid]
  exact h1.add h2

/-- **L2S-09**: the `ℓ = 0` node. (`h3` added to the posted statement: it is needed for `c_k = p^σ u`.) -/
theorem nd0_jet (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hkp : k < p)
    (F : MPT[X]) (e : ℤ) (hF : JetGE p k e F) :
    GV p ((sig n p k : ℤ) - 1 + e) (ndT n k F) := by
  have hp0 := p_ne_zero' (p := p)
  obtain ⟨u, hu, -, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  have hmod : k % p = k := Nat.mod_eq_of_lt hkp
  rw [hmod] at hu
  have hu' : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p k) * u := by exact_mod_cast hu
  have hc : GV p (sig n p k : ℤ) (MvPolynomial.C (laiCoef n k : ℚ) : MPT) :=
    GV_C_eq (by rw [hu', zpow_natCast]) (natq_mem u)
  have hU := GV_ren (laiU_zero (p := p) k hkp)
  have hV := GV_ren (laiV_zero (p := p) n k h8 hk hkp)
  have hd : GV p (-1 + e) (devk k F) := by
    have h := GV_Cinv_mul hF.2
    have : (MvPolynomial.C ((p : ℚ)⁻¹) : MPT) * (MvPolynomial.C (p : ℚ) * devk k F) = devk k F := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, one_mul]
    rw [this] at h
    exact h.mono (le_of_eq (by ring))
  have hVe : GV p (0 + (-1 + e)) (ren (laiV n k) * evk k F) := by simpa using hV.mul hF.1
  unfold ndT
  rw [ren_C]
  have := hc.mul ((hU.mul hd).add hVe)
  exact this.mono (by omega)

end LemmaJ

/-! ### Part 6: the Taylor step (L2S-10) -/

section Taylor

variable {p : ℕ} [hp : Fact p.Prime]

lemma pow_taylor (x h : MPT) (hx : GV p 0 x) (hh : GV p 1 h) (i : ℕ) :
    GV p 2 ((x + h) ^ i - x ^ i - (i : MPT) * x ^ (i - 1) * h) := by
  have hxh : GV p 0 (x + h) := hx.add (hh.mono (by norm_num))
  cases i with
  | zero => simpa using GV.zero (p := p) (σ := TVar) 2
  | succ j =>
    induction j with
    | zero => simpa using GV.zero (p := p) (σ := TVar) 2
    | succ j ih =>
      have e : (x + h) ^ (j + 1 + 1) - x ^ (j + 1 + 1) - ((j + 1 + 1 : ℕ) : MPT) * x ^ (j + 1 + 1 - 1) * h =
          (x + h) * ((x + h) ^ (j + 1) - x ^ (j + 1) - ((j + 1 : ℕ) : MPT) * x ^ (j + 1 - 1) * h) +
            ((j + 1 : ℕ) : MPT) * x ^ j * h ^ 2 := by
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
      rw [e]
      have hn : GV p 0 (((j + 1 : ℕ) : MPT)) := by
        have : (((j + 1 : ℕ) : MPT)) = MvPolynomial.C (((j + 1 : ℕ) : ℤ) : ℚ) := by push_cast; simp
        rw [this]; exact GV.const_int _
      have h2 : GV p 2 (h ^ 2) := by simpa using hh.pow 2
      have := (hxh.mul ih).add ((hn.mul (hx.pow j)).mul h2)
      simpa using this

lemma pow_diff (x h : MPT) (hx : GV p 0 x) (hh : GV p 1 h) (i : ℕ) :
    GV p 1 ((x + h) ^ i - x ^ i) := by
  have hn : GV p 0 (i : MPT) := by
    have : ((i : MPT)) = MvPolynomial.C ((i : ℤ) : ℚ) := by simp
    rw [this]; exact GV.const_int _
  have h1 := (hn.mul (hx.pow (i - 1))).mul hh
  have h2 := (pow_taylor x h hx hh i).mono (show (1 : ℤ) ≤ 2 by norm_num)
  have := h2.add (by simpa using h1)
  convert this using 1; ring

/-- **L2S-10** (Taylor step modulo `p²`). -/
theorem taylor_p2 {R : MPT[X]} (hR : PInt p R) (s l : ℕ) :
    GV p 2 (evk (s + l * p) R - (R.eval (MvPolynomial.C (-(s : ℚ))) -
        MvPolynomial.C ((l : ℚ) * p) * (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))))) ∧
    GV p 1 (devk (s + l * p) R - (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) := by
  have hx : GV p 0 (MvPolynomial.C (-(s : ℚ)) : MPT) := GV.const_loc ((LocRing p).neg_mem (natq_mem s))
  have hh : GV p 1 (MvPolynomial.C (-((l : ℚ) * p)) : MPT) := by
    apply GV.const
    have hp0 := p_ne_zero' (p := p)
    have : (p : ℚ) ^ (-(1 : ℤ)) * (-((l : ℚ) * p)) = -(l : ℚ) := by rw [zpow_neg_one]; field_simp
    rw [this]; exact (LocRing p).neg_mem (natq_mem l)
  have hxh : (MvPolynomial.C (-((s + l * p : ℕ) : ℚ)) : MPT) =
      MvPolynomial.C (-(s : ℚ)) + MvPolynomial.C (-((l : ℚ) * p)) := by
    rw [← map_add]; congr 1; push_cast; ring
  set x : MPT := MvPolynomial.C (-(s : ℚ)) with hxdef
  set h : MPT := MvPolynomial.C (-((l : ℚ) * p)) with hhdef
  have hCl : (MvPolynomial.C ((l : ℚ) * p) : MPT) = -h := by rw [hhdef, map_neg, neg_neg]
  constructor
  · have e : evk (s + l * p) R - (R.eval x - MvPolynomial.C ((l : ℚ) * p) * (Polynomial.derivative R).eval x) =
        ∑ i ∈ range (R.natDegree + 1), R.coeff i * ((x + h) ^ i - x ^ i - (i : MPT) * x ^ (i - 1) * h) := by
      unfold evk
      rw [hxh, hCl, Polynomial.eval_eq_sum_range (x := x + h), Polynomial.eval_eq_sum_range (x := x),
        eval_derivative_range R R.natDegree le_rfl x]
      have hS : -h * ∑ j ∈ range (R.natDegree + 1), R.coeff j * (j : MPT) * x ^ (j - 1) =
          -∑ i ∈ range (R.natDegree + 1), R.coeff i * ((i : MPT) * x ^ (i - 1) * h) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hS]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    rw [e]
    exact GV.sum fun i _ => by simpa using (hR i).mul (pow_taylor x h hx hh i)
  · have e : devk (s + l * p) R - (Polynomial.derivative R).eval x =
        ∑ i ∈ range (R.natDegree + 1), (Polynomial.derivative R).coeff i * ((x + h) ^ i - x ^ i) := by
      unfold devk
      rw [hxh, Polynomial.eval_eq_sum_range' (n := R.natDegree + 1)
          (Nat.lt_succ_of_le ((Polynomial.natDegree_derivative_le R).trans (Nat.sub_le _ _))) (x + h),
        Polynomial.eval_eq_sum_range' (n := R.natDegree + 1)
          (Nat.lt_succ_of_le ((Polynomial.natDegree_derivative_le R).trans (Nat.sub_le _ _))) x]
      simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e]
    exact GV.sum fun i _ => by simpa using (PInt_derivative hR i).mul (pow_diff x h hx hh i)

end Taylor

/-! ### Part 7: Lemma P (L2S-11) -/

section ResSecond

variable {p : ℕ} [hp : Fact p.Prime]

/-- The difference `LHS - RHS` of the per-node congruence of Lemma P, over any commutative ring. -/
def nodeAlg {S : Type*} [CommRing S] (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va : S) : S :=
  (cb + pi * cb * l * lam + pi ^ 2 * ce) *
    (b * (Tu * (2 * a0 * a1 * (R0 - pi * l * R1 + pi ^ 2 * t2) + pi * (a0 ^ 2 * (R1 + pi * t1))) +
        Tv * (a0 ^ 2 * (R0 - pi * l * R1 + pi ^ 2 * t2)) -
        pi * kap * lam * uL * (a0 ^ 2 * (R0 - pi * l * R1 + pi ^ 2 * t2))) +
      pi * a * kap * (ua * (2 * a0 * a1 * (R0 - pi * l * R1 + pi ^ 2 * t2) + pi * (a0 ^ 2 * (R1 + pi * t1))) +
        va * (a0 ^ 2 * (R0 - pi * l * R1 + pi ^ 2 * t2)))) -
  cb * (b * (R0 * (Tu * (2 * a0 * a1) + Tv * a0 ^ 2) +
        pi * (l * (lam * R0 - R1) * (Tu * (2 * a0 * a1) + Tv * a0 ^ 2) + R1 * Tu * a0 ^ 2 -
          lam * kap * uL * a0 ^ 2 * R0)) +
      pi * a * R0 * kap * (ua * (2 * a0 * a1) + va * a0 ^ 2))

lemma nodeAlg_eq {S : Type*} [CommRing S] (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va : S) :
    nodeAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va = pi ^ 2 * ((-2) * a * a0 * a1 * cb * l * R1 * kap * ua + (2) * a * a0 * a1 * cb * l * lam * R0 * kap * ua + a * a0^2 * cb * R1 * kap * ua + (-1) * a * a0^2 * cb * l * R1 * kap * va + a * a0^2 * cb * l * lam * R0 * kap * va + b * a0^2 * cb * l * lam * R1 * kap * uL + (-1) * b * a0^2 * cb * l * lam^2 * R0 * kap * uL + b * Tv * a0^2 * R0 * ce + b * Tv * a0^2 * cb * t2 + (-1) * b * Tv * a0^2 * cb * l^2 * lam * R1 + (2) * b * Tu * a0 * a1 * R0 * ce + (2) * b * Tu * a0 * a1 * cb * t2 + (-2) * b * Tu * a0 * a1 * cb * l^2 * lam * R1 + b * Tu * a0^2 * cb * t1 + b * Tu * a0^2 * cb * l * lam * R1 + pi^1 * ((2) * a * a0 * a1 * R0 * ce * kap * ua + (2) * a * a0 * a1 * cb * t2 * kap * ua + (-2) * a * a0 * a1 * cb * l^2 * lam * R1 * kap * ua + a * a0^2 * R0 * ce * kap * va + a * a0^2 * cb * t1 * kap * ua + a * a0^2 * cb * t2 * kap * va + a * a0^2 * cb * l * lam * R1 * kap * ua + (-1) * a * a0^2 * cb * l^2 * lam * R1 * kap * va + (-1) * b * a0^2 * lam * R0 * ce * kap * uL + (-1) * b * a0^2 * cb * lam * t2 * kap * uL + b * a0^2 * cb * l^2 * lam^2 * R1 * kap * uL + (-1) * b * Tv * a0^2 * l * R1 * ce + b * Tv * a0^2 * cb * l * lam * t2 + (-2) * b * Tu * a0 * a1 * l * R1 * ce + (2) * b * Tu * a0 * a1 * cb * l * lam * t2 + b * Tu * a0^2 * R1 * ce + b * Tu * a0^2 * cb * l * lam * t1) + pi^2 * ((-2) * a * a0 * a1 * l * R1 * ce * kap * ua + (2) * a * a0 * a1 * cb * l * lam * t2 * kap * ua + a * a0^2 * R1 * ce * kap * ua + (-1) * a * a0^2 * l * R1 * ce * kap * va + a * a0^2 * cb * l * lam * t1 * kap * ua + a * a0^2 * cb * l * lam * t2 * kap * va + b * a0^2 * l * lam * R1 * ce * kap * uL + (-1) * b * a0^2 * cb * l * lam^2 * t2 * kap * uL + b * Tv * a0^2 * ce * t2 + (2) * b * Tu * a0 * a1 * ce * t2 + b * Tu * a0^2 * ce * t1) + pi^3 * ((2) * a * a0 * a1 * ce * t2 * kap * ua + a * a0^2 * ce * t1 * kap * ua + a * a0^2 * ce * t2 * kap * va + (-1) * b * a0^2 * lam * ce * t2 * kap * uL)) := by
  unfold nodeAlg; ring

/-- `GV ≥ 0` elements form a subring of `MPT`. -/
def GV0 (p : ℕ) [Fact p.Prime] : Subring MPT where
  carrier := {x | GV p 0 x}
  mul_mem' := fun {a b} ha hb => by simpa using GV.mul (p := p) ha hb
  one_mem' := GV.one
  add_mem' := fun {a b} ha hb => GV.add ha hb
  zero_mem' := GV.zero 0
  neg_mem' := fun {a} ha => GV.neg ha

lemma nodeAlg_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va : S) :
    f (nodeAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va) =
      nodeAlg (f pi) (f b) (f a) (f Tu) (f Tv) (f a0) (f a1) (f cb) (f l) (f lam) (f R0) (f R1) (f ce)
        (f t2) (f t1) (f kap) (f uL) (f ua) (f va) := by
  unfold nodeAlg
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]

lemma nodeAlg_GV {pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va : MPT}
    (hpi1 : GV p 1 pi) (hb : GV p 0 b) (ha : GV p 0 a) (hTu : GV p 0 Tu) (hTv : GV p 0 Tv)
    (ha0 : GV p 0 a0) (ha1 : GV p 0 a1) (hcb : GV p 0 cb) (hl : GV p 0 l) (hlam : GV p 0 lam)
    (hR0 : GV p 0 R0) (hR1 : GV p 0 R1) (hce : GV p 0 ce) (ht2 : GV p 0 t2) (ht1 : GV p 0 t1)
    (hkap : GV p 0 kap) (huL : GV p 0 uL) (hua : GV p 0 ua) (hva : GV p 0 va) :
    GV p 2 (nodeAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va) := by
  have hpi : GV p 0 pi := hpi1.mono (by norm_num)
  obtain ⟨Z, hZ⟩ : ∃ Z : GV0 p, nodeAlg (⟨pi, hpi⟩ : GV0 p) ⟨b, hb⟩ ⟨a, ha⟩ ⟨Tu, hTu⟩ ⟨Tv, hTv⟩
      ⟨a0, ha0⟩ ⟨a1, ha1⟩ ⟨cb, hcb⟩ ⟨l, hl⟩ ⟨lam, hlam⟩ ⟨R0, hR0⟩ ⟨R1, hR1⟩ ⟨ce, hce⟩ ⟨t2, ht2⟩
      ⟨t1, ht1⟩ ⟨kap, hkap⟩ ⟨uL, huL⟩ ⟨ua, hua⟩ ⟨va, hva⟩ = (⟨pi, hpi⟩ : GV0 p) ^ 2 * Z :=
    ⟨_, nodeAlg_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  have hmap := congrArg (GV0 p).subtype hZ
  rw [nodeAlg_map] at hmap
  simp only [Subring.subtype_apply, map_mul, map_pow] at hmap
  rw [show nodeAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va = _ from hmap]
  have := (hpi1.pow 2).mul Z.2
  simpa using this
lemma GV_Cpowinv_mul {e : ℤ} (k : ℕ) {f : MPT} (hf : GV p e f) :
    GV p (e - k) (MvPolynomial.C (((p : ℚ) ^ k)⁻¹) * f) := by
  have hp0 := p_ne_zero' (p := p)
  have := GV.const_mul (e := -(k : ℤ)) (e' := e) (x := ((p : ℚ) ^ k)⁻¹) (by
    rw [neg_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero k hp0)]; exact (LocRing p).one_mem) hf
  exact this.mono (le_of_eq (by ring))

/-- The per-node main term `B_ℓ` of Lemma P: `∑_ℓ B_ℓ = resJet`. -/
def nodeTerm (n p s μ : ℕ) (τu kap : ℕ → ℚ) (A R : MPT[X]) (ℓ : ℕ) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 4) * (cbarZ n p s : ℚ)) *
    (bT * (R.eval (MvPolynomial.C (-(s : ℚ))) *
          (Tu ℓ * (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) * (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) +
            Tv ℓ * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2) +
        MvPolynomial.C (p : ℚ) * (MvPolynomial.C (ℓ : ℚ) *
            (MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) -
              (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) *
            (Tu ℓ * (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) * (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) +
              Tv ℓ * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2) +
          (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) * Tu ℓ *
            (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 -
          MvPolynomial.C (lam0 n p s) * MvPolynomial.C (τu ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 *
            R.eval (MvPolynomial.C (-(s : ℚ))))) +
      MvPolynomial.C (p : ℚ) * aT * R.eval (MvPolynomial.C (-(s : ℚ))) *
        (MvPolynomial.C (kap ℓ) * (MvPolynomial.C (uaL ℓ) *
            (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) * (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) +
          MvPolynomial.C (vaL n p (s + ℓ * p) ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2)))

lemma linM_cLoc (L : ℕ) (Φ : MPT[X]) :
    linM (cLoc L) Φ = ∑ l ∈ range L, (Tv (l + 1) * Φ.eval (MvPolynomial.C (-((l + 1 : ℕ) : ℚ))) +
      Tu (l + 1) * (Polynomial.derivative Φ).eval (MvPolynomial.C (-((l + 1 : ℕ) : ℚ)))) := by
  unfold linM cLoc
  rw [Polynomial.sum_def]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Polynomial.eval_eq_sum, Polynomial.derivative_eval, Polynomial.sum_def, Polynomial.sum_def,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_pow, map_mul, map_neg, map_natCast]
  ring

lemma eval_deriv_sq (A : MPT[X]) (x : MPT) :
    (Polynomial.derivative (A ^ 2)).eval x = 2 * A.eval x * (Polynomial.derivative A).eval x := by
  simp only [pow_two, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul]
  ring

lemma eval_deriv_XA2 (A : MPT[X]) (x : MPT) :
    (Polynomial.derivative (Polynomial.X * A ^ 2)).eval x =
      (A.eval x) ^ 2 + x * (2 * A.eval x * (Polynomial.derivative A).eval x) := by
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_deriv_sq]
  simp only [Polynomial.derivative_X, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_pow]
  ring

lemma evk_P_sq (p μ s ℓ : ℕ) (A R : MPT[X]) (hAd : A.natDegree ≤ μ) :
    evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R) =
      MvPolynomial.C ((p : ℚ) ^ (2 * μ)) * ((A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 * evk (s + ℓ * p) R) := by
  rw [pow_two, evk_mul, evk_mul, shiftP_eval p μ s ℓ A hAd]
  have : (MvPolynomial.C ((p : ℚ) ^ (2 * μ)) : MPT) =
      MvPolynomial.C ((p : ℚ) ^ μ) * MvPolynomial.C ((p : ℚ) ^ μ) := by
    rw [← map_mul, ← pow_add]; congr 2; ring
  rw [this]; ring

lemma devk_P_sq (p μ s ℓ : ℕ) (A R : MPT[X]) (hAd : A.natDegree ≤ μ) :
    MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R) =
      MvPolynomial.C ((p : ℚ) ^ (2 * μ)) *
        (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) * (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ))) *
            evk (s + ℓ * p) R +
          MvPolynomial.C (p : ℚ) * ((A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 * devk (s + ℓ * p) R)) := by
  have h1 := shiftP_eval p μ s ℓ A hAd
  have h2 := shiftP_deriv p μ s ℓ A hAd
  rw [pow_two, devk_mul, devk_mul, evk_mul, h1]
  have : (MvPolynomial.C ((p : ℚ) ^ (2 * μ)) : MPT) =
      MvPolynomial.C ((p : ℚ) ^ μ) * MvPolynomial.C ((p : ℚ) ^ μ) := by
    rw [← map_mul, ← pow_add]; congr 2; ring
  rw [this]
  linear_combination (2 * MvPolynomial.C ((p : ℚ) ^ μ) * A.eval (MvPolynomial.C (-(ℓ : ℚ))) *
    evk (s + ℓ * p) R) * h2

/-- `∑_ℓ B_ℓ = resJet`. -/
theorem sum_nodeTerm (n p s L μ : ℕ) (τu kap : ℕ → ℚ) (A R : MPT[X]) :
    ∑ l ∈ range L, nodeTerm n p s μ τu kap A R (l + 1) = resJet n p s L μ τu kap A R := by
  unfold resJet locUtau locAk
  rw [linM_cLoc, linM_cLoc]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, nodeTerm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [eval_deriv_sq, eval_deriv_XA2]
  simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, map_neg]
  ring

/-- One node `ℓ ≥ 1` of Lemma P: `nodeT_k(P_s² R) ≡ B_ℓ` modulo `p^{σ+2μ-2}`. -/
lemma node_step (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ) (hL1 : s + L * p ≤ 6 * n)
    (hK : ∀ l, 1 ≤ l → l ≤ L → (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (μ : ℕ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ) (R : MPT[X]) (hR : PInt p R)
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    GV p ((sig n p s : ℤ) + 2 * μ - 2)
      (nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  have hkmod : (s + ℓ * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hkdiv : (s + ℓ * p) / p = ℓ := by
    rw [Nat.add_mul_div_right _ _ hpp, Nat.div_eq_of_lt hs, zero_add]
  have hk6 : s + ℓ * p ≤ 6 * n := by
    have : ℓ * p ≤ L * p := Nat.mul_le_mul_right p hℓL
    omega
  obtain ⟨hKk, hd⟩ := hK ℓ hℓ1 hℓL
  have hq6 : ℓ + bflag n p s ≤ q6 n p := by
    obtain ⟨h1, -, -⟩ := sub_div_mod p (6 * n) (s + ℓ * p) hpp hk6
    rw [hkdiv, hkmod] at h1
    exact h1
  have hP := JetGE.shiftP μ s ℓ hA hAd
  have hJ : JetGE p (s + ℓ * p) (2 * μ) (shiftP p μ s A ^ 2 * R) := by
    have := (hP.mul hP).mul (JetGE.of_pint (k := s + ℓ * p) hR)
    rw [pow_two]
    exact this.mono (le_of_eq (by ring))
  have h1 := nodeT_jet n K σ cl τu τv h8 h3 (s + ℓ * p) hk6 hKk hd _ _ hJ
  rw [hkmod] at h1
  have h2 : GV p ((sig n p s : ℤ) + 2 * μ - 2)
      (nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by
    obtain ⟨-, -, -, hτu, -⟩ := hd
    rw [hkmod, hkdiv] at hτu
    have hkp : ℓ < p := by
      have : (s + ℓ * p) / p < p := by
        rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show s + ℓ * p < p ^ 2 by omega)
      rwa [hkdiv] at this
    obtain ⟨ce, hce, e_cl⟩ : ∃ ce ∈ LocRing p, (clZ n p ℓ s : ℚ) =
        (cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s) + (p : ℚ) ^ 2 * ce :=
      ⟨_, clZ_split_Q n ℓ s hs h3 hq6, by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hp0), one_mul]; ring⟩
    obtain ⟨hT2, hT1⟩ := taylor_p2 hR s ℓ
    obtain ⟨t2, ht2def⟩ : ∃ t2 : MPT, t2 = MvPolynomial.C (((p : ℚ) ^ 2)⁻¹) *
        (evk (s + ℓ * p) R - (R.eval (MvPolynomial.C (-(s : ℚ))) -
          MvPolynomial.C ((ℓ : ℚ) * p) * (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))))) :=
      ⟨_, rfl⟩
    have ht2 : GV p 0 t2 := by rw [ht2def]; simpa using GV_Cpowinv_mul 2 hT2
    have e_Rk : evk (s + ℓ * p) R = R.eval (MvPolynomial.C (-(s : ℚ))) -
        MvPolynomial.C ((ℓ : ℚ) * p) * (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) +
        MvPolynomial.C ((p : ℚ) ^ 2) * t2 := by
      rw [ht2def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero 2 hp0), map_one, one_mul]; ring
    obtain ⟨t1, ht1def⟩ : ∃ t1 : MPT, t1 = MvPolynomial.C ((p : ℚ)⁻¹) *
        (devk (s + ℓ * p) R - (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) := ⟨_, rfl⟩
    have ht1 : GV p 0 t1 := by rw [ht1def]; simpa using GV_Cinv_mul hT1
    have e_Rk' : devk (s + ℓ * p) R = (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) +
        MvPolynomial.C (p : ℚ) * t1 := by
      rw [ht1def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]; ring
    have hq : (p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 4) =
        (p : ℚ) ^ ((sig n p s : ℤ) - 4) * (p : ℚ) ^ (2 * μ) := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]; congr 1; push_cast; ring
    have hid : nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ =
        MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 4)) *
          nodeAlg (MvPolynomial.C (p : ℚ)) bT aT (Tu ℓ) (Tv ℓ) (A.eval (MvPolynomial.C (-(ℓ : ℚ))))
            ((Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) (MvPolynomial.C (cbarZ n p s : ℚ))
            (MvPolynomial.C (ℓ : ℚ)) (MvPolynomial.C (lam0 n p s)) (R.eval (MvPolynomial.C (-(s : ℚ))))
            ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) (MvPolynomial.C ce) t2 t1
            (MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ)) (MvPolynomial.C (uL ℓ))
            (MvPolynomial.C (uaL ℓ)) (MvPolynomial.C (vaL n p (s + ℓ * p) ℓ)) := by
      rw [evk_P_sq _ _ _ _ _ _ hAd, devk_P_sq _ _ _ _ _ _ hAd]
      unfold nodeJet nodeTerm nodeAlg
      simp only [hkmod, hkdiv]
      rw [e_cl, e_Rk, e_Rk', hq, hτu]
      simp only [map_mul, map_add, map_sub, map_pow, map_one]
      ring
    rw [hid]
    have hCq : GV p ((sig n p s : ℤ) + 2 * μ - 4)
        (MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 4)) : MPT) :=
      GV_C_eq (y := 1) (by simp) (LocRing p).one_mem
    have hpi1 : GV p 1 (MvPolynomial.C (p : ℚ) : MPT) := by
      simpa using GV_Cp_mul (p := p) (e := 0) (GV.one (σ := TVar))
    have hnegℓ : (-(ℓ : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem ℓ)
    have hnegs : (-(s : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem s)
    have hδ := delta_mem (p := p) n (s + ℓ * p) h8 hk6
    have hh2 := Hq_mem (p := p) 2 ℓ hkp
    have hh3 := Hq_mem (p := p) 3 ℓ hkp
    have hua : uaL ℓ ∈ LocRing p := by unfold uaL; exact (LocRing p).mul_mem lm3 hh2
    have hva : vaL n p (s + ℓ * p) ℓ ∈ LocRing p := by
      unfold vaL
      exact (LocRing p).mul_mem lm3 ((LocRing p).add_mem ((LocRing p).mul_mem hδ hh2)
        ((LocRing p).mul_mem l2 hh3))
    have hbb : GV p 0 bT := GV.var _
    have haa : GV p 0 aT := GV.var _
    have hTuu : GV p 0 (Tu ℓ) := GV.var _
    have hTvv : GV p 0 (Tv ℓ) := GV.var _
    refine (hCq.mul (e' := 2) ?_).mono (le_of_eq (by ring))
    exact nodeAlg_GV (p := p) hpi1 hbb haa hTuu hTvv
      (GV_eval hA hnegℓ) (GV_eval (PInt_derivative hA) hnegℓ)
      (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (cbarZ n p s))) (GV.const_loc (natq_mem ℓ))
      (GV.const_loc (lam0_mem (p := p) n s hs)) (GV_eval hR hnegs) (GV_eval (PInt_derivative hR) hnegs)
      (GV.const_loc hce) ht2 ht1
      (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (kapZ n p (bflag n p s) (eflag n p s) ℓ)))
      (GV.const_loc (uL_mem (p := p) ℓ hkp))
      (GV.const_loc hua) (GV.const_loc hva)
  have hsum : nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ =
      (nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
          (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))) +
      (nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by ring
  rw [hsum]
  exact (h1.mono (le_of_eq (by ring))).add h2

/-- **L2S-11, Lemma P** (per-residue formula). -/
theorem res_second (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ) (hL1 : s + L * p ≤ 6 * n)
    (hL2 : 6 * n < s + (L + 1) * p)
    (hK : ∀ l, 1 ≤ l → l ≤ L → (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (hK0 : s ∉ K) (μ : ℕ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p s : ℤ) + 2 * μ - 2)
      (∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p) (shiftP p μ s A ^ 2 * R) -
        resJet n p s L μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R) := by
  rw [Finset.sum_range_succ', ← sum_nodeTerm n p s L μ τu
    (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R]
  have hz : nodeT (p := p) n K σ cl τu τv (s + 0 * p) (shiftP p μ s A ^ 2 * R) =
      ndT n s (shiftP p μ s A ^ 2 * R) := by
    simp only [zero_mul, add_zero]
    unfold nodeT; rw [if_neg hK0, add_zero]
  have hs6 : s ≤ 6 * n := by omega
  have hP0 : JetGE p s μ (shiftP p μ s A) := by
    simpa using JetGE.shiftP (p := p) μ s 0 hA hAd
  have hJ0 : JetGE p s (2 * μ) (shiftP p μ s A ^ 2 * R) := by
    have := (hP0.mul hP0).mul (JetGE.of_pint (k := s) hR)
    rw [pow_two]
    exact this.mono (le_of_eq (by ring))
  have hnd0 := nd0_jet n s h8 h3 hs6 hs _ _ hJ0
  rw [hz]
  have hsum : ∑ l ∈ range L, nodeT (p := p) n K σ cl τu τv (s + (l + 1) * p) (shiftP p μ s A ^ 2 * R) +
        ndT n s (shiftP p μ s A ^ 2 * R) -
      ∑ l ∈ range L, nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R (l + 1) =
      ∑ l ∈ range L, (nodeT (p := p) n K σ cl τu τv (s + (l + 1) * p) (shiftP p μ s A ^ 2 * R) -
        nodeTerm n p s μ τu (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R (l + 1)) +
      ndT n s (shiftP p μ s A ^ 2 * R) := by
    rw [Finset.sum_sub_distrib]; ring
  rw [hsum]
  refine (GV.sum fun l hl => ?_).add (hnd0.mono (by omega))
  have hl' := Finset.mem_range.1 hl
  exact node_step n K σ cl τu τv h8 h3 s hs L hL1 hK μ A hA hAd R hR (l + 1) (by omega) (by omega)

end ResSecond

/-! ### Part 8: own pairs (L2S-13) -/

section OwnPair

variable {p : ℕ} [hp : Fact p.Prime]

theorem JetGE.pow {k : ℕ} {e : ℤ} {F : MPT[X]} (hF : JetGE p k e F) (i : ℕ) : JetGE p k (i * e) (F ^ i) := by
  induction i with
  | zero =>
    have : PInt p (1 : MPT[X]) := by
      intro j
      rw [Polynomial.coeff_one]
      split_ifs
      · exact GV.one
      · exact GV.zero 0
    simpa using JetGE.of_pint (p := p) (k := k) this
  | succ i ih =>
    rw [pow_succ]
    have := ih.mul hF
    exact this.mono (le_of_eq (by push_cast; ring))

/-- Difference `LHS - RHS` of the first-order node congruence of Lemma O. -/
def ownAlg {S : Type*} [CommRing S] (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi : S) : S :=
  (cb + pi * cb * l * lam + pi ^ 2 * ce) *
    (b * (Tu * ((mi * a0 + m * a1) * (R0 - pi * l * R1 + pi ^ 2 * t2) + pi * (m * a0 * (R1 + pi * t1))) +
        Tv * (m * a0 * (R0 - pi * l * R1 + pi ^ 2 * t2)) -
        pi * kap * lam * uL * (m * a0 * (R0 - pi * l * R1 + pi ^ 2 * t2))) +
      pi * a * kap * (ua * ((mi * a0 + m * a1) * (R0 - pi * l * R1 + pi ^ 2 * t2) +
          pi * (m * a0 * (R1 + pi * t1))) +
        va * (m * a0 * (R0 - pi * l * R1 + pi ^ 2 * t2)))) -
  cb * b * R0 * (Tu * (mi * a0 + m * a1) + Tv * m * a0)

lemma ownAlg_eq {S : Type*} [CommRing S]
    (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi : S) :
    ownAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi = pi * (a * a1 * cb * R0 * kap * ua * m + a * a0 * cb * R0 * kap * va * m + a * a0 * cb * R0 * kap * ua * mi + (-1) * b * a0 * cb * lam * R0 * kap * uL * m + (-1) * b * Tv * a0 * cb * l * R1 * m + b * Tv * a0 * cb * l * lam * R0 * m + (-1) * b * Tu * a1 * cb * l * R1 * m + b * Tu * a1 * cb * l * lam * R0 * m + b * Tu * a0 * cb * R1 * m + (-1) * b * Tu * a0 * cb * l * R1 * mi + b * Tu * a0 * cb * l * lam * R0 * mi + pi^1 * ((-1) * a * a1 * cb * l * R1 * kap * ua * m + a * a1 * cb * l * lam * R0 * kap * ua * m + a * a0 * cb * R1 * kap * ua * m + (-1) * a * a0 * cb * l * R1 * kap * va * m + (-1) * a * a0 * cb * l * R1 * kap * ua * mi + a * a0 * cb * l * lam * R0 * kap * va * m + a * a0 * cb * l * lam * R0 * kap * ua * mi + b * a0 * cb * l * lam * R1 * kap * uL * m + (-1) * b * a0 * cb * l * lam^2 * R0 * kap * uL * m + b * Tv * a0 * R0 * ce * m + b * Tv * a0 * cb * t2 * m + (-1) * b * Tv * a0 * cb * l^2 * lam * R1 * m + b * Tu * a1 * R0 * ce * m + b * Tu * a1 * cb * t2 * m + (-1) * b * Tu * a1 * cb * l^2 * lam * R1 * m + b * Tu * a0 * R0 * ce * mi + b * Tu * a0 * cb * t1 * m + b * Tu * a0 * cb * t2 * mi + b * Tu * a0 * cb * l * lam * R1 * m + (-1) * b * Tu * a0 * cb * l^2 * lam * R1 * mi) + pi^2 * (a * a1 * R0 * ce * kap * ua * m + a * a1 * cb * t2 * kap * ua * m + (-1) * a * a1 * cb * l^2 * lam * R1 * kap * ua * m + a * a0 * R0 * ce * kap * va * m + a * a0 * R0 * ce * kap * ua * mi + a * a0 * cb * t1 * kap * ua * m + a * a0 * cb * t2 * kap * va * m + a * a0 * cb * t2 * kap * ua * mi + a * a0 * cb * l * lam * R1 * kap * ua * m + (-1) * a * a0 * cb * l^2 * lam * R1 * kap * va * m + (-1) * a * a0 * cb * l^2 * lam * R1 * kap * ua * mi + (-1) * b * a0 * lam * R0 * ce * kap * uL * m + (-1) * b * a0 * cb * lam * t2 * kap * uL * m + b * a0 * cb * l^2 * lam^2 * R1 * kap * uL * m + (-1) * b * Tv * a0 * l * R1 * ce * m + b * Tv * a0 * cb * l * lam * t2 * m + (-1) * b * Tu * a1 * l * R1 * ce * m + b * Tu * a1 * cb * l * lam * t2 * m + b * Tu * a0 * R1 * ce * m + (-1) * b * Tu * a0 * l * R1 * ce * mi + b * Tu * a0 * cb * l * lam * t1 * m + b * Tu * a0 * cb * l * lam * t2 * mi) + pi^3 * ((-1) * a * a1 * l * R1 * ce * kap * ua * m + a * a1 * cb * l * lam * t2 * kap * ua * m + a * a0 * R1 * ce * kap * ua * m + (-1) * a * a0 * l * R1 * ce * kap * va * m + (-1) * a * a0 * l * R1 * ce * kap * ua * mi + a * a0 * cb * l * lam * t1 * kap * ua * m + a * a0 * cb * l * lam * t2 * kap * va * m + a * a0 * cb * l * lam * t2 * kap * ua * mi + b * a0 * l * lam * R1 * ce * kap * uL * m + (-1) * b * a0 * cb * l * lam^2 * t2 * kap * uL * m + b * Tv * a0 * ce * t2 * m + b * Tu * a1 * ce * t2 * m + b * Tu * a0 * ce * t1 * m + b * Tu * a0 * ce * t2 * mi) + pi^4 * (a * a1 * ce * t2 * kap * ua * m + a * a0 * ce * t1 * kap * ua * m + a * a0 * ce * t2 * kap * va * m + a * a0 * ce * t2 * kap * ua * mi + (-1) * b * a0 * lam * ce * t2 * kap * uL * m)) := by
  unfold ownAlg; ring

lemma ownAlg_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi : S) :
    f (ownAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi) =
      ownAlg (f pi) (f b) (f a) (f Tu) (f Tv) (f a0) (f a1) (f cb) (f l) (f lam) (f R0) (f R1) (f ce)
        (f t2) (f t1) (f kap) (f uL) (f ua) (f va) (f m) (f mi) := by
  unfold ownAlg
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat]

lemma ownAlg_GV {pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi : MPT}
    (hpi1 : GV p 1 pi) (hb : GV p 0 b) (ha : GV p 0 a) (hTu : GV p 0 Tu) (hTv : GV p 0 Tv)
    (ha0 : GV p 0 a0) (ha1 : GV p 0 a1) (hcb : GV p 0 cb) (hl : GV p 0 l) (hlam : GV p 0 lam)
    (hR0 : GV p 0 R0) (hR1 : GV p 0 R1) (hce : GV p 0 ce) (ht2 : GV p 0 t2) (ht1 : GV p 0 t1)
    (hkap : GV p 0 kap) (huL : GV p 0 uL) (hua : GV p 0 ua) (hva : GV p 0 va)
    (hm : GV p 0 m) (hmi : GV p 0 mi) :
    GV p 1 (ownAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi) := by
  have hpi : GV p 0 pi := hpi1.mono (by norm_num)
  obtain ⟨Z, hZ⟩ : ∃ Z : GV0 p, ownAlg (⟨pi, hpi⟩ : GV0 p) ⟨b, hb⟩ ⟨a, ha⟩ ⟨Tu, hTu⟩ ⟨Tv, hTv⟩
      ⟨a0, ha0⟩ ⟨a1, ha1⟩ ⟨cb, hcb⟩ ⟨l, hl⟩ ⟨lam, hlam⟩ ⟨R0, hR0⟩ ⟨R1, hR1⟩ ⟨ce, hce⟩ ⟨t2, ht2⟩
      ⟨t1, ht1⟩ ⟨kap, hkap⟩ ⟨uL, huL⟩ ⟨ua, hua⟩ ⟨va, hva⟩ ⟨m, hm⟩ ⟨mi, hmi⟩ =
      (⟨pi, hpi⟩ : GV0 p) * Z :=
    ⟨_, ownAlg_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  have hmap := congrArg (GV0 p).subtype hZ
  rw [ownAlg_map] at hmap
  simp only [Subring.subtype_apply, map_mul] at hmap
  rw [show ownAlg pi b a Tu Tv a0 a1 cb l lam R0 R1 ce t2 t1 kap uL ua va m mi = _ from hmap]
  have := hpi1.mul Z.2
  simpa using this

lemma evk_own (p μ s ℓ i : ℕ) (A R : MPT[X]) (hAd : A.natDegree ≤ μ) :
    evk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R) =
      MvPolynomial.C ((p : ℚ) ^ (μ + i)) *
        ((MvPolynomial.C (-(ℓ : ℚ))) ^ i * A.eval (MvPolynomial.C (-(ℓ : ℚ))) * evk (s + ℓ * p) R) := by
  have hS : evk (s + ℓ * p) (sX s ^ i) =
      (MvPolynomial.C (p : ℚ)) ^ i * (MvPolynomial.C (-(ℓ : ℚ))) ^ i := by
    unfold evk
    rw [Polynomial.eval_pow, sX_eval_node, mul_pow]
  rw [evk_mul, evk_mul, hS, shiftP_eval p μ s ℓ A hAd]
  simp only [map_pow]
  ring

lemma devk_own (p μ s ℓ i : ℕ) (A R : MPT[X]) (hAd : A.natDegree ≤ μ) :
    MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R) =
      MvPolynomial.C ((p : ℚ) ^ (μ + i)) *
        (((i : MPT) * (MvPolynomial.C (-(ℓ : ℚ))) ^ (i - 1) * A.eval (MvPolynomial.C (-(ℓ : ℚ))) +
            (MvPolynomial.C (-(ℓ : ℚ))) ^ i * (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) *
            evk (s + ℓ * p) R +
          MvPolynomial.C (p : ℚ) * ((MvPolynomial.C (-(ℓ : ℚ))) ^ i * A.eval (MvPolynomial.C (-(ℓ : ℚ))) *
            devk (s + ℓ * p) R)) := by
  have hS : evk (s + ℓ * p) (sX s ^ i) =
      (MvPolynomial.C (p : ℚ)) ^ i * (MvPolynomial.C (-(ℓ : ℚ))) ^ i := by
    unfold evk
    rw [Polynomial.eval_pow, sX_eval_node, mul_pow]
  have hdS : MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i) =
      (MvPolynomial.C (p : ℚ)) ^ i * ((i : MPT) * (MvPolynomial.C (-(ℓ : ℚ))) ^ (i - 1)) := by
    unfold devk
    have hd : Polynomial.derivative (sX s) = 1 := by simp [sX]
    rw [Polynomial.derivative_pow, hd]
    simp only [mul_one, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_C]
    have := sX_eval_node p s ℓ
    rw [this]
    cases i with
    | zero => simp
    | succ j => simp only [Nat.add_sub_cancel]; push_cast; ring
  have h1 := shiftP_eval p μ s ℓ A hAd
  have h2 := shiftP_deriv p μ s ℓ A hAd
  rw [devk_mul, devk_mul, evk_mul, hS, h1]
  simp only [map_pow] at h2 ⊢
  linear_combination (evk (s + ℓ * p) R) * (MvPolynomial.C (p : ℚ) ^ μ * A.eval (MvPolynomial.C (-(ℓ : ℚ)))) * hdS +
    ((MvPolynomial.C (p : ℚ)) ^ i * (MvPolynomial.C (-(ℓ : ℚ))) ^ i * evk (s + ℓ * p) R) * h2

lemma evalXiA (i : ℕ) (A : MPT[X]) (x : MPT) : (Polynomial.X ^ i * A).eval x = x ^ i * A.eval x := by
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

lemma evalDXiA (i : ℕ) (A : MPT[X]) (x : MPT) :
    (Polynomial.derivative (Polynomial.X ^ i * A)).eval x =
      (i : MPT) * x ^ (i - 1) * A.eval x + x ^ i * (Polynomial.derivative A).eval x := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_natCast]

/-- The per-node main term of Lemma O (it sums to `0`). -/
def ownTerm (n p s μ i : ℕ) (A R : MPT[X]) (ℓ : ℕ) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) - 4 + μ + i) * (cbarZ n p s : ℚ)) *
    (bT * R.eval (MvPolynomial.C (-(s : ℚ))) *
      (Tu ℓ * (Polynomial.derivative (Polynomial.X ^ i * A)).eval (MvPolynomial.C (-(ℓ : ℚ))) +
        Tv ℓ * (Polynomial.X ^ i * A).eval (MvPolynomial.C (-(ℓ : ℚ)))))

lemma sum_ownTerm (n p s μ i L : ℕ) (A R : MPT[X]) (h : linM (cLoc L) (Polynomial.X ^ i * A) = 0) :
    ∑ l ∈ range L, ownTerm n p s μ i A R (l + 1) = 0 := by
  unfold ownTerm
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have : ∑ l ∈ range L, (Tu (l + 1) * (Polynomial.derivative (Polynomial.X ^ i * A)).eval
        (MvPolynomial.C (-((l + 1 : ℕ) : ℚ))) + Tv (l + 1) * (Polynomial.X ^ i * A).eval
        (MvPolynomial.C (-((l + 1 : ℕ) : ℚ)))) = linM (cLoc L) (Polynomial.X ^ i * A) := by
    rw [linM_cLoc]
    exact Finset.sum_congr rfl fun l _ => add_comm _ _
  rw [this, h]; simp

lemma own_node_step (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ) (hL1 : s + L * p ≤ 6 * n)
    (hK : ∀ l, 1 ≤ l → l ≤ L → (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (μ : ℕ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ) (R : MPT[X]) (hR : PInt p R)
    (i ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓL : ℓ ≤ L) :
    GV p ((sig n p s : ℤ) - 3 + μ + i)
      (nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R) -
        ownTerm n p s μ i A R ℓ) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  have hkmod : (s + ℓ * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hkdiv : (s + ℓ * p) / p = ℓ := by
    rw [Nat.add_mul_div_right _ _ hpp, Nat.div_eq_of_lt hs, zero_add]
  have hk6 : s + ℓ * p ≤ 6 * n := by
    have : ℓ * p ≤ L * p := Nat.mul_le_mul_right p hℓL
    omega
  obtain ⟨hKk, hd⟩ := hK ℓ hℓ1 hℓL
  have hq6 : ℓ + bflag n p s ≤ q6 n p := by
    obtain ⟨h1, -, -⟩ := sub_div_mod p (6 * n) (s + ℓ * p) hpp hk6
    rw [hkdiv, hkmod] at h1
    exact h1
  have hP := JetGE.shiftP μ s ℓ hA hAd
  have hS := (JetGE_sX_aux (p := p) s ℓ).pow i
  have hJ : JetGE p (s + ℓ * p) (i + μ) (sX s ^ i * shiftP p μ s A * R) := by
    have := (hS.mul hP).mul (JetGE.of_pint (k := s + ℓ * p) hR)
    exact this.mono (le_of_eq (by ring))
  have h1 := nodeT_jet n K σ cl τu τv h8 h3 (s + ℓ * p) hk6 hKk hd _ _ hJ
  rw [hkmod] at h1
  have h2 : GV p ((sig n p s : ℤ) - 3 + μ + i)
      (nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R)) -
        ownTerm n p s μ i A R ℓ) := by
    obtain ⟨-, -, -, hτu, -⟩ := hd
    rw [hkmod, hkdiv] at hτu
    have hkp : ℓ < p := by
      have : (s + ℓ * p) / p < p := by
        rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show s + ℓ * p < p ^ 2 by omega)
      rwa [hkdiv] at this
    obtain ⟨ce, hce, e_cl⟩ : ∃ ce ∈ LocRing p, (clZ n p ℓ s : ℚ) =
        (cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s) + (p : ℚ) ^ 2 * ce :=
      ⟨_, clZ_split_Q n ℓ s hs h3 hq6, by
        rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hp0), one_mul]; ring⟩
    obtain ⟨hT2, hT1⟩ := taylor_p2 hR s ℓ
    obtain ⟨t2, ht2def⟩ : ∃ t2 : MPT, t2 = MvPolynomial.C (((p : ℚ) ^ 2)⁻¹) *
        (evk (s + ℓ * p) R - (R.eval (MvPolynomial.C (-(s : ℚ))) -
          MvPolynomial.C ((ℓ : ℚ) * p) * (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))))) :=
      ⟨_, rfl⟩
    have ht2 : GV p 0 t2 := by rw [ht2def]; simpa using GV_Cpowinv_mul 2 hT2
    have e_Rk : evk (s + ℓ * p) R = R.eval (MvPolynomial.C (-(s : ℚ))) -
        MvPolynomial.C ((ℓ : ℚ) * p) * (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) +
        MvPolynomial.C ((p : ℚ) ^ 2) * t2 := by
      rw [ht2def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero 2 hp0), map_one, one_mul]; ring
    obtain ⟨t1, ht1def⟩ : ∃ t1 : MPT, t1 = MvPolynomial.C ((p : ℚ)⁻¹) *
        (devk (s + ℓ * p) R - (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) := ⟨_, rfl⟩
    have ht1 : GV p 0 t1 := by rw [ht1def]; simpa using GV_Cinv_mul hT1
    have e_Rk' : devk (s + ℓ * p) R = (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) +
        MvPolynomial.C (p : ℚ) * t1 := by
      rw [ht1def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]; ring
    have hq : (p : ℚ) ^ ((sig n p s : ℤ) - 4 + μ + i) =
        (p : ℚ) ^ ((sig n p s : ℤ) - 4) * (p : ℚ) ^ (μ + i) := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]; congr 1; push_cast; ring
    have hid : nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R)) -
        ownTerm n p s μ i A R ℓ =
        MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) - 4 + μ + i)) *
          ownAlg (MvPolynomial.C (p : ℚ)) bT aT (Tu ℓ) (Tv ℓ) (A.eval (MvPolynomial.C (-(ℓ : ℚ))))
            ((Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) (MvPolynomial.C (cbarZ n p s : ℚ))
            (MvPolynomial.C (ℓ : ℚ)) (MvPolynomial.C (lam0 n p s)) (R.eval (MvPolynomial.C (-(s : ℚ))))
            ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) (MvPolynomial.C ce) t2 t1
            (MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ)) (MvPolynomial.C (uL ℓ))
            (MvPolynomial.C (uaL ℓ)) (MvPolynomial.C (vaL n p (s + ℓ * p) ℓ))
            ((MvPolynomial.C (-(ℓ : ℚ))) ^ i) ((i : MPT) * (MvPolynomial.C (-(ℓ : ℚ))) ^ (i - 1)) := by
      rw [evk_own _ _ _ _ _ _ _ hAd, devk_own _ _ _ _ _ _ _ hAd]
      unfold nodeJet ownTerm ownAlg
      simp only [hkmod, hkdiv, evalXiA, evalDXiA]
      rw [e_cl, e_Rk, e_Rk', hq]
      simp only [map_mul, map_add, map_sub, map_pow, map_one]
      ring
    rw [hid]
    have hCq : GV p ((sig n p s : ℤ) - 4 + μ + i)
        (MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) - 4 + μ + i)) : MPT) :=
      GV_C_eq (y := 1) (by simp) (LocRing p).one_mem
    have hpi1 : GV p 1 (MvPolynomial.C (p : ℚ) : MPT) := by
      simpa using GV_Cp_mul (p := p) (e := 0) (GV.one (σ := TVar))
    have hnegℓ : (-(ℓ : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem ℓ)
    have hnegs : (-(s : ℚ)) ∈ LocRing p := (LocRing p).neg_mem (natq_mem s)
    have hδ := delta_mem (p := p) n (s + ℓ * p) h8 hk6
    have hh2 := Hq_mem (p := p) 2 ℓ hkp
    have hh3 := Hq_mem (p := p) 3 ℓ hkp
    have hua : uaL ℓ ∈ LocRing p := by unfold uaL; exact (LocRing p).mul_mem lm3 hh2
    have hva : vaL n p (s + ℓ * p) ℓ ∈ LocRing p := by
      unfold vaL
      exact (LocRing p).mul_mem lm3 ((LocRing p).add_mem ((LocRing p).mul_mem hδ hh2)
        ((LocRing p).mul_mem l2 hh3))
    have hbb : GV p 0 bT := GV.var _
    have haa : GV p 0 aT := GV.var _
    have hTuu : GV p 0 (Tu ℓ) := GV.var _
    have hTvv : GV p 0 (Tv ℓ) := GV.var _
    have hm : GV p 0 ((MvPolynomial.C (-(ℓ : ℚ)) : MPT) ^ i) := by
      simpa using (GV.const_loc (σ := TVar) hnegℓ).pow i
    have hnat : GV p 0 ((i : MPT)) := by
      have : ((i : MPT)) = MvPolynomial.C ((i : ℤ) : ℚ) := by simp
      rw [this]; exact GV.const_int _
    have hmi : GV p 0 ((i : MPT) * (MvPolynomial.C (-(ℓ : ℚ))) ^ (i - 1)) := by
      simpa using hnat.mul (by simpa using (GV.const_loc (σ := TVar) hnegℓ).pow (i - 1))
    refine (hCq.mul (e' := 1) ?_).mono (le_of_eq (by ring))
    exact ownAlg_GV (p := p) hpi1 hbb haa hTuu hTvv
      (GV_eval hA hnegℓ) (GV_eval (PInt_derivative hA) hnegℓ)
      (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (cbarZ n p s))) (GV.const_loc (natq_mem ℓ))
      (GV.const_loc (lam0_mem (p := p) n s hs)) (GV_eval hR hnegs) (GV_eval (PInt_derivative hR) hnegs)
      (GV.const_loc hce) ht2 ht1
      (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (kapZ n p (bflag n p s) (eflag n p s) ℓ)))
      (GV.const_loc (uL_mem (p := p) ℓ hkp)) (GV.const_loc hua) (GV.const_loc hva) hm hmi
  have hsum : nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R) -
        ownTerm n p s μ i A R ℓ =
      (nodeT (p := p) n K σ cl τu τv (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R) -
        nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R))
          (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R))) +
      (nodeJet n p (s + ℓ * p) (evk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (sX s ^ i * shiftP p μ s A * R)) -
        ownTerm n p s μ i A R ℓ) := by ring
  rw [hsum]
  exact (h1.mono (by omega)).add h2

/-- **L2S-13, Lemma O** (own pairs). -/
theorem own_pair (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (h8 : 8 * n < p ^ 2)
    (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ) (hL1 : s + L * p ≤ 6 * n)
    (hL2 : 6 * n < s + (L + 1) * p)
    (hK : ∀ l, 1 ≤ l → l ≤ L → (s + l * p) ∈ K ∧ NodeData2 p n σ cl τu τv (s + l * p))
    (hK0 : s ∉ K) (μ i : ℕ) (hi : i < μ) (R : MPT[X]) (hR : PInt p R) :
    GV p ((sig n p s : ℤ) - 3 + μ + i)
      (∑ l ∈ range (L + 1), nodeT (p := p) n K σ cl τu τv (s + l * p)
        (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R)) := by
  have hA : PInt p (orthA (cLoc L) μ) := orthA_pint _ _ (fun j => GV_cLoc L j)
  have hAd := orthA_natDegree_le (cLoc L) μ
  have horth : linM (cLoc L) (Polynomial.X ^ i * orthA (cLoc L) μ) = 0 := orthA_orth _ μ i hi
  rw [Finset.sum_range_succ']
  have hz : nodeT (p := p) n K σ cl τu τv (s + 0 * p) (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) =
      ndT n s (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) := by
    simp only [zero_mul, add_zero]
    unfold nodeT; rw [if_neg hK0, add_zero]
  have hs6 : s ≤ 6 * n := by omega
  have hP0 : JetGE p s μ (shiftP p μ s (orthA (cLoc L) μ)) := by
    simpa using JetGE.shiftP (p := p) μ s 0 hA hAd
  have hS0 : JetGE p s 1 (sX s) := by simpa using JetGE_sX_aux (p := p) s 0
  have hJ0 : JetGE p s (i + μ) (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) := by
    have := ((hS0.pow i).mul hP0).mul (JetGE.of_pint (k := s) hR)
    exact this.mono (le_of_eq (by ring))
  have hnd0 := nd0_jet n s h8 h3 hs6 hs _ _ hJ0
  rw [hz]
  have hzero := sum_ownTerm n p s μ i L (orthA (cLoc L) μ) R horth
  have hsum : ∑ l ∈ range L, nodeT (p := p) n K σ cl τu τv (s + (l + 1) * p)
        (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) + ndT n s (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) =
      ∑ l ∈ range L, (nodeT (p := p) n K σ cl τu τv (s + (l + 1) * p)
        (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) - ownTerm n p s μ i (orthA (cLoc L) μ) R (l + 1)) +
      ndT n s (sX s ^ i * shiftP p μ s (orthA (cLoc L) μ) * R) := by
    rw [Finset.sum_sub_distrib, hzero]; ring
  rw [hsum]
  refine (GV.sum fun l hl => ?_).add (hnd0.mono (by omega))
  have hl' := Finset.mem_range.1 hl
  exact own_node_step n K σ cl τu τv h8 h3 s hs L hL1 hK μ _ hA hAd R hR i (l + 1) (by omega) (by omega)

end OwnPair

end

end CatalanCore.Lai
