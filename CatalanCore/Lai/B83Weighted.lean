module

public import CatalanCore.Lai.ContentL2Main
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# `CatalanCore.Lai.B83Weighted`: weighted entry bounds for Theorem B83 (ledger LB02)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.3.  Band `8n/3 < p < 3n - 1`, window class `W = D`
(`μ_W = 0`).  The Gram entries of `L_n` are `a·A + b·B + X·C`; the existing `entry_bound` gives
`v(B) ≥ thr`.  Here:

* **channels**: `chA n k F` (the coefficient of `a` at the node `k`) and `chX n k F` (the coefficient of
  `X`), as elements of `MPT`; `ndT = a·chA + b·chB + X·chX` (`ndT_channels`);
* **pass bounds** (`chA_ge`, `chX_ge`): `GV (σ - 3 + e)` and `GV (σ + e)` at every node;
* **a-jet** (`chA_jet`): the a-channel of a node to relative order `p` (the `λ₀` correction);
* **window sums** for both channels (analogues of `wsum_core`, `wsum_first`, `wsum_second`), reusing
  the scalar facts `hb1, hb2, hb3` of `ContentL2Sum`;
* **entry assembly** (`entry_chan`) and the weighted entry bound.
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid

namespace CatalanCore.Lai

noncomputable section

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Part 1: channels -/

/-- the `a`-channel of the node `k`: the coefficient of `a` in `ndT n k F`. -/
def chA (n k : ℕ) (F : MPT[X]) : MPT :=
  MvPolynomial.C (laiCoef n k : ℚ) *
    (MvPolynomial.C (-3 * Hq 2 k) * devk k F +
      MvPolynomial.C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * evk k F)

/-- the `b`-channel of the node `k` (not used for bounds; for the decomposition). -/
def chB (n k : ℕ) (F : MPT[X]) : MPT :=
  MvPolynomial.C (laiCoef n k : ℚ) *
    (MvPolynomial.C (-2 * Hq 3 k) * devk k F +
      MvPolynomial.C (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * evk k F)

/-- the `X`-channel of the node `k`: the coefficient of `X` in `ndT n k F`. -/
def chX (n k : ℕ) (F : MPT[X]) : MPT :=
  MvPolynomial.C (6 * (laiCoef n k : ℚ)) * evk k F

theorem ndT_channels (n k : ℕ) (F : MPT[X]) :
    ndT n k F = aT * chA n k F + bT * chB n k F + xT * chX n k F := by
  unfold ndT chA chB chX
  rw [ren_C, ren_laiU, ren_laiV]
  simp only [map_mul, map_sub, map_ofNat]
  ring

/-! ### Part 2: integrality of the digits -/

lemma pz (a b : ℤ) : (p : ℚ) ^ a * (p : ℚ) ^ b = (p : ℚ) ^ (a + b) :=
  (zpow_add₀ (p_ne_zero' (p := p)) a b).symm

lemma Hq_scaled (j k : ℕ) (hk : k < p ^ 2) : (p : ℚ) ^ j * Hq j k ∈ LocRing p := by
  have hp0 := p_ne_zero' (p := p)
  have hlt : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using hk
  have h1 := Hq_digit_lead (p := p) j k
  have h2 := Hq_mem (p := p) j (k / p) hlt
  have e : (p : ℚ) ^ j * Hq j k = Hq j (k / p) + (p : ℚ) ^ j * (Hq j k - ((p : ℚ) ^ j)⁻¹ * Hq j (k / p)) := by
    field_simp; ring
  rw [e]
  exact (LocRing p).add_mem h2 ((LocRing p).mul_mem (natPow_mem j) h1)

lemma laiH_scaled {n : ℕ} (h8 : 8 * n < p ^ 2) (k : ℕ) (hk : k ≤ 6 * n) :
    (p : ℚ) * laiH n k ∈ LocRing p := by
  have h1 := laiH_split (p := p) n k
  have h2 := delta_mem (p := p) n k h8 hk
  have hp0 := p_ne_zero' (p := p)
  have e : (p : ℚ) * laiH n k = (p : ℚ) * (laiH n k + (p : ℚ)⁻¹ * laiDelta n p k) - laiDelta n p k := by
    field_simp; ring
  rw [e]
  exact (LocRing p).sub_mem ((LocRing p).mul_mem lp h1) h2

lemma GV_cm {e0 e : ℤ} (x : ℚ) (hx : (p : ℚ) ^ (-e0) * x ∈ LocRing p) {f : MPT} (hf : GV p e f) :
    GV p (e0 + e) (MvPolynomial.C x * f) := GV.const_mul hx hf

/-! ### Part 3: pass bounds -/

/-- **The `a`-channel pass bound.** -/
theorem chA_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) {e : ℤ} {F : MPT[X]}
    (hF : JetGE p k e F) : GV p ((sig n p (k % p) : ℤ) - 3 + e) (chA n k F) := by
  have hp0 := p_ne_zero' (p := p)
  obtain ⟨u, hu, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  set σ : ℤ := (sig n p (k % p) : ℤ) with hσ
  have hk2 : k < p ^ 2 := by omega
  have hH2 := Hq_scaled (p := p) 2 k hk2
  have hH3 := Hq_scaled (p := p) 3 k hk2
  have hLH := laiH_scaled (p := p) h8 k hk
  have hc : (laiCoef n k : ℚ) = (p : ℚ) ^ σ * u := by
    rw [hu]; push_cast; rw [hσ, zpow_natCast]
  have hdk : MvPolynomial.C (-3 * Hq 2 k) * devk k F =
      MvPolynomial.C (-3 * Hq 2 k * (p : ℚ)⁻¹) * (MvPolynomial.C (p : ℚ) * devk k F) := by
    rw [← mul_assoc, ← map_mul]; congr 2; field_simp
  unfold chA
  rw [hdk, hc]
  have t1 : GV p (σ - 3 + e) (MvPolynomial.C ((p : ℚ) ^ σ * u * (-3 * Hq 2 k * (p : ℚ)⁻¹)) *
      (MvPolynomial.C (p : ℚ) * devk k F)) := by
    refine GV_cm (e0 := σ - 3) _ ?_ hF.2
    have : (p : ℚ) ^ (-(σ - 3)) * ((p : ℚ) ^ σ * u * (-3 * Hq 2 k * (p : ℚ)⁻¹)) =
        (u : ℚ) * (-3 * ((p : ℚ) ^ 2 * Hq 2 k)) := by
      have e1 : (p : ℚ) ^ (-(σ - 3)) * (p : ℚ) ^ σ = (p : ℚ) ^ 3 := by
        rw [pz]; ring_nf; simp
      calc (p : ℚ) ^ (-(σ - 3)) * ((p : ℚ) ^ σ * u * (-3 * Hq 2 k * (p : ℚ)⁻¹))
          = ((p : ℚ) ^ (-(σ - 3)) * (p : ℚ) ^ σ) * ((u : ℚ) * (-3 * Hq 2 k) * (p : ℚ)⁻¹) := by ring
        _ = (p : ℚ) ^ 3 * ((u : ℚ) * (-3 * Hq 2 k) * (p : ℚ)⁻¹) := by rw [e1]
        _ = _ := by field_simp
    rw [this]
    exact (LocRing p).mul_mem (natq_mem u) ((LocRing p).mul_mem lm3 hH2)
  have t2 : GV p (σ - 3 + e) (MvPolynomial.C ((p : ℚ) ^ σ * u * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k)) *
      evk k F) := by
    refine GV_cm (e0 := σ - 3) _ ?_ hF.1
    have : (p : ℚ) ^ (-(σ - 3)) * ((p : ℚ) ^ σ * u * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k)) =
        (u : ℚ) * (3 * ((p : ℚ) * laiH n k) * ((p : ℚ) ^ 2 * Hq 2 k) - 6 * ((p : ℚ) ^ 3 * Hq 3 k)) := by
      have e1 : (p : ℚ) ^ (-(σ - 3)) * (p : ℚ) ^ σ = (p : ℚ) ^ 3 := by
        rw [pz]; ring_nf; simp
      calc (p : ℚ) ^ (-(σ - 3)) * ((p : ℚ) ^ σ * u * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k))
          = ((p : ℚ) ^ (-(σ - 3)) * (p : ℚ) ^ σ) * ((u : ℚ) * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k)) := by ring
        _ = (p : ℚ) ^ 3 * ((u : ℚ) * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k)) := by rw [e1]
        _ = _ := by ring
    rw [this]
    exact (LocRing p).mul_mem (natq_mem u) ((LocRing p).sub_mem
      ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hLH) hH2) ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) hH3))
  have := t1.add t2
  have e2 : MvPolynomial.C ((p : ℚ) ^ σ * u) * (MvPolynomial.C (-3 * Hq 2 k * (p : ℚ)⁻¹) *
        (MvPolynomial.C (p : ℚ) * devk k F) + MvPolynomial.C (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * evk k F) =
      MvPolynomial.C ((p : ℚ) ^ σ * u * (-3 * Hq 2 k * (p : ℚ)⁻¹)) * (MvPolynomial.C (p : ℚ) * devk k F) +
      MvPolynomial.C ((p : ℚ) ^ σ * u * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k)) * evk k F := by
    simp only [map_mul]; ring
  rw [e2]
  exact this

/-- **The `X`-channel pass bound.** -/
theorem chX_ge (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) {e : ℤ} {F : MPT[X]}
    (hF : JetGE p k e F) : GV p ((sig n p (k % p) : ℤ) + e) (chX n k F) := by
  obtain ⟨u, hu, -⟩ := laiCoef_unit (p := p) h8 h3 k hk
  unfold chX
  refine GV_cm (e0 := (sig n p (k % p) : ℤ)) _ ?_ hF.1
  have hp0 := p_ne_zero' (p := p)
  have : (p : ℚ) ^ (-((sig n p (k % p) : ℤ))) * (6 * (laiCoef n k : ℚ)) = 6 * (u : ℚ) := by
    rw [hu]; push_cast
    rw [mul_left_comm, ← mul_assoc, zpow_neg, zpow_natCast]
    field_simp
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) (natq_mem u)


/-! ### Part 4: the `a`-jet (relative order `p`) -/

/-- Main term of `chA n k F` (relative order `p`): `p^{σ-3} u [u^a f₁ + v^a f₀] - p^{σ-2} u λ₀ u^a f₀`,
with `f₀ = F(-k)`, `f₁ = p F'(-k)`. -/
def chAJet (σ : ℤ) (n p k u : ℕ) (f0 f1 : MPT) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ (σ - 3) * u) *
      (MvPolynomial.C (uaL (k / p)) * f1 + MvPolynomial.C (vaL n p k (k / p)) * f0) -
    MvPolynomial.C ((p : ℚ) ^ (σ - 2) * u * lam0 n p (k % p) * uaL (k / p)) * f0

lemma zpow_shift3 (σ : ℤ) : (p : ℚ) ^ (σ - 2) = (p : ℚ) ^ (σ - 3) * p ∧
    (p : ℚ) ^ (σ - 1) = (p : ℚ) ^ (σ - 3) * p ^ 2 ∧ (p : ℚ) ^ σ = (p : ℚ) ^ (σ - 3) * p ^ 3 := by
  have hp0 := p_ne_zero' (p := p)
  refine ⟨?_, ?_, ?_⟩
  · rw [show σ - 2 = (σ - 3) + 1 by ring, zpow_add₀ hp0, zpow_one]
  · rw [show σ - 1 = (σ - 3) + 2 by ring, zpow_add₀ hp0]; norm_cast
  · rw [show σ = (σ - 3) + 3 by ring, zpow_add₀ hp0]; norm_cast
    congr 1; ring_nf

/-- The pure field identities behind the `a`-jet. -/
lemma chA_coeffs {q δ lam E h2 h3 I2 I3 H Hk2 Hk3 : ℚ} (hq : q ≠ 0)
    (eH : H = -(q⁻¹ * δ) + lam + q * E) (e2 : Hk2 = (q ^ 2)⁻¹ * h2 + I2)
    (e3 : Hk3 = (q ^ 3)⁻¹ * h3 + I3) :
    (-3 * Hk2) * q⁻¹ = (q ^ 3)⁻¹ * (-3 * h2) + q⁻¹ * (-3 * I2) ∧
    (3 * H * Hk2 - 6 * Hk3) = (q ^ 3)⁻¹ * (-3 * (δ * h2 + 2 * h3)) + (q ^ 2)⁻¹ * (-lam * (-3 * h2)) +
      (q⁻¹ * (3 * E * h2 - 3 * δ * I2) + (3 * lam * I2 - 6 * I3 + 3 * q * E * I2)) := by
  subst eH e2 e3
  constructor <;> (field_simp; ring)


/-- **The `a`-jet.**  `chA n k F - chAJet` has `GV (σ - 1 + e)` when `ν_k(F) ≥ e`. -/
theorem chA_jet (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (u : ℕ)
    (hu : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u) {e : ℤ} {F : MPT[X]}
    (hF : JetGE p k e F) :
    GV p ((sig n p (k % p) : ℤ) - 1 + e)
      (chA n k F - chAJet (sig n p (k % p) : ℤ) n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F)) := by
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
  have hh2 := Hq_mem (p := p) 2 (k / p) hkp
  have hh3 := Hq_mem (p := p) 3 (k / p) hkp
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ = (sig n p (k % p) : ℤ) := ⟨_, rfl⟩
  rw [← hσ]
  obtain ⟨z2, z1, z0⟩ := zpow_shift3 (p := p) σ
  obtain ⟨Q, hQ⟩ : ∃ Q : ℚ, Q = (p : ℚ) ^ (σ - 3) := ⟨_, rfl⟩
  rw [← hQ] at z2 z1 z0
  have hc : (laiCoef n k : ℚ) = Q * (p : ℚ) ^ 3 * u := by
    rw [hu, ← z0, ← zpow_natCast, hσ]
  set B2 : ℚ := 3 * E * Hq 2 (k / p) - 3 * laiDelta n p k * I2 with hB2
  set B3 : ℚ := 3 * lam0 n p (k % p) * I2 - 6 * I3 + 3 * p * E * I2 with hB3
  have hf1 : MvPolynomial.C (p : ℚ) * devk k F = MvPolynomial.C (p : ℚ) * devk k F := rfl
  have key : chA n k F - chAJet σ n p k u (evk k F) (MvPolynomial.C (p : ℚ) * devk k F) =
      MvPolynomial.C ((laiCoef n k : ℚ) * (-3 * Hq 2 k) - Q * u * uaL (k / p) * p) * devk k F +
      MvPolynomial.C ((laiCoef n k : ℚ) * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) - Q * u * vaL n p k (k / p) +
        Q * p * u * lam0 n p (k % p) * uaL (k / p)) * evk k F := by
    unfold chA chAJet
    rw [z2, ← hQ]
    simp only [map_mul, map_sub, map_add]
    ring
  have s1 : (laiCoef n k : ℚ) * (-3 * Hq 2 k) - Q * u * uaL (k / p) * p =
      Q * (p : ℚ) ^ 3 * u * (-3 * I2) := by
    unfold uaL
    rw [hc, e2]; field_simp; ring
  have s0 : (laiCoef n k : ℚ) * (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) - Q * u * vaL n p k (k / p) +
        Q * p * u * lam0 n p (k % p) * uaL (k / p) = Q * (p : ℚ) ^ 2 * u * (B2 + p * B3) := by
    unfold uaL vaL
    rw [hc, eH, e2, e3]; field_simp; ring
  rw [key, s1, s0]
  have hQ0 : Q ≠ 0 := by rw [hQ]; exact zpow_ne_zero _ hp0
  have e1 : (p : ℚ) ^ (-(σ - 1)) * (Q * (p : ℚ) ^ 2) = 1 := by
    rw [zpow_neg, z1]; field_simp
  have hm1 : GV p (σ - 1 + e) (MvPolynomial.C (Q * (p : ℚ) ^ 3 * u * (-3 * I2)) * devk k F) := by
    have e5 : MvPolynomial.C (Q * (p : ℚ) ^ 3 * u * (-3 * I2)) * devk k F =
        MvPolynomial.C (Q * (p : ℚ) ^ 2 * u * (-3 * I2)) * (MvPolynomial.C (p : ℚ) * devk k F) := by
      rw [show Q * (p : ℚ) ^ 3 * u * (-3 * I2) = (Q * (p : ℚ) ^ 2 * u * (-3 * I2)) * p by ring, map_mul]
      ring
    rw [e5]
    refine GV_cm (e0 := σ - 1) _ ?_ hF.2
    have : (p : ℚ) ^ (-(σ - 1)) * (Q * (p : ℚ) ^ 2 * u * (-3 * I2)) = u * (-3 * I2) := by
      calc _ = ((p : ℚ) ^ (-(σ - 1)) * (Q * (p : ℚ) ^ 2)) * (u * (-3 * I2)) := by ring
        _ = _ := by rw [e1, one_mul]
    rw [this]
    exact (LocRing p).mul_mem (natq_mem u) ((LocRing p).mul_mem lm3 hI2)
  have hm0 : GV p (σ - 1 + e) (MvPolynomial.C (Q * (p : ℚ) ^ 2 * u * (B2 + p * B3)) * evk k F) := by
    refine GV_cm (e0 := σ - 1) _ ?_ hF.1
    have : (p : ℚ) ^ (-(σ - 1)) * (Q * (p : ℚ) ^ 2 * u * (B2 + p * B3)) = u * (B2 + p * B3) := by
      calc _ = ((p : ℚ) ^ (-(σ - 1)) * (Q * (p : ℚ) ^ 2)) * (u * (B2 + p * B3)) := by ring
        _ = _ := by rw [e1, one_mul]
    rw [this]
    refine (LocRing p).mul_mem (natq_mem u) ((LocRing p).add_mem ?_ ((LocRing p).mul_mem lp ?_))
    · exact (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hE) hh2)
        ((LocRing p).mul_mem ((LocRing p).mul_mem l3 hδ) hI2)
    · refine (LocRing p).add_mem ((LocRing p).sub_mem ((LocRing p).mul_mem
        ((LocRing p).mul_mem l3 hlam) hI2) ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) 6) hI3))
        ((LocRing p).mul_mem ((LocRing p).mul_mem ((LocRing p).mul_mem l3 lp) hE) hI2)
  exact hm1.add hm0


/-! ### Part 5: the per-node algebra of the window (`a`- and `X`-channels) -/

section StepAlg

/-- `LHS - RHS` of the second-order node congruence of the `a`-channel, over any commutative ring.
`u = κ (ĉ (1 + p ℓ λ₀) + p² ε) + p² w`, `R_k = R₀ - pℓ R₁ + p² t₂`, `R_k' = R₁ + p t₁`. -/
def stepAlg {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va : S) : S :=
  (kap * (cb + pi * cb * l * lam + pi ^ 2 * ce) + pi ^ 2 * w) *
      (ua * (2 * A0 * A1 * (R0 - pi * l * R1 + pi ^ 2 * t2) + pi * (A0 ^ 2 * (R1 + pi * t1))) +
        va * (A0 ^ 2 * (R0 - pi * l * R1 + pi ^ 2 * t2)) -
        pi * lam * ua * (A0 ^ 2 * (R0 - pi * l * R1 + pi ^ 2 * t2))) -
    kap * cb * (R0 * (ua * (2 * A0 * A1) + va * A0 ^ 2) +
      pi * ((lam * R0 - R1) * (l * (ua * (2 * A0 * A1) + va * A0 ^ 2)) + R1 * (ua * A0 ^ 2) -
        lam * R0 * (ua * A0 ^ 2)))

/-- the quotient `Z` of `stepAlg` by `pi²`. -/
def stepZ {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va : S) : S :=
  let Φ := ua * (2 * A0 * A1) + va * A0 ^ 2
  let Ψ := ua * A0 ^ 2
  let u0 := kap * cb
  let u1 := kap * cb * l * lam
  let u2 := kap * ce + w
  let B0 := Φ * R0
  let B1 := -l * Φ * R1 + Ψ * R1 - lam * Ψ * R0
  let B2 := Φ * t2 + Ψ * t1 + l * lam * Ψ * R1
  let B3 := -lam * Ψ * t2
  (u0 * B2 + u1 * B1 + u2 * B0) + pi * (u0 * B3 + u1 * B2 + u2 * B1) + pi ^ 2 * (u1 * B3 + u2 * B2) +
    pi ^ 3 * (u2 * B3)

lemma stepAlg_eq {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va : S) :
    stepAlg pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va =
      pi ^ 2 * stepZ pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va := by
  unfold stepAlg stepZ
  ring

lemma stepAlg_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va : S) :
    f (stepZ pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va) =
      stepZ (f pi) (f kap) (f cb) (f ce) (f w) (f l) (f lam) (f R0) (f R1) (f t1) (f t2) (f A0) (f A1)
        (f ua) (f va) := by
  unfold stepZ
  simp only [map_mul, map_add, map_sub, map_neg, map_pow, map_ofNat]

lemma stepAlg_GV {pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va : MPT}
    (hpi : GV p 0 pi) (h1 : GV p 0 kap) (h2 : GV p 0 cb) (h3 : GV p 0 ce) (h4 : GV p 0 w)
    (h5 : GV p 0 l) (h6 : GV p 0 lam) (h7 : GV p 0 R0) (h8 : GV p 0 R1) (h9 : GV p 0 t1)
    (h10 : GV p 0 t2) (h11 : GV p 0 A0) (h12 : GV p 0 A1) (h13 : GV p 0 ua) (h14 : GV p 0 va) :
    GV p 0 (stepZ pi kap cb ce w l lam R0 R1 t1 t2 A0 A1 ua va) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : GV0 p, Z = stepZ (⟨pi, hpi⟩ : GV0 p) ⟨kap, h1⟩ ⟨cb, h2⟩ ⟨ce, h3⟩ ⟨w, h4⟩ ⟨l, h5⟩
      ⟨lam, h6⟩ ⟨R0, h7⟩ ⟨R1, h8⟩ ⟨t1, h9⟩ ⟨t2, h10⟩ ⟨A0, h11⟩ ⟨A1, h12⟩ ⟨ua, h13⟩ ⟨va, h14⟩ := ⟨_, rfl⟩
  have hmap := congrArg (GV0 p).subtype hZ
  rw [stepAlg_map] at hmap
  simp only [Subring.subtype_apply] at hmap
  rw [← hmap]
  exact Z.2

end StepAlg


/-! ### Part 6: the `a`-channel at a window node -/

section NodeA

/-- The per-node main term of the `a`-channel (relative order `p`) at the window residue `s`,
for `F = P_s² R`. -/
def termA (n p s μ : ℕ) (kap : ℕ → ℚ) (A R : MPT[X]) (ℓ : ℕ) : MPT :=
  MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 3) * (cbarZ n p s : ℚ)) *
    (MvPolynomial.C (kap ℓ) *
      (R.eval (MvPolynomial.C (-(s : ℚ))) *
          (MvPolynomial.C (uaL ℓ) * (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) *
              (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) +
            MvPolynomial.C (vaL n p (s + ℓ * p) ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2) +
        MvPolynomial.C (p : ℚ) *
          ((MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) -
              (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) *
            (MvPolynomial.C (ℓ : ℚ) *
              (MvPolynomial.C (uaL ℓ) * (2 * A.eval (MvPolynomial.C (-(ℓ : ℚ))) *
                  (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ)))) +
                MvPolynomial.C (vaL n p (s + ℓ * p) ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2)) +
            (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) *
              (MvPolynomial.C (uaL ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2) -
            MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) *
              (MvPolynomial.C (uaL ℓ) * (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2))))

/-- `∑_ℓ termA = p^{σ+2μ-3} ĉ { R(-s) 𝓛^a(A²) + p (R'(-s) - λ₀ R(-s)) 𝓛^a(y A²) }`. -/
theorem sum_termA (n p s L μ : ℕ) (kap : ℕ → ℚ) (A R : MPT[X]) :
    ∑ l ∈ range L, termA n p s μ kap A R (l + 1) =
      MvPolynomial.C ((p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ - 3) * (cbarZ n p s : ℚ)) *
        (R.eval (MvPolynomial.C (-(s : ℚ))) * locAk n p s L kap (A ^ 2) +
          MvPolynomial.C (p : ℚ) * ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) -
              MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ)))) *
            locAk n p s L kap (Polynomial.X * A ^ 2)) := by
  unfold locAk
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold termA
  rw [eval_deriv_sq, eval_deriv_XA2]
  simp only [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_X, map_neg]
  ring


/-- One node `0 ≤ ℓ ≤ L` of the `a`-channel at a window residue:
`chA_k(P_s² R) ≡ termA_ℓ` modulo `p^{σ+2μ-1}`. -/
theorem nodeA_step (n : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ)
    (hL1 : s + L * p ≤ 6 * n) (μ : ℕ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (R : MPT[X]) (hR : PInt p R) (ℓ : ℕ) (hℓL : ℓ ≤ L) :
    GV p ((sig n p s : ℤ) + 2 * μ - 1)
      (chA n (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  have hkmod : (s + ℓ * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hkdiv : (s + ℓ * p) / p = ℓ := by
    rw [Nat.add_mul_div_right _ _ hpp, Nat.div_eq_of_lt hs, zero_add]
  have hk6 : s + ℓ * p ≤ 6 * n := by
    have : ℓ * p ≤ L * p := Nat.mul_le_mul_right p hℓL
    omega
  have hq6 : ℓ + bflag n p s ≤ q6 n p := by
    obtain ⟨h1, -, -⟩ := sub_div_mod p (6 * n) (s + ℓ * p) hpp hk6
    rw [hkdiv, hkmod] at h1
    exact h1
  have hkp : ℓ < p := by
    have : (s + ℓ * p) / p < p := by
      rw [Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show s + ℓ * p < p ^ 2 by omega)
    rwa [hkdiv] at this
  have hP := JetGE.shiftP (p := p) μ s ℓ hA hAd
  have hJ : JetGE p (s + ℓ * p) (2 * μ) (shiftP p μ s A ^ 2 * R) := by
    have := (hP.mul hP).mul (JetGE.of_pint (k := s + ℓ * p) hR)
    rw [pow_two]
    exact this.mono (le_of_eq (by ring))
  obtain ⟨u, hu, hU⟩ := laiCoef_kc_p2 (p := p) h8 h3 (s + ℓ * p) hk6
  rw [hkmod] at hu
  rw [hkmod, hkdiv] at hU
  have hu2 : (laiCoef n (s + ℓ * p) : ℚ) = (p : ℚ) ^ (sig n p s) * u := by exact_mod_cast hu
  have h1 := chA_jet n (s + ℓ * p) h8 h3 hk6 u (by rw [hkmod]; exact hu2) hJ
  rw [hkmod] at h1
  -- the unit part
  obtain ⟨w, hw⟩ : ((p : ℤ) ^ 2) ∣ (u : ℤ) - kapZ n p (bflag n p s) (eflag n p s) ℓ * clZ n p ℓ s := by
    have h0 : (((u : ℤ) - kapZ n p (bflag n p s) (eflag n p s) ℓ * clZ n p ℓ s : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast; rw [hU]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 h0
    simpa using this
  have hwq : (u : ℚ) - (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ) * (clZ n p ℓ s : ℚ) =
      (p : ℚ) ^ 2 * (w : ℚ) := by exact_mod_cast hw
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
  have e_Rk2 : devk (s + ℓ * p) R = (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ))) +
      MvPolynomial.C (p : ℚ) * t1 := by
    rw [ht1def, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one, one_mul]; ring
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ = (sig n p s : ℤ) := ⟨_, rfl⟩
  rw [← hσ] at h1 ⊢
  obtain ⟨z2, z1, z0⟩ := zpow_shift3 (p := p) σ
  have hq : (p : ℚ) ^ (σ + 2 * μ - 3) = (p : ℚ) ^ (σ - 3) * (p : ℚ) ^ (2 * μ) := by
    rw [show σ + 2 * (μ : ℤ) - 3 = (σ - 3) + ((2 * μ : ℕ) : ℤ) by push_cast; ring, zpow_add₀ hp0, zpow_natCast]
  have hu_eq : (u : ℚ) = (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ) *
      ((cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s) + (p : ℚ) ^ 2 * ce) + (p : ℚ) ^ 2 * w := by
    have := hwq; rw [e_cl] at this; linarith
  have hid : chAJet σ n p (s + ℓ * p) u (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
      termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ =
      MvPolynomial.C ((p : ℚ) ^ (σ - 3) * (p : ℚ) ^ (2 * μ)) *
        stepAlg (MvPolynomial.C (p : ℚ)) (MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ))
          (MvPolynomial.C (cbarZ n p s : ℚ)) (MvPolynomial.C ce) (MvPolynomial.C (w : ℚ))
          (MvPolynomial.C (ℓ : ℚ)) (MvPolynomial.C (lam0 n p s)) (R.eval (MvPolynomial.C (-(s : ℚ))))
          ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) t1 t2
          (A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ((Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ))))
          (MvPolynomial.C (uaL ℓ)) (MvPolynomial.C (vaL n p (s + ℓ * p) ℓ)) := by
    rw [evk_P_sq _ _ _ _ _ _ hAd, devk_P_sq _ _ _ _ _ _ hAd]
    unfold chAJet termA stepAlg
    simp only [hkmod, hkdiv]
    rw [← hσ, z2, hq, hu_eq, e_Rk, e_Rk2]
    simp only [map_mul, map_add, map_sub, map_pow, map_one, map_natCast]
    ring
  have hZ := stepAlg_GV (p := p) (pi := MvPolynomial.C (p : ℚ))
    (kap := MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ))
    (cb := MvPolynomial.C (cbarZ n p s : ℚ)) (ce := MvPolynomial.C ce) (w := MvPolynomial.C (w : ℚ))
    (l := MvPolynomial.C (ℓ : ℚ)) (lam := MvPolynomial.C (lam0 n p s))
    (R0 := R.eval (MvPolynomial.C (-(s : ℚ))))
    (R1 := (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) (t1 := t1) (t2 := t2)
    (A0 := A.eval (MvPolynomial.C (-(ℓ : ℚ))))
    (A1 := (Polynomial.derivative A).eval (MvPolynomial.C (-(ℓ : ℚ))))
    (ua := MvPolynomial.C (uaL ℓ)) (va := MvPolynomial.C (vaL n p (s + ℓ * p) ℓ))
    GV0_Cp (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (kapZ n p (bflag n p s) (eflag n p s) ℓ)))
    (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (cbarZ n p s))) (GV.const_loc hce)
    (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) w)) (GV.const_loc (natq_mem ℓ))
    (GV.const_loc (lam0_mem (p := p) n s hs)) (GV_eval hR ((LocRing p).neg_mem (natq_mem s)))
    (GV_eval (PInt_derivative hR) ((LocRing p).neg_mem (natq_mem s))) ht1 ht2
    (GV_eval hA ((LocRing p).neg_mem (natq_mem ℓ)))
    (GV_eval (PInt_derivative hA) ((LocRing p).neg_mem (natq_mem ℓ)))
    (GV.const_loc (uaL_mem (p := p) ℓ hkp)) (GV.const_loc (vaL_mem (p := p) h8 (s + ℓ * p) ℓ hk6 hkp))
  have hCq : GV p (σ + 2 * μ - 3) (MvPolynomial.C ((p : ℚ) ^ (σ - 3) * (p : ℚ) ^ (2 * μ)) : MPT) := by
    refine GV_C_eq (y := 1) ?_ (LocRing p).one_mem
    rw [mul_one, ← hq]
  have h2 : GV p (σ + 2 * μ - 1) (chAJet σ n p (s + ℓ * p) u (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
      termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by
    rw [hid, stepAlg_eq]
    have hpi : GV p 1 (MvPolynomial.C (p : ℚ) : MPT) := by
      simpa using GV_Cp_mul (p := p) (e := 0) (GV.one (σ := TVar))
    have := hCq.mul ((hpi.pow 2).mul hZ)
    refine this.mono ?_
    omega
  have hsum : chA n (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ =
      (chA n (s + ℓ * p) (shiftP p μ s A ^ 2 * R) - chAJet σ n p (s + ℓ * p) u
        (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))) +
      (chAJet σ n p (s + ℓ * p) u (evk (s + ℓ * p) (shiftP p μ s A ^ 2 * R))
        (MvPolynomial.C (p : ℚ) * devk (s + ℓ * p) (shiftP p μ s A ^ 2 * R)) -
      termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by ring
  rw [hsum]
  exact (h1.mono (le_of_eq (by ring))).add h2


end NodeA

/-! ### Part 7: the `X`-channel at a window node -/

section NodeX

/-- `LHS - RHS` of the second-order node congruence of the `X`-channel. -/
def stepAlgX {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t2 : S) : S :=
  (kap * (cb + pi * cb * l * lam + pi ^ 2 * ce) + pi ^ 2 * w) * (R0 - pi * l * R1 + pi ^ 2 * t2) -
    kap * cb * (R0 + pi * l * (lam * R0 - R1))

def stepZX {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t2 : S) : S :=
  let u0 := kap * cb
  let u1 := kap * cb * l * lam
  let u2 := kap * ce + w
  (u2 * R0 + u0 * t2 - u1 * l * R1) + pi * (-(u2 * l * R1) + u1 * t2) + pi ^ 2 * (u2 * t2)

lemma stepAlgX_eq {S : Type*} [CommRing S] (pi kap cb ce w l lam R0 R1 t2 : S) :
    stepAlgX pi kap cb ce w l lam R0 R1 t2 = pi ^ 2 * stepZX pi kap cb ce w l lam R0 R1 t2 := by
  unfold stepAlgX stepZX
  ring

lemma stepZX_map {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T)
    (pi kap cb ce w l lam R0 R1 t2 : S) :
    f (stepZX pi kap cb ce w l lam R0 R1 t2) =
      stepZX (f pi) (f kap) (f cb) (f ce) (f w) (f l) (f lam) (f R0) (f R1) (f t2) := by
  unfold stepZX
  simp only [map_mul, map_add, map_sub, map_neg, map_pow]

lemma stepZX_GV {pi kap cb ce w l lam R0 R1 t2 : MPT}
    (hpi : GV p 0 pi) (h1 : GV p 0 kap) (h2 : GV p 0 cb) (h3 : GV p 0 ce) (h4 : GV p 0 w)
    (h5 : GV p 0 l) (h6 : GV p 0 lam) (h7 : GV p 0 R0) (h8 : GV p 0 R1) (h10 : GV p 0 t2) :
    GV p 0 (stepZX pi kap cb ce w l lam R0 R1 t2) := by
  obtain ⟨Z, hZ⟩ : ∃ Z : GV0 p, Z = stepZX (⟨pi, hpi⟩ : GV0 p) ⟨kap, h1⟩ ⟨cb, h2⟩ ⟨ce, h3⟩ ⟨w, h4⟩
      ⟨l, h5⟩ ⟨lam, h6⟩ ⟨R0, h7⟩ ⟨R1, h8⟩ ⟨t2, h10⟩ := ⟨_, rfl⟩
  have hmap := congrArg (GV0 p).subtype hZ
  rw [stepZX_map] at hmap
  simp only [Subring.subtype_apply] at hmap
  rw [← hmap]
  exact Z.2

/-- The per-node main term of the `X`-channel at the window residue `s`, for `F = P_s² R`. -/
def termX (n p s μ : ℕ) (kap : ℕ → ℚ) (A R : MPT[X]) (ℓ : ℕ) : MPT :=
  MvPolynomial.C (6 * (p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ)) *
    ((A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 *
      (MvPolynomial.C (kap ℓ) * MvPolynomial.C (cbarZ n p s : ℚ) *
        (R.eval (MvPolynomial.C (-(s : ℚ))) +
          MvPolynomial.C (p : ℚ) * MvPolynomial.C (ℓ : ℚ) *
            (MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) -
              (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))))))

/-- `∑_{ℓ=0}^{L} κ_ℓ A(-ℓ)²`. -/
def locXa (L : ℕ) (kap : ℕ → ℚ) (A : MPT[X]) : MPT :=
  ∑ l ∈ range (L + 1), MvPolynomial.C (kap l) * (A.eval (MvPolynomial.C (-(l : ℚ)))) ^ 2

/-- `∑_{ℓ=0}^{L} ℓ κ_ℓ A(-ℓ)²`. -/
def locXb (L : ℕ) (kap : ℕ → ℚ) (A : MPT[X]) : MPT :=
  ∑ l ∈ range (L + 1), MvPolynomial.C (kap l) * MvPolynomial.C (l : ℚ) *
    (A.eval (MvPolynomial.C (-(l : ℚ)))) ^ 2

theorem sum_termX (n p s L μ : ℕ) (kap : ℕ → ℚ) (A R : MPT[X]) :
    ∑ l ∈ range (L + 1), termX n p s μ kap A R l =
      MvPolynomial.C (6 * (p : ℚ) ^ ((sig n p s : ℤ) + 2 * μ) * (cbarZ n p s : ℚ)) *
        (R.eval (MvPolynomial.C (-(s : ℚ))) * locXa L kap A +
          MvPolynomial.C (p : ℚ) * (MvPolynomial.C (lam0 n p s) * R.eval (MvPolynomial.C (-(s : ℚ))) -
              (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) * locXb L kap A) := by
  unfold locXa locXb
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold termX
  simp only [map_mul]
  ring

/-- One node `0 ≤ ℓ ≤ L` of the `X`-channel at a window residue:
`chX_k(P_s² R) ≡ termX_ℓ` modulo `p^{σ+2μ+2}`. -/
theorem nodeX_step (n : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (s : ℕ) (hs : s < p) (L : ℕ)
    (hL1 : s + L * p ≤ 6 * n) (μ : ℕ) (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (R : MPT[X]) (hR : PInt p R) (ℓ : ℕ) (hℓL : ℓ ≤ L) :
    GV p ((sig n p s : ℤ) + 2 * μ + 2)
      (chX n (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
        termX n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ) := by
  have hp0 := p_ne_zero' (p := p)
  have hpp := hp.out.pos
  have hkmod : (s + ℓ * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hkdiv : (s + ℓ * p) / p = ℓ := by
    rw [Nat.add_mul_div_right _ _ hpp, Nat.div_eq_of_lt hs, zero_add]
  have hk6 : s + ℓ * p ≤ 6 * n := by
    have : ℓ * p ≤ L * p := Nat.mul_le_mul_right p hℓL
    omega
  have hq6 : ℓ + bflag n p s ≤ q6 n p := by
    obtain ⟨h1, -, -⟩ := sub_div_mod p (6 * n) (s + ℓ * p) hpp hk6
    rw [hkdiv, hkmod] at h1
    exact h1
  obtain ⟨u, hu, hU⟩ := laiCoef_kc_p2 (p := p) h8 h3 (s + ℓ * p) hk6
  rw [hkmod] at hu
  rw [hkmod, hkdiv] at hU
  have hu2 : (laiCoef n (s + ℓ * p) : ℚ) = (p : ℚ) ^ (sig n p s) * u := by exact_mod_cast hu
  obtain ⟨w, hw⟩ : ((p : ℤ) ^ 2) ∣ (u : ℤ) - kapZ n p (bflag n p s) (eflag n p s) ℓ * clZ n p ℓ s := by
    have h0 : (((u : ℤ) - kapZ n p (bflag n p s) (eflag n p s) ℓ * clZ n p ℓ s : ℤ) : ZMod (p ^ 2)) = 0 := by
      push_cast; rw [hU]; ring
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p ^ 2)).1 h0
    simpa using this
  have hwq : (u : ℚ) - (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ) * (clZ n p ℓ s : ℚ) =
      (p : ℚ) ^ 2 * (w : ℚ) := by exact_mod_cast hw
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
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, σ = (sig n p s : ℤ) := ⟨_, rfl⟩
  rw [← hσ]
  have hu_eq : (u : ℚ) = (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ) *
      ((cbarZ n p s : ℚ) * (1 + (p : ℚ) * ℓ * lam0 n p s) + (p : ℚ) ^ 2 * ce) + (p : ℚ) ^ 2 * w := by
    have := hwq; rw [e_cl] at this; linarith
  have hpow : (p : ℚ) ^ (sig n p s) = (p : ℚ) ^ σ := by rw [hσ, zpow_natCast]
  have hq : (p : ℚ) ^ (σ + 2 * μ) = (p : ℚ) ^ σ * (p : ℚ) ^ (2 * μ) := by
    rw [show σ + 2 * (μ : ℤ) = σ + ((2 * μ : ℕ) : ℤ) by push_cast; ring, zpow_add₀ hp0, zpow_natCast]
  have hid : chX n (s + ℓ * p) (shiftP p μ s A ^ 2 * R) -
      termX n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A R ℓ =
      MvPolynomial.C (6 * (p : ℚ) ^ (σ + 2 * μ)) * ((A.eval (MvPolynomial.C (-(ℓ : ℚ)))) ^ 2 *
        stepAlgX (MvPolynomial.C (p : ℚ)) (MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ))
          (MvPolynomial.C (cbarZ n p s : ℚ)) (MvPolynomial.C ce) (MvPolynomial.C (w : ℚ))
          (MvPolynomial.C (ℓ : ℚ)) (MvPolynomial.C (lam0 n p s)) (R.eval (MvPolynomial.C (-(s : ℚ))))
          ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) t2) := by
    unfold chX termX stepAlgX
    rw [evk_P_sq _ _ _ _ _ _ hAd, hu2, hpow, ← hσ, hq, hu_eq, e_Rk]
    simp only [map_mul, map_add, map_sub, map_pow, map_one, map_natCast, map_ofNat]
    ring
  have hZ := stepZX_GV (p := p) (pi := MvPolynomial.C (p : ℚ))
    (kap := MvPolynomial.C (kapZ n p (bflag n p s) (eflag n p s) ℓ : ℚ))
    (cb := MvPolynomial.C (cbarZ n p s : ℚ)) (ce := MvPolynomial.C ce) (w := MvPolynomial.C (w : ℚ))
    (l := MvPolynomial.C (ℓ : ℚ)) (lam := MvPolynomial.C (lam0 n p s))
    (R0 := R.eval (MvPolynomial.C (-(s : ℚ))))
    (R1 := (Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) (t2 := t2)
    GV0_Cp (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (kapZ n p (bflag n p s) (eflag n p s) ℓ)))
    (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) (cbarZ n p s))) (GV.const_loc hce)
    (GV.const_loc (by exact_mod_cast int_mem_locRing (ℓ := p) w)) (GV.const_loc (natq_mem ℓ))
    (GV.const_loc (lam0_mem (p := p) n s hs)) (GV_eval hR ((LocRing p).neg_mem (natq_mem s)))
    (GV_eval (PInt_derivative hR) ((LocRing p).neg_mem (natq_mem s))) ht2
  have hA0 : GV p 0 (A.eval (MvPolynomial.C (-(ℓ : ℚ))) ^ 2) := by
    simpa using (GV_eval hA ((LocRing p).neg_mem (natq_mem ℓ))).pow 2
  have h6 : GV p (σ + 2 * μ) (MvPolynomial.C (6 * (p : ℚ) ^ (σ + 2 * μ)) : MPT) := by
    refine GV_C_eq (y := 6) (by ring) ?_
    exact_mod_cast int_mem_locRing (ℓ := p) 6
  rw [hid, stepAlgX_eq]
  have hpi : GV p 1 (MvPolynomial.C (p : ℚ) : MPT) := by
    simpa using GV_Cp_mul (p := p) (e := 0) (GV.one (σ := TVar))
  have := h6.mul ((hA0).mul ((hpi.pow 2).mul hZ))
  refine this.mono ?_
  omega

end NodeX


/-! ### Part 8: the window sums of the two channels -/

section WinSums

lemma termA_zero (n p s μ : ℕ) (kap : ℕ → ℚ) (A R : MPT[X]) : termA n p s μ kap A R 0 = 0 := by
  unfold termA uaL vaL
  simp [Hq_zero]

lemma GV0_locXa (L : ℕ) {kap : ℕ → ℚ} (hkap : ∀ l, kap l ∈ LocRing p) {A : MPT[X]} (hA : PInt p A) :
    GV p 0 (locXa L kap A) := by
  unfold locXa
  refine GV.sum fun l _ => GV0_mul (GV.const_loc (hkap l)) ?_
  simpa using (GV_eval hA ((LocRing p).neg_mem (natq_mem l))).pow 2

lemma GV0_locXb (L : ℕ) {kap : ℕ → ℚ} (hkap : ∀ l, kap l ∈ LocRing p) {A : MPT[X]} (hA : PInt p A) :
    GV p 0 (locXb L kap A) := by
  unfold locXb
  refine GV.sum fun l _ => GV0_mul (GV0_mul (GV.const_loc (hkap l)) (GV.const_loc (natq_mem l))) ?_
  simpa using (GV_eval hA ((LocRing p).neg_mem (natq_mem l))).pow 2

/-- **The window sum of the `a`-channel** (analogue of `wsum_core`). -/
theorem wsumA_core {n : ℕ} (h : Rng n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (μ : ℕ) (L : ℕ)
    (hL : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p)
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ) (V : ℤ[X]) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2)
    (hb1 : GV p (m : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)))
    (hb2 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)))
    (hb3 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s))) :
    GV p ((σW : ℤ) + 2 * μ - 3 + m)
      (∑ s ∈ Wf, ∑ l ∈ range (L + 1), chA n (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)) := by
  classical
  rcases Wf.eq_empty_or_nonempty with hW0 | ⟨s0, hs0⟩
  · subst hW0; simpa using GV.zero (p := p) (σ := TVar) _
  have h8 := h.h8
  have h3 : 3 ≤ p := by have := h.p5; omega
  have hsig : ∀ s ∈ Wf, (sig n p s : ℤ) = σW := fun s hs => by rw [((hWf s).1 hs).2]
  have hlt : ∀ s ∈ Wf, s < p := fun s hs => ((hWf s).1 hs).1
  have hkap : ∀ s ∈ Wf, bflag n p s = bflag n p s0 ∧ eflag n p s = eflag n p s0 := fun s hs =>
    flags_of_sig n p s s0 (((hWf s).1 hs).2.trans ((hWf s0).1 hs0).2.symm)
  have hR : ∀ s, PInt p (Rres p μ Wf A V s) := fun s => PInt_Rres μ Wf hA V s
  have hAsq : PInt p (A ^ 2) := hA.pow 2
  have hXA : PInt p (Polynomial.X * A ^ 2) := PInt_X.mul hAsq
  have La0 : GV p 0 (locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2)) :=
    GV0_locAk h8 s0 L (hL s0 hs0).1 (fun l => int_mem_locRing _) hAsq
  have Lx0 : GV p 0 (locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ))
      (Polynomial.X * A ^ 2)) :=
    GV0_locAk h8 s0 L (hL s0 hs0).1 (fun l => int_mem_locRing _) hXA
  -- Step A: node sums against the `termA`
  have hA2 : ∀ s ∈ Wf, GV p ((σW : ℤ) + 2 * μ - 1)
      (∑ l ∈ range (L + 1), chA n (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) -
        ∑ l ∈ range (L + 1), termA n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A
          (Rres p μ Wf A V s) l) := by
    intro s hs
    rw [← Finset.sum_sub_distrib, Rres_eq μ Wf A V hs]
    have := GV.sum (s := range (L + 1)) fun l hl =>
      nodeA_step n h8 h3 s (hlt s hs) L (hL s hs).1 μ A hA hAd (Rres p μ Wf A V s) (hR s) l
        (by have := Finset.mem_range.1 hl; omega)
    rw [hsig s hs] at this
    exact this
  have hsumA := GV.sum (s := Wf) hA2
  rw [Finset.sum_sub_distrib] at hsumA
  -- Step B: the main terms
  have hmain : ∀ s ∈ Wf, ∑ l ∈ range (L + 1), termA n p s μ
        (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A (Rres p μ Wf A V s) l =
      MvPolynomial.C ((p : ℚ) ^ ((σW : ℤ) + 2 * μ - 3)) *
        (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) *
            locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2) +
          MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
              zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
            locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ))
              (Polynomial.X * A ^ 2)) := by
    intro s hs
    rw [Finset.sum_range_succ', termA_zero, add_zero, sum_termA,
      locAk_const h8 s s0 L (hlt s hs) (hlt s0 hs0) (hL s hs).1 (hL s0 hs0).1 (hkap s hs).1 (hkap s hs).2,
      locAk_const h8 s s0 L (hlt s hs) (hlt s0 hs0) (hL s hs).1 (hL s0 hs0).1 (hkap s hs).1 (hkap s hs).2,
      hsig s hs]
    simp only [map_mul, zphi_apply, evk, devk]
    ring
  rw [Finset.sum_congr rfl hmain, ← Finset.mul_sum] at hsumA
  have hcomb : ∑ s ∈ Wf, (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) *
            locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2) +
          MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s) -
              zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
            locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ))
              (Polynomial.X * A ^ 2)) =
      (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) *
          locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) (A ^ 2) +
        MvPolynomial.C (p : ℚ) * ((∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) -
            ∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
          locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ))
            (Polynomial.X * A ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hcomb] at hsumA
  have hm1' : (1 : ℤ) + ((m : ℤ) - 1) = m := by ring
  have t1 := GVm hb1 La0
  have t2 : GV p (m : ℤ) (MvPolynomial.C (p : ℚ) * ((∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) -
            ∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) *
          locAk n p s0 L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ))
            (Polynomial.X * A ^ 2)) := by
    have := GVm (GV1_Cp.mul (hb2.sub hb3)) Lx0
    rwa [hm1'] at this
  have hB := t1.add t2
  have hJ := (GV.const_zpow_mul_iff (p := p) (σ := TVar) (e := (m : ℤ)) (k := (σW : ℤ) + 2 * μ - 3)).2 hB
  have hfin := (GV.mono (e := (σW : ℤ) + 2 * μ - 1) (e' := (σW : ℤ) + 2 * μ - 3 + m) (by omega) hsumA).add
    (GV.mono (e := (m : ℤ) + ((σW : ℤ) + 2 * μ - 3)) (e' := (σW : ℤ) + 2 * μ - 3 + m) (by omega) hJ)
  simpa using hfin


/-- **The window sum of the `X`-channel.** -/
theorem wsumX_core {n : ℕ} (h : Rng n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (μ : ℕ) (L : ℕ)
    (hL : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p)
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ) (V : ℤ[X]) (m : ℕ) (hm1 : 1 ≤ m) (hm2 : m ≤ 2)
    (hb1 : GV p (m : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)))
    (hb2 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)))
    (hb3 : GV p ((m : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s))) :
    GV p ((σW : ℤ) + 2 * μ + m)
      (∑ s ∈ Wf, ∑ l ∈ range (L + 1), chX n (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)) := by
  classical
  rcases Wf.eq_empty_or_nonempty with hW0 | ⟨s0, hs0⟩
  · subst hW0; simpa using GV.zero (p := p) (σ := TVar) _
  have h8 := h.h8
  have h3 : 3 ≤ p := by have := h.p5; omega
  have hsig : ∀ s ∈ Wf, (sig n p s : ℤ) = σW := fun s hs => by rw [((hWf s).1 hs).2]
  have hlt : ∀ s ∈ Wf, s < p := fun s hs => ((hWf s).1 hs).1
  have hkap : ∀ s ∈ Wf, bflag n p s = bflag n p s0 ∧ eflag n p s = eflag n p s0 := fun s hs =>
    flags_of_sig n p s s0 (((hWf s).1 hs).2.trans ((hWf s0).1 hs0).2.symm)
  have hR : ∀ s, PInt p (Rres p μ Wf A V s) := fun s => PInt_Rres μ Wf hA V s
  have Xa0 : GV p 0 (locXa L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A) :=
    GV0_locXa L (fun l => by exact_mod_cast int_mem_locRing (ℓ := p) _) hA
  have Xb0 : GV p 0 (locXb L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A) :=
    GV0_locXb L (fun l => by exact_mod_cast int_mem_locRing (ℓ := p) _) hA
  have hA2 : ∀ s ∈ Wf, GV p ((σW : ℤ) + 2 * μ + 2)
      (∑ l ∈ range (L + 1), chX n (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) -
        ∑ l ∈ range (L + 1), termX n p s μ (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A
          (Rres p μ Wf A V s) l) := by
    intro s hs
    rw [← Finset.sum_sub_distrib, Rres_eq μ Wf A V hs]
    have := GV.sum (s := range (L + 1)) fun l hl =>
      nodeX_step n h8 h3 s (hlt s hs) L (hL s hs).1 μ A hA hAd (Rres p μ Wf A V s) (hR s) l
        (by have := Finset.mem_range.1 hl; omega)
    rw [hsig s hs] at this
    exact this
  have hsumA := GV.sum (s := Wf) hA2
  rw [Finset.sum_sub_distrib] at hsumA
  have hmain : ∀ s ∈ Wf, ∑ l ∈ range (L + 1), termX n p s μ
        (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) A (Rres p μ Wf A V s) l =
      MvPolynomial.C (6 * (p : ℚ) ^ ((σW : ℤ) + 2 * μ)) *
        (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) *
            locXa L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A +
          MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s) -
              zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) *
            locXb L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A) := by
    intro s hs
    rw [sum_termX, (hkap s hs).1, (hkap s hs).2, hsig s hs]
    simp only [map_mul, zphi_apply, evk, devk]
    ring
  rw [Finset.sum_congr rfl hmain, ← Finset.mul_sum] at hsumA
  have hcomb : ∑ s ∈ Wf, (zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s) *
            locXa L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A +
          MvPolynomial.C (p : ℚ) * (zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s) -
              zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) *
            locXb L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A) =
      (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) *
          locXa L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A +
        MvPolynomial.C (p : ℚ) * ((∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) -
            ∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) *
          locXb L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hcomb] at hsumA
  have hm1' : (1 : ℤ) + ((m : ℤ) - 1) = m := by ring
  have t1 := GVm hb1 Xa0
  have t2 : GV p (m : ℤ) (MvPolynomial.C (p : ℚ) * ((∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) * evk s (Rres p μ Wf A V s)) -
            ∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) *
          locXb L (fun l => (kapZ n p (bflag n p s0) (eflag n p s0) l : ℚ)) A) := by
    have := GVm (GV1_Cp.mul (hb3.sub hb2)) Xb0
    rwa [hm1'] at this
  have hB := t1.add t2
  have h6 : GV p ((σW : ℤ) + 2 * μ) (MvPolynomial.C (6 * (p : ℚ) ^ ((σW : ℤ) + 2 * μ)) : MPT) := by
    refine GV_C_eq (y := 6) (by ring) ?_
    exact_mod_cast int_mem_locRing (ℓ := p) 6
  have hJ := h6.mul hB
  have hfin := (GV.mono (e := (σW : ℤ) + 2 * μ + 2) (e' := (σW : ℤ) + 2 * μ + m) (by omega) hsumA).add
    (GV.mono (e := (σW : ℤ) + 2 * μ + (m : ℤ)) (e' := (σW : ℤ) + 2 * μ + m) (by omega) hJ)
  simpa using hfin


end WinSums

/-! ### Part 9: the scalar facts `hb1, hb2, hb3` (copied from `wsum_first`, `wsum_second`) -/

section HB

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

theorem hb_first {n : ℕ} (h : Rng n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ)
    (A : MPT[X]) (hA : PInt p A) (hAd : A.natDegree ≤ μ)
    (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p σW = QhatPoly n p σW * Vneg p V)
    (hGd : G.natDegree ≤ p - 2)
    (hG : ∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0)
    (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s)) :
    GV p ((1 : ℕ) : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) ∧
    GV p (((1 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) ∧
    GV p (((1 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s)) := by
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
  exact ⟨hb1, hb2, hb3⟩

theorem hb_second {n : ℕ} (h : Rng n p) (hx2 : 0 < xtwo n p) (σW : ℕ) (Wf : Finset ℕ)
    (hWf : ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) (hne : Wf.Nonempty)
    (μ : ℕ) (hμ : ∀ r ∈ Wf, mu n p r = μ)
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
    GV p ((2 : ℕ) : ℤ) (∑ s ∈ Wf, zphi (cbarZ n p s) * evk s (Rres p μ Wf A V s)) ∧
    GV p (((2 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * devk s (Rres p μ Wf A V s)) ∧
    GV p (((2 : ℕ) : ℤ) - 1) (∑ s ∈ Wf, zphi (cbarZ n p s) * MvPolynomial.C (lam0 n p s) *
      evk s (Rres p μ Wf A V s)) := by
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
  exact ⟨hb1, hb2, hb3⟩


end HB

/-! ### Part 10: the entry assembly (band: `μ_W = 0`) -/

section Entry

variable {n : ℕ}

lemma sum_nodes_fiber {M : Type*} [AddCommMonoid M] (h : Rng n p) (g : ℕ → M) :
    ∑ k ∈ range (6 * n + 1), g k = ∑ s ∈ range p, ∑ l ∈ range (Lc n p s + 1), g (s + l * p) := by
  have hpp := h.p5
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => k % p) (t := range p)
    (fun k _ => Finset.mem_range.2 (Nat.mod_lt _ (by omega)))]
  refine Finset.sum_congr rfl fun s hs => ?_
  exact mn_sum_fiber h s (Finset.mem_range.1 hs) _

/-- The pass bound at a node, in terms of the potentials (analogue of `mn_node_ok`). -/
lemma node_ok_chan (ω : ℤ) (nf : ℕ → MPT[X] → MPT)
    (hpass : ∀ k, k ≤ 6 * n → ∀ (e : ℤ) (F : MPT[X]), JetGE p k e F →
      GV p ((sig n p (k % p) : ℤ) - 4 + e + ω) (nf k F))
    (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (μ : ℕ) (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (L0 : ℕ) (x y : FIdx n p σW) (s : ℕ) (hs : s < p)
    (l : ℕ) (hl : l ≤ Lc n p s) (hd : defF n p σW x y s ≤ 0) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + ω)
      (nf (s + l * p) (elF n p σW μ (orthA (cLoc L0) μ) x * elF n p σW μ (orthA (cLoc L0) μ) y)) := by
  have hpp := h.p5
  have hAP : PInt p (orthA (cLoc L0) μ) := orthA_pint _ _ (fun i => GV_cLoc _ i)
  have hAd : (orthA (cLoc L0) μ).natDegree ≤ μ := orthA_natDegree_le _ _
  obtain ⟨b1, b2⟩ := mn_Lc_bound h s hs
  have hk6 : s + l * p ≤ 6 * n := by
    have : l * p ≤ Lc n p s * p := Nat.mul_le_mul_right p hl
    omega
  have hkm : (s + l * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  have hj := (fam_jets σW μ hμ hAP hAd x (s + l * p)).mul (fam_jets σW μ hμ hAP hAd y (s + l * p))
  rw [hkm] at hj
  have hnp := hpass (s + l * p) hk6 _ _ hj
  rw [hkm] at hnp
  refine hnp.mono ?_
  unfold defF at hd
  omega

/-- **The weighted entry bound for one channel** (band: the window multiplicity `μ = 0`). -/
theorem entry_chan (ω : ℤ) (nf : ℕ → MPT[X] → MPT)
    (hpass : ∀ k, k ≤ 6 * n → ∀ (e : ℤ) (F : MPT[X]), JetGE p k e F →
      GV p ((sig n p (k % p) : ℤ) - 4 + e + ω) (nf k F))
    (hW1 : ∀ (Wf : Finset ℕ) (σW : ℕ), (∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) → ∀ (μ L : ℕ),
      (∀ r ∈ Wf, mu n p r = μ) → (∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p) →
      ∀ (A : MPT[X]), PInt p A → A.natDegree ≤ μ → ∀ (V : ℤ[X]) (G : (ZMod (p ^ 2))[X]),
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V → G.natDegree ≤ p - 2 →
      (∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) → ∀ Kz : ZMod (p ^ 2),
      (∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s)) →
      GV p ((σW : ℤ) + 2 * μ - 3 + ω)
        (∑ s ∈ Wf, ∑ l ∈ range (L + 1), nf (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)))
    (hW2 : ∀ (Wf : Finset ℕ) (σW : ℕ), (∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW) → Wf.Nonempty → 0 < xtwo n p →
      (lam n p - (σW : ℤ)) % 2 = 0 → ∀ (μ L : ℕ),
      (∀ r ∈ Wf, mu n p r = μ) → (∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p) →
      ∀ (A : MPT[X]), PInt p A → A.natDegree ≤ μ → ∀ (V : ℤ[X]) (G Hr : (ZMod (p ^ 2))[X]),
      G * Epoly n p σW = QhatPoly n p σW * Vneg p V →
      Hr * Epoly n p σW = QhatPoly n p σW * Vneg p (Polynomial.derivative V) →
      G.natDegree ≤ p - 4 → Hr.natDegree ≤ p - 2 →
      (∀ m, m < p → m ∉ Wf → G.eval (m : ZMod (p ^ 2)) = 0) →
      (∀ m, m < p → m ∉ Wf → (Polynomial.derivative G).eval (m : ZMod (p ^ 2)) = 0) →
      (∀ m, m < p → m ∉ Wf → Hr.eval (m : ZMod (p ^ 2)) = 0) → ∀ Kz : ZMod (p ^ 2),
      (∀ s ∈ Wf, fR n p σW s = Kz * Qhat n p σW s * jetp p (xiR n p s)) →
      GV p ((σW : ℤ) + 2 * μ - 2 + ω)
        (∑ s ∈ Wf, ∑ l ∈ range (L + 1), nf (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi)))
    (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + ω)
      (∑ k ∈ range (6 * n + 1), nf k
        (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)) := by
  classical
  have hpp := h.p5
  have hp3 : 3 ≤ p := by omega
  have h8 := h.h8
  obtain ⟨L, hLeq⟩ : ∃ L, L = Lc n p s0 := ⟨_, rfl⟩
  obtain ⟨A, hAeq⟩ : ∃ A, A = orthA (cLoc L) μ := ⟨_, rfl⟩
  rw [← hLeq, ← hAeq]
  have hAP : PInt p A := by rw [hAeq]; exact orthA_pint _ _ (fun i => GV_cLoc _ i)
  have hAd : A.natDegree ≤ μ := by rw [hAeq]; exact orthA_natDegree_le _ _
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Finset ℕ, ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW :=
    ⟨(range p).filter (fun r => sig n p r = σW), fun r => by simp [Finset.mem_filter, Finset.mem_range]⟩
  have hWfe : (range p).filter (fun r => sig n p r = σW) = Wf := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; exact (hWf r).symm
  have hLW : ∀ s ∈ Wf, Lc n p s = L := by
    intro s hs
    obtain ⟨hs1, hs2⟩ := (hWf s).1 hs
    rw [hLeq, mn_Lc_eq, mn_Lc_eq, (mn_flags_of_sig (n := n) (p := p) (s := s) (s' := s0)
      (by rw [hs2, hsW])).1]
  have hLb : ∀ s ∈ Wf, s + L * p ≤ 6 * n ∧ 6 * n < s + (L + 1) * p := by
    intro s hs
    rw [← hLW s hs]
    exact mn_Lc_bound h s ((hWf s).1 hs).1
  have hμW : ∀ r ∈ Wf, mu n p r = μ := fun r hr => hμ r ((hWf r).1 hr).1 ((hWf r).1 hr).2
  have hs0Wf : s0 ∈ Wf := (hWf s0).2 ⟨hs0, hsW⟩
  have hres := resfacts h σW hpar s0 hs0
  have h2mu : 2 * (μ : ℤ) + σW = lam n p + 4 := by
    have := hres.2 hsW
    rw [hμ s0 hs0 hsW, hsW] at this
    exact this
  rw [sum_nodes_fiber h]
  have hTok : ∀ (x y : FIdx n p σW) (s : ℕ), s < p → defF n p σW x y s ≤ 0 →
      GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + ω)
        (∑ l ∈ range (Lc n p s + 1), nf (s + l * p) (elF n p σW μ A x * elF n p σW μ A y)) :=
    fun x y s hs hd => GV.sum fun l hl => by
      have := node_ok_chan ω nf hpass h σW hpar μ hμ L x y s hs l
        (by have := Finset.mem_range.1 hl; omega) hd
      rw [← hAeq] at this
      exact this
  have hrearr : ∀ (g : ℕ → MPT), ∑ s ∈ range p, g s =
      ∑ s ∈ (range p).filter (fun s => sig n p s = σW), g s +
      ∑ s ∈ (range p).filter (fun s => ¬ sig n p s = σW), g s := fun g =>
    (Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = σW) g).symm
  rcases pair_classify h σW hpar x y with hA
    | ⟨r, i, hxe, hrW, hyp, hnown, hdr, hdo⟩ | ⟨r, i, hye, hrW, hxp, hnown, hdr, hdo⟩
    | ⟨c1, c2, c3, c4, hoff, hon⟩ | ⟨c1, c2, c3, hoff, hon⟩
  · rw [hrearr]
    exact (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
        (hA s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1))).add
      (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
        (hA s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)))
  · exfalso
    have hm := mn_mF_W σW μ hμ r r.2 hrW
    have := i.2
    omega
  · exfalso
    have hm := mn_mF_W σW μ hμ r r.2 hrW
    have := i.2
    omega
  · rw [hrearr]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
      (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
    rw [hWfe]
    obtain ⟨V, G, h1, h2, h3, h4⟩ := pair_Gdata_W1 h σW hpar hx2 hcard μ A Wf hWf x y c1 c2 (by omega)
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := hW1 Wf σW hWf μ L hμW hLb A hAP hAd V G h2 h3 h4 Kz
      (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nf (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nf (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    refine key.mono ?_
    omega
  · rw [hrearr]
    refine GV.add ?_ (GV.sum fun s hs => hTok x y s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1)
      (hoff s (Finset.mem_range.1 (Finset.mem_filter.1 hs).1) (Finset.mem_filter.1 hs).2))
    rw [hWfe]
    obtain ⟨V, G, Hr, h1, h2, h3, h4, h5, h6, h7, h8'⟩ :=
      pair_Gdata_W2 h σW hpar hx2 hcard μ A Wf hWf x y c1 c2 c3
    obtain ⟨Kz, -, hKz⟩ := lemmaR_p2 h σW hpar
    have key := hW2 Wf σW hWf ⟨s0, hs0Wf⟩ hx2 hpar μ L hμW hLb A hAP hAd V G Hr h2 h3 h4 h5 h6 h7 h8' Kz
      (fun s hs => hKz s ((hWf s).1 hs).1 ((hWf s).1 hs).2)
    have e : ∑ s ∈ Wf, ∑ l ∈ range (Lc n p s + 1), nf (s + l * p) (elF n p σW μ A x * elF n p σW μ A y) =
        ∑ s ∈ Wf, ∑ l ∈ range (L + 1), nf (s + l * p) ((∏ r ∈ Wf, shiftP p μ r A) ^ 2 * V.map zphi) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [hLW s hs, h1]
    rw [e]
    refine key.mono ?_
    have hxle := (pot_le h σW hpar x).1
    have hyle := (pot_le h σW hpar y).1
    omega


end Entry

/-! ### Part 11: the two channels -/

section Channels

variable {n : ℕ}

/-- **The `a`-channel of an entry**: `GV (thr + 1)`. -/
theorem entry_chA (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)
      (∑ k ∈ range (6 * n + 1), chA n k
        (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  refine entry_chan 1 (chA n) (fun k hk e F hF => ?_) ?_ ?_ h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
  · exact (chA_ge n k h.h8 hp3 hk hF).mono (le_of_eq (by ring))
  · intro Wf σW' hWf μ' L hμW hL A hA hAd V G hGE hGd hG Kz hK
    obtain ⟨hb1, hb2, hb3⟩ := hb_first h σW' Wf hWf μ' hμW A hA hAd V G hGE hGd hG Kz hK
    have := wsumA_core h σW' Wf hWf μ' L hL A hA hAd V 1 le_rfl (by norm_num) hb1 hb2 hb3
    simpa using this
  · intro Wf σW' hWf hne hx2' hpar' μ' L hμW hL A hA hAd V G Hr hGE hHE hGd hHd hG hG' hH Kz hK
    obtain ⟨hb1, hb2, hb3⟩ := hb_second h hx2' σW' Wf hWf hne μ' hμW A hA hAd V G Hr hGE hHE hGd hHd
      hG hG' hH Kz hK
    have := wsumA_core h σW' Wf hWf μ' L hL A hA hAd V 2 (by norm_num) le_rfl hb1 hb2 hb3
    refine this.mono ?_
    push_cast; omega

/-- **The `X`-channel of an entry**: `GV (thr + 4)`. -/
theorem entry_chX (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 4)
      (∑ k ∈ range (6 * n + 1), chX n k
        (elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y)) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  refine entry_chan 4 (chX n) (fun k hk e F hF => ?_) ?_ ?_ h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
  · exact (chX_ge n k h.h8 hp3 hk hF).mono (le_of_eq (by ring))
  · intro Wf σW' hWf μ' L hμW hL A hA hAd V G hGE hGd hG Kz hK
    obtain ⟨hb1, hb2, hb3⟩ := hb_first h σW' Wf hWf μ' hμW A hA hAd V G hGE hGd hG Kz hK
    have := wsumX_core h σW' Wf hWf μ' L hL A hA hAd V 1 le_rfl (by norm_num) hb1 hb2 hb3
    refine this.mono ?_
    push_cast; omega
  · intro Wf σW' hWf hne hx2' hpar' μ' L hμW hL A hA hAd V G Hr hGE hHE hGd hHd hG hG' hH Kz hK
    obtain ⟨hb1, hb2, hb3⟩ := hb_second h hx2' σW' Wf hWf hne μ' hμW A hA hAd V G Hr hGE hHE hGd hHd
      hG hG' hH Kz hK
    have := wsumX_core h σW' Wf hWf μ' L hL A hA hAd V 2 (by norm_num) le_rfl hb1 hb2 hb3
    refine this.mono ?_
    push_cast; omega


end Channels

/-! ### Part 12: from the generic functional to the entries of `L_n` -/

section Glue

variable {n : ℕ}

/-- The `a`-coefficient of `L_n(F)`. -/
def entA (n : ℕ) (F : ℚ[X]) : ℚ :=
  ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℚ) *
    (-3 * Hq 2 k * F.derivative.eval (-(k : ℚ)) + (3 * laiH n k * Hq 2 k - 6 * Hq 3 k) * F.eval (-(k : ℚ)))

/-- The `b`-coefficient of `L_n(F)`. -/
def entB (n : ℕ) (F : ℚ[X]) : ℚ :=
  ∑ k ∈ range (6 * n + 1), (laiCoef n k : ℚ) *
    (-2 * Hq 3 k * F.derivative.eval (-(k : ℚ)) + (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * F.eval (-(k : ℚ)))

/-- The `X`-coefficient of `L_n(F)`. -/
def entX (n : ℕ) (F : ℚ[X]) : ℚ :=
  ∑ k ∈ range (6 * n + 1), 6 * (laiCoef n k : ℚ) * F.eval (-(k : ℚ))

theorem laiL_channels (n : ℕ) (F : ℚ[X]) :
    laiL n F = MvPolynomial.X 0 * MvPolynomial.C (entA n F) + MvPolynomial.X 1 * MvPolynomial.C (entB n F) +
      MvPolynomial.X 2 * MvPolynomial.C (entX n F) := by
  unfold laiL entA entB entX
  simp only [map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold laiU laiV
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat]
  ring

theorem sum_chA_map (n : ℕ) (F : ℚ[X]) :
    ∑ k ∈ range (6 * n + 1), chA n k (F.map (MvPolynomial.C : ℚ →+* MPT)) =
      MvPolynomial.C (entA n F) := by
  unfold entA
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold chA
  rw [evk_map, devk_map]
  simp only [map_mul, map_add, map_sub, map_neg, map_ofNat]

theorem sum_chX_map (n : ℕ) (F : ℚ[X]) :
    ∑ k ∈ range (6 * n + 1), chX n k (F.map (MvPolynomial.C : ℚ →+* MPT)) =
      MvPolynomial.C (entX n F) := by
  unfold entX
  simp only [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold chX
  rw [evk_map]
  simp only [map_mul]

lemma shiftP_zero_orth (p s : ℕ) (L : ℕ) : shiftP p 0 s (orthA (cLoc L) 0) = 1 := by
  unfold shiftP orthA orthDet
  simp

lemma elF_band (σW μ : ℕ) (hμ0 : μ = 0) (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (L : ℕ)
    (x : FIdx n p σW) :
    elF n p σW μ (orthA (cLoc L) μ) x = (ExZ n p σW x).map zphi := by
  classical
  obtain ⟨Wf, hWf⟩ : ∃ Wf : Finset ℕ, ∀ r, r ∈ Wf ↔ r < p ∧ sig n p r = σW :=
    ⟨(range p).filter (fun r => sig n p r = σW), fun r => by simp [Finset.mem_filter, Finset.mem_range]⟩
  have hx : ∀ (r : Fin p) (i : Fin (mF n p σW r)), x = Sum.inl ⟨r, i⟩ → sig n p r ≠ σW := by
    intro r i _ hrW
    have hm := mn_mF_W σW μ hμ r r.2 hrW
    have := i.2
    omega
  rw [el_decomp σW μ _ Wf hWf x hx]
  have : ∏ r ∈ Wf, shiftP p μ r (orthA (cLoc L) μ) = 1 := by
    subst hμ0
    exact Finset.prod_eq_one fun r _ => shiftP_zero_orth p r L
  rw [this, one_mul]

/-- `bind₁ specT` of the node of `L_T` on a mapped polynomial is the node of `L_n`. -/
lemma bind_nodeT (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl τu τv : ℕ → ℚ) (k : ℕ) (F0 : ℚ[X]) :
    MvPolynomial.bind₁ (specT τu τv)
        (nodeT (p := p) n K σ cl τu τv k (F0.map (MvPolynomial.C : ℚ →+* MPT))) = laiNd n k F0 := by
  unfold nodeT
  rw [map_add, ndT_map, specT_ren]
  split_ifs
  · rw [modNdT_map, specT_modNd, add_zero]
  · rw [map_zero, add_zero]

/-- **The `b`-channel of an entry** (from `entry_bound`): `GV thr (L_n(e_x e_y))`. -/
theorem entry_laiL (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW) :
    GV p ((pot2F n p σW x + pot2F n p σW y + 1) / 2)
      (laiL n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ))) := by
  have h8 := h.h8
  have hE := entry_bound h σW hpar hx2 hcard s0 hs0 hsW μ hμ x y
  have hF : elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y =
      (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
    rw [elF_band σW μ hμ0 hμ, elF_band σW μ hμ0 hμ, ← Polynomial.map_mul, Polynomial.map_map]
    rfl
  rw [hF] at hE
  have hK6 : Kset n p σW ⊆ range (6 * n + 1) := Finset.filter_subset _ _
  rw [laiLTx_nodes n _ hK6] at hE
  have hg : ∀ v : TVar, GV p 0 (specT (tauU n p s0) (tauV n p s0) v) := by
    rintro (i | ⟨l, _ | _⟩)
    · exact GV.var i
    · exact GV.const_loc (mn_tauU_mem n s0 l)
    · exact GV.const_loc (mn_tauV_mem n s0 h8 l)
  have := GV.subst hE (specT (tauU n p s0) (tauV n p s0)) hg
  rw [map_sum] at this
  simp only [bind_nodeT] at this
  rwa [← laiL_eq_sum] at this


end Glue

/-! ### Part 13: LB02, the weighted entry bounds -/

section LB02

variable {n : ℕ}

/-- **LB02.**  For the E2 basis `e_x` (window multiplicity `μ = 0`), with `thr = ⌈(2π_x + 2π_y)/2⌉`
and `F = e_x e_y`: `v(A) ≥ thr + 1`, `v(B) ≥ thr`, `v(X-coefficient) ≥ thr + 4`, where
`L_n(F) = a A + b B + X C`. -/
theorem lb02_entry (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW) :
    (p : ℚ) ^ (-((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)) *
        entA n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)) ∈ LocRing p ∧
      (p : ℚ) ^ (-((pot2F n p σW x + pot2F n p σW y + 1) / 2)) *
        entB n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)) ∈ LocRing p ∧
      (p : ℚ) ^ (-((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 4)) *
        entX n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)) ∈ LocRing p := by
  have hF : elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) x * elF n p σW μ (orthA (cLoc (Lc n p s0)) μ) y =
      (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
    rw [elF_band σW μ hμ0 hμ, elF_band σW μ hμ0 hμ, ← Polynomial.map_mul, Polynomial.map_map]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · have := entry_chA h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
    rw [hF, sum_chA_map] at this
    exact GV.const_iff.1 this
  · have hv := entry_laiL h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
    have := GV.evalPt hv ![0, 1, 0] (fun i => by fin_cases i <;> simp [(LocRing p).one_mem])
    rw [laiL_channels] at this
    simpa using this
  · have := entry_chX h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
    rw [hF, sum_chX_map] at this
    exact GV.const_iff.1 this

/-- **LB02 at a point.**  For `a, b ∈ ℤ_(p)` and `v_p(X) ≥ -3`, the entry of `L_n` at `(a, b, X)` is
`b B` up to `p^{thr+1}`. -/
theorem lb02_point (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (hx2 : 0 < xtwo n p)
    (hcard : ((range p).filter (fun s => sig n p s = σW)).card = tieW n p)
    (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = σW) (μ : ℕ)
    (hμ : ∀ r < p, sig n p r = σW → mu n p r = μ) (hμ0 : μ = 0) (x y : FIdx n p σW)
    (a b X : ℚ) (ha : a ∈ LocRing p) (hb : b ∈ LocRing p) (hX : (p : ℚ) ^ 3 * X ∈ LocRing p) :
    (p : ℚ) ^ (-((pot2F n p σW x + pot2F n p σW y + 1) / 2 + 1)) *
      (MvPolynomial.eval ![a, b, X]
          (laiL n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ))) -
        b * entB n (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ))) ∈ LocRing p := by
  obtain ⟨hA, -, hC⟩ := lb02_entry h σW hpar hx2 hcard s0 hs0 hsW μ hμ hμ0 x y
  have hp0 := p_ne_zero' (p := p)
  rw [laiL_channels]
  simp only [map_add, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  set E := (((ExZ n p σW x) * (ExZ n p σW y)).map (Int.castRingHom ℚ)) with hE
  set t : ℤ := (pot2F n p σW x + pot2F n p σW y + 1) / 2 with ht
  have e : (p : ℚ) ^ (-(t + 1)) * (a * entA n E + b * entB n E + X * entX n E - b * entB n E) =
      a * ((p : ℚ) ^ (-(t + 1)) * entA n E) + (p : ℚ) ^ 3 * X * ((p : ℚ) ^ (-(t + 4)) * entX n E) := by
    have e1 : (p : ℚ) ^ (-(t + 1)) = (p : ℚ) ^ 3 * (p : ℚ) ^ (-(t + 4)) := by
      rw [show (p : ℚ) ^ 3 = (p : ℚ) ^ (3 : ℤ) by norm_cast, pz]; congr 1; ring
    rw [e1]; ring
  rw [e]
  exact (LocRing p).add_mem ((LocRing p).mul_mem ha hA) ((LocRing p).mul_mem hX hC)


end LB02

/-! ### Part 14: the band `8n/3 < p < 3n - 1` -/

section Band

variable {n : ℕ}

theorem band_rng (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : Rng n p := by
  have hp11 : 11 ≤ p := by omega
  refine ⟨?_, by omega⟩
  nlinarith

theorem band_q6 (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : q6 n p = 2 := by
  have hpp := hp.out.pos
  unfold q6
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem band_q2 (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : q2 n p = 0 := by
  have hpp := hp.out.pos
  unfold q2
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem band_r6 (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : r6 n p = 6 * n - 2 * p := by
  have hpp := hp.out.pos
  have := qr6 n p hpp
  rw [band_q6 (p := p) h1 h2] at this
  omega

theorem band_r2 (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : r2 n p = 2 * n := by
  have hpp := hp.out.pos
  have := qr2 n p hpp
  rw [band_q2 (p := p) h1 h2] at this
  omega

/-- In the band the greedy cut is `λ = 1`. -/
theorem band_lam (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : lam n p = 1 := by
  have h := band_rng (p := p) h1 h2
  have hq6 := band_q6 (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hl0 := lam_ge_zero h
  have hl1 := lam_le_top h
  obtain ⟨hs1, hs2⟩ := lam_spec n p (by have := h.p5; omega) (by have := h.n2; omega)
  by_contra hne
  have hz : lam n p = 0 := by omega
  rw [hz] at hs1
  have := cnt_formula h 0 (by omega) (by omega)
  rw [this, hr6, hr2] at hs1
  norm_num at hs1
  omega

theorem band_mu (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (r : ℕ) (hr : r < p) (hs : sig n p r = 5) :
    mu n p r = 0 := by
  have h := band_rng (p := p) h1 h2
  rw [mu_formula h hr, band_lam h1 h2, hs]
  norm_num

open Classical in
theorem band_xtwo (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) :
    xtwo n p = ((3 * n - 1 - p : ℕ) : ℤ) ∧ tieW n p = 2 * n := by
  have h := band_rng (p := p) h1 h2
  have hq6 := band_q6 (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hlam := band_lam (p := p) h1 h2
  have hsum : ∑ s ∈ range p, mu n p s = 2 * n + 1 := by
    have e : ∑ s ∈ range p, mu n p s = cnt n p (lam n p - 1) := rfl
    have hc0 := cnt_formula h 0 (by omega) (by omega)
    rw [e, hlam, sub_self, hc0, hr6, hr2]
    norm_num
    omega
  have hd : dcnt n p = n - 1 := by
    unfold dcnt; rw [hsum]; omega
  have hodd : ¬ lam n p % 2 = 0 := by rw [hlam]; norm_num
  have hszB : szB n p = 0 := by unfold szB; omega
  have hszD : szD n p = 2 * n := by unfold szD; omega
  have hszA : szA n p = 6 * n - 2 * p + 1 := by unfold szA; omega
  have hszC : szC n p = (p - 2 * n) - (6 * n - 2 * p + 1) := by unfold szC; omega
  have hW : tieW n p = 2 * n := by
    unfold tieW; rw [if_neg hodd, hszB, hszD]; omega
  have hZ : tieZ n p = 0 := by
    unfold tieZ; rw [if_neg hodd, hszB, hszD]; omega
  have hN : Ncnt n p = p - 2 * n := by
    rw [Ncnt_eq h, if_neg hodd, hszA, hszC]; omega
  refine ⟨?_, hW⟩
  unfold xtwo xone
  rw [hd, hW, hZ, hN]
  omega

theorem band_xtwo_pos (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) : 0 < xtwo n p := by
  rw [(band_xtwo (p := p) h1 h2).1]
  omega

/-- **LB02 in the band.**  The weighted entry bounds of the E2 basis (`σ_W = 5`, window `D = [a, p)`,
`μ_W = 0`): for all `x, y` in the family, with `thr = ⌈(2π_x + 2π_y)/2⌉` and `F = e_x e_y`,
`L_n(F) = a A + b B + X C` with `v(A) ≥ thr + 1`, `v(B) ≥ thr`, `v(C) ≥ thr + 4`. -/
theorem lb02_band (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (x y : FIdx n p 5) :
    (p : ℚ) ^ (-((pot2F n p 5 x + pot2F n p 5 y + 1) / 2 + 1)) *
        entA n (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)) ∈ LocRing p ∧
      (p : ℚ) ^ (-((pot2F n p 5 x + pot2F n p 5 y + 1) / 2)) *
        entB n (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)) ∈ LocRing p ∧
      (p : ℚ) ^ (-((pot2F n p 5 x + pot2F n p 5 y + 1) / 2 + 4)) *
        entX n (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)) ∈ LocRing p := by
  classical
  have h := band_rng (p := p) h1 h2
  have hlam := band_lam (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hs0 : p - 2 * n < p := by omega
  have hsW : sig n p (p - 2 * n) = 5 := by
    unfold sig; rw [hr6, hr2]
    have : ¬ (p - 2 * n ≤ 6 * n - 2 * p) := by omega
    have h2' : p - 2 * n ≤ p - 2 * n := le_rfl
    simp [this, h2']
  refine lb02_entry h 5 (by rw [hlam]; norm_num) (band_xtwo_pos h1 h2) ?_ (p - 2 * n) hs0 hsW 0
    (fun r hr hrs => band_mu h1 h2 r hr hrs) rfl x y
  rw [card_sig_five h, (band_xtwo h1 h2).2]
  unfold szD; rw [hr6, hr2]; omega

end Band

end

end CatalanCore.Lai

#print axioms CatalanCore.Lai.chA_ge
#print axioms CatalanCore.Lai.chX_ge
#print axioms CatalanCore.Lai.chA_jet
#print axioms CatalanCore.Lai.nodeA_step
#print axioms CatalanCore.Lai.nodeX_step
#print axioms CatalanCore.Lai.wsumA_core
#print axioms CatalanCore.Lai.wsumX_core
#print axioms CatalanCore.Lai.entry_chan
#print axioms CatalanCore.Lai.entry_chA
#print axioms CatalanCore.Lai.entry_chX
#print axioms CatalanCore.Lai.entry_laiL
#print axioms CatalanCore.Lai.lb02_entry
#print axioms CatalanCore.Lai.lb02_point
#print axioms CatalanCore.Lai.band_lam
#print axioms CatalanCore.Lai.band_xtwo
#print axioms CatalanCore.Lai.lb02_band
