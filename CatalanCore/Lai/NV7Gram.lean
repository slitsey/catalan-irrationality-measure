module

public import CatalanCore.Lai.ContentLaw
public import CatalanCore.Lai.NVCore

@[expose] public section

/-! # `CatalanCore.Lai.NV7Gram`: node expansion, the E-prime lattice and its Gram matrix modulo l (ledger LN06, steps 1-3). -/

section
/-!
# Node expansion at NV points (generic first-order expansion of a node term)

For a node `-k`, `k = s + jℓ`, and `F = (X + s)^m R` with `R` an `ℓ`-integral polynomial, the node term
`w (u F'(-k) + e F(-k))` with `w = ℓ^ω w₀`, `ℓ³u = U`, `ℓ⁴e = E` satisfies
`ℓ⁴ · term = ℓ^{ω+m} (w₀ · M + ℓ z)`, `z ∈ ℤ_(ℓ)`, where the main term is
`M = E ρ` for `m = 0` and `(-j)^{m-1} (m U - j E) ρ` for `m ≥ 1`, `ρ = R(-s)`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Main term of a node expansion, in `ℤ_(ℓ)`. -/
def Mr (m j : ℕ) (U E ρ : LocRing ℓ) : LocRing ℓ :=
  if m = 0 then E * ρ else (-(j : LocRing ℓ)) ^ (m - 1) * ((m : LocRing ℓ) * U - (j : LocRing ℓ) * E) * ρ

theorem node_expand (k ω w0 : ℕ) (u e : ℚ) (U E ρ : LocRing ℓ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = (E : ℚ)) (m : ℕ) (R : ℚ[X])
    (hR : IntPoly ℓ R) (hρ : (ρ : ℚ) = R.eval (-((k % ℓ : ℕ) : ℚ))) :
    ∃ z : LocRing ℓ,
      (ℓ : ℚ) ^ 4 * ((ℓ : ℚ) ^ ω * (w0 : ℚ) *
        (u * (derivative ((X + C ((k % ℓ : ℕ) : ℚ)) ^ m * R)).eval (-(k : ℚ)) +
          e * (((X + C ((k % ℓ : ℕ) : ℚ)) ^ m * R).eval (-(k : ℚ))))) =
      (ℓ : ℚ) ^ (ω + m) * ((w0 : ℚ) * ((Mr m (k / ℓ) U E ρ : LocRing ℓ) : ℚ) + (ℓ : ℚ) * (z : ℚ)) := by
  have hl : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  set s := k % ℓ with hs
  set j := k / ℓ with hj
  have hkl : k = ℓ * j + s := (Nat.div_add_mod k ℓ).symm
  have hkq : (k : ℚ) = ℓ * j + s := by exact_mod_cast hkl
  have hxs : -(k : ℚ) + s = -((j : ℚ) * ℓ) := by rw [hkq]; ring
  -- R(-k) = R(-s) + ℓ e1
  obtain ⟨e1, he1⟩ : ∃ e1 : LocRing ℓ, R.eval (-(k : ℚ)) = R.eval (-(s : ℚ)) + (ℓ : ℚ) * (e1 : ℚ) := by
    have := hR.eval_sub (-(k : ℤ)) (-(s : ℤ)) (by
      have : (-(k : ℤ)) - (-(s : ℤ)) = -((ℓ : ℤ) * j) := by omega
      rw [this]; exact (dvd_neg.2 (dvd_mul_right _ _)))
    refine ⟨⟨_, this⟩, ?_⟩
    simp only
    push_cast at this ⊢
    field_simp
    ring
  have hρ' : ∃ ρ' : LocRing ℓ, (ρ' : ℚ) = (derivative R).eval (-(k : ℚ)) :=
    ⟨⟨_, hR.derivative.eval_mem ((LocRing ℓ).neg_mem (by exact_mod_cast int_mem_locRing (ℓ := ℓ) (k : ℤ)))⟩, rfl⟩
  obtain ⟨ρ', hρ'⟩ := hρ'
  have hFe : (((X + C (s : ℚ)) ^ m * R).eval (-(k : ℚ))) = (-((j : ℚ) * ℓ)) ^ m * R.eval (-(k : ℚ)) := by
    rw [eval_mul, eval_pow]
    simp only [eval_add, eval_X, eval_C]
    rw [hxs]
  have hFd : (derivative ((X + C (s : ℚ)) ^ m * R)).eval (-(k : ℚ)) =
      (m : ℚ) * (-((j : ℚ) * ℓ)) ^ (m - 1) * R.eval (-(k : ℚ)) +
        (-((j : ℚ) * ℓ)) ^ m * (derivative R).eval (-(k : ℚ)) := by
    rw [derivative_mul, derivative_pow]
    simp only [derivative_add, derivative_X, derivative_C, add_zero, mul_one, eval_add, eval_mul,
      eval_pow, eval_C, eval_X, eval_natCast]
    rw [hxs]
  rw [hFe, hFd, he1, ← hρ, ← hρ']
  rcases m with _ | m'
  · -- m = 0
    refine ⟨(w0 : LocRing ℓ) * (U * ρ' + E * e1), ?_⟩
    simp only [Mr, if_true, Nat.cast_zero, pow_zero, zero_mul, zero_add, one_mul, add_zero]
    have hu' : (ℓ : ℚ) ^ 4 * u = (ℓ : ℚ) * (U : ℚ) := by
      rw [show (ℓ : ℚ) ^ 4 = ℓ * ℓ ^ 3 by ring, mul_assoc, hu]
    push_cast
    calc (ℓ : ℚ) ^ 4 * ((ℓ : ℚ) ^ ω * (w0 : ℚ) * (u * (ρ' : ℚ) + e * ((ρ : ℚ) + ℓ * (e1 : ℚ))))
        = (ℓ : ℚ) ^ ω * w0 * (((ℓ : ℚ) ^ 4 * u) * ρ' + ((ℓ : ℚ) ^ 4 * e) * (ρ + ℓ * e1)) := by ring
      _ = _ := by rw [hu', he]; ring
  · -- m = m' + 1
    refine ⟨(w0 : LocRing ℓ) * ((-(j : LocRing ℓ)) ^ m' * ((((m' + 1 : ℕ) : LocRing ℓ)) * U - (j : LocRing ℓ) * E) * e1 +
      U * (-(j : LocRing ℓ)) ^ (m' + 1) * ρ'), ?_⟩
    simp only [Mr, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    have hu' : (ℓ : ℚ) ^ 4 * u = (ℓ : ℚ) * (U : ℚ) := by
      rw [show (ℓ : ℚ) ^ 4 = ℓ * ℓ ^ 3 by ring, mul_assoc, hu]
    push_cast
    have e1' : (-((j : ℚ) * ℓ)) ^ (m' + 1) = (ℓ : ℚ) ^ (m' + 1) * (-(j : ℚ)) ^ (m' + 1) := by
      rw [← mul_pow]; congr 1; ring
    have e2' : (-((j : ℚ) * ℓ)) ^ m' = (ℓ : ℚ) ^ m' * (-(j : ℚ)) ^ m' := by
      rw [← mul_pow]; congr 1; ring
    rw [e1', e2']
    have hE' : (ℓ : ℚ) ^ 4 * e = E := he
    calc (ℓ : ℚ) ^ 4 * ((ℓ : ℚ) ^ ω * (w0 : ℚ) *
          (u * (((m' : ℚ) + 1) * ((ℓ : ℚ) ^ m' * (-(j : ℚ)) ^ m') * ((ρ : ℚ) + ℓ * (e1 : ℚ)) +
            (ℓ : ℚ) ^ (m' + 1) * (-(j : ℚ)) ^ (m' + 1) * (ρ' : ℚ)) +
          e * ((ℓ : ℚ) ^ (m' + 1) * (-(j : ℚ)) ^ (m' + 1) * ((ρ : ℚ) + ℓ * (e1 : ℚ)))))
        = (ℓ : ℚ) ^ ω * w0 * ((ℓ : ℚ) * U *
            (((m' : ℚ) + 1) * ((ℓ : ℚ) ^ m' * (-(j : ℚ)) ^ m') * ((ρ : ℚ) + ℓ * (e1 : ℚ)) +
            (ℓ : ℚ) ^ (m' + 1) * (-(j : ℚ)) ^ (m' + 1) * (ρ' : ℚ)) +
          (E : ℚ) * ((ℓ : ℚ) ^ (m' + 1) * (-(j : ℚ)) ^ (m' + 1) * ((ρ : ℚ) + ℓ * (e1 : ℚ)))) := by
          rw [← hu', ← hE']; ring
      _ = _ := by push_cast; ring

end CatalanCore.Lai.NV7

end

section
/-!
# The data `U_k = ℓ³u_k`, `E_k = ℓ⁴e_k` of Lai's `J_n` at an NV point `(a, b, X'/ℓ³)`

For `k ≤ 6n`, `8n < ℓ²`, `a, b, X' ∈ ℤ_(ℓ)`: `U_k ≡ b · u_{⌊k/ℓ⌋}` and `E_k ≡ b · v_{⌊k/ℓ⌋}(δ_k)`
modulo `ℓ`, with `u_j = -2 H_j(3)`, `v_j = -2 (H_j(3) δ + 3 H_j(4))` (content `Lemma N`).
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem nv_UE (n k : ℕ) (hk : k ≤ 6 * n) (h8 : 8 * n < ℓ ^ 2) (a b X' : LocRing ℓ) :
    ∃ U E zU zE : LocRing ℓ,
      (ℓ : ℚ) ^ 3 * (-3 * (a : ℚ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) = (U : ℚ) ∧
      (ℓ : ℚ) ^ 4 * (laiH n k * (3 * (a : ℚ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - (a : ℚ) * Hq 3 k - (b : ℚ) * Hq 4 k)) = (E : ℚ) ∧
      (U : ℚ) = (b : ℚ) * uL (k / ℓ) + (ℓ : ℚ) * (zU : ℚ) ∧
      (E : ℚ) = (b : ℚ) * vL n ℓ k (k / ℓ) + (ℓ : ℚ) * (zE : ℚ) := by
  have hl : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have c2 : ((2 : LocRing ℓ) : ℚ) = 2 := rfl
  have c3 : ((3 : LocRing ℓ) : ℚ) = 3 := rfl
  have c6 : ((6 : LocRing ℓ) : ℚ) = 6 := rfl
  have hj : k / ℓ < ℓ := by
    rw [Nat.div_lt_iff_lt_mul hℓ.out.pos]; nlinarith
  set j := k / ℓ with hjdef
  let H2 : LocRing ℓ := ⟨Hq 2 j, Hq_mem 2 j hj⟩
  let H3 : LocRing ℓ := ⟨Hq 3 j, Hq_mem 3 j hj⟩
  let H4 : LocRing ℓ := ⟨Hq 4 j, Hq_mem 4 j hj⟩
  let z2 : LocRing ℓ := ⟨Hq 2 k - ((ℓ : ℚ) ^ 2)⁻¹ * Hq 2 j, Hq_split 2 k⟩
  let z3 : LocRing ℓ := ⟨Hq 3 k - ((ℓ : ℚ) ^ 3)⁻¹ * Hq 3 j, Hq_split 3 k⟩
  let z4 : LocRing ℓ := ⟨Hq 4 k - ((ℓ : ℚ) ^ 4)⁻¹ * Hq 4 j, Hq_split 4 k⟩
  let dl : LocRing ℓ := ⟨laiDelta n ℓ k, delta_mem n k h8 hk⟩
  let h0 : LocRing ℓ := ⟨laiH n k + (ℓ : ℚ)⁻¹ * laiDelta n ℓ k, laiH_split n k⟩
  let N1 : LocRing ℓ := 3 * a * (H2 + (ℓ : LocRing ℓ) ^ 2 * z2) + 2 * b * (ℓ : LocRing ℓ) ^ 2 * z3
  let N : LocRing ℓ := 2 * b * H3 + (ℓ : LocRing ℓ) * N1
  refine ⟨-3 * a * ((ℓ : LocRing ℓ) * H2 + (ℓ : LocRing ℓ) ^ 3 * z2) -
      2 * b * (H3 + (ℓ : LocRing ℓ) ^ 3 * z3),
    (ℓ : LocRing ℓ) * h0 * N - dl * N + 6 * (ℓ : LocRing ℓ) * X' - 6 * (ℓ : LocRing ℓ) * a * H3 -
      6 * (ℓ : LocRing ℓ) ^ 4 * a * z3 - 6 * b * H4 - 6 * (ℓ : LocRing ℓ) ^ 4 * b * z4,
    -3 * a * (H2 + (ℓ : LocRing ℓ) ^ 2 * z2) - 2 * b * (ℓ : LocRing ℓ) ^ 2 * z3,
    h0 * N - dl * N1 + 6 * X' - 6 * a * H3 - 6 * (ℓ : LocRing ℓ) ^ 3 * a * z3 -
      6 * (ℓ : LocRing ℓ) ^ 3 * b * z4, ?_, ?_, ?_, ?_⟩
  · simp only [H2, H3, z2, z3, N1, N, Subring.coe_mul, Subring.coe_add,
      Subring.coe_pow, Subring.coe_natCast, Subring.coe_neg]
    push_cast
    simp only [c2, c3, c6]
    field_simp
    ring
  · simp only [H2, H3, H4, z2, z3, z4, dl, h0, N1, N, Subring.coe_mul,
      Subring.coe_add, Subring.coe_pow, Subring.coe_natCast, Subring.coe_neg]
    push_cast
    simp only [c2, c3, c6]
    field_simp
    ring
  · simp only [H3, H2, z2, z3, uL, Subring.coe_mul, Subring.coe_add,
      Subring.coe_pow, Subring.coe_natCast, Subring.coe_neg]
    push_cast
    simp only [c2, c3, c6]
    field_simp
    ring
  · simp only [H3, H2, H4, z2, z3, z4, dl, h0, N1, N, vL, Subring.coe_mul,
      Subring.coe_add, Subring.coe_pow, Subring.coe_natCast, Subring.coe_neg]
    push_cast
    simp only [c2, c3, c6]
    field_simp
    ring

end CatalanCore.Lai.NV7

end

section
/-!
# The `E′` lattice: basis, exponents, and the exponent bound (generic in `α, A, d`)

Residues `0, …, A` carry the multiplicity `ν₀(t) = 3` (`t < α`, the set `T1`) or `1` (`α ≤ t ≤ A`, `T2`);
the residues `A < t < ℓ` (`T4`) have no zero.  The basis consists of the A-vectors
`(X + r)^i Π/(X + r)³` (`r < α`, `i < 3`), the E-vectors `Π/(X + u)` (`u ∈ T2`) and the G-vectors
`X^m Π`.  All are of the form `Pd (A+1) w ν` of `Lai.ContentLaw`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section Scaled

theorem sum_scaled {κ : Type*} (s : Finset κ) (e : κ → ℕ) (c : ℕ) (hc : ∀ k ∈ s, c ≤ e k)
    (wq zq : κ → LocRing ℓ) :
    ∃ Z : LocRing ℓ, (∑ k ∈ s, (ℓ : ℚ) ^ (e k) * ((wq k : ℚ) + (ℓ : ℚ) * (zq k : ℚ))) =
        (ℓ : ℚ) ^ c * (Z : ℚ) ∧
      redQ ℓ Z = ∑ k ∈ s, if e k = c then redQ ℓ (wq k) else 0 := by
  classical
  refine ⟨∑ k ∈ s, (ℓ : LocRing ℓ) ^ (e k - c) * (wq k + (ℓ : LocRing ℓ) * zq k), ?_, ?_⟩
  · push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := hc k hk
    obtain ⟨t, ht⟩ : ∃ t, e k = c + t := ⟨e k - c, by omega⟩
    rw [ht, Nat.add_sub_cancel_left, pow_add]
    ring
  · rw [map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have := hc k hk
    have hz : redQ ℓ (ℓ : LocRing ℓ) = 0 := by
      have : ((ℓ : ℕ) : LocRing ℓ) = (ℓ : LocRing ℓ) := rfl
      rw [map_natCast, ZMod.natCast_self]
    by_cases h : e k = c
    · rw [if_pos h, h, Nat.sub_self, pow_zero, one_mul, map_add, map_mul, hz, zero_mul, add_zero]
    · rw [if_neg h]
      obtain ⟨t, ht⟩ : ∃ t, e k - c = t + 1 := ⟨e k - c - 1, by omega⟩
      rw [ht, pow_succ, map_mul, map_mul, map_pow, hz, mul_zero, zero_mul]

end Scaled

section Basis

variable (α A d : ℕ)

abbrev IA : Type := Fin α × Fin 3
abbrev IB : Type := Fin (A + 1 - α) ⊕ Fin d
abbrev Ix : Type := IA α ⊕ IB α A d

/-- multiplicity of `X + t` in `Π`. -/
def nu0 (t : ℕ) : ℕ := if t < α then 3 else 1

/-- multiplicity of `X + t` in the basis vector `x`. -/
def nuV : Ix α A d → Fin (A + 1) → ℕ
  | Sum.inl (r, i) => fun t => if (t : ℕ) = r then (i : ℕ) else nu0 α t
  | Sum.inr (Sum.inl u) => fun t => if (t : ℕ) = α + u then 0 else nu0 α t
  | Sum.inr (Sum.inr _) => fun t => nu0 α t

/-- power of `X` in the basis vector `x`. -/
def wV : Ix α A d → ℕ
  | Sum.inr (Sum.inr m) => m
  | _ => 0

noncomputable def vecV (x : Ix α A d) : ℚ[X] := Pd (A + 1) (wV α A d x) (nuV α A d x)

def exV : Ix α A d → ℕ
  | Sum.inl (_, i) => (i : ℕ)
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

def eyV : Ix α A d → ℕ
  | Sum.inl (_, i) => (i : ℕ)
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr _) => 3

/-- the `B × A` correction. -/
def corr : Ix α A d → Ix α A d → ℕ
  | Sum.inr _, Sum.inl _ => 1
  | _, _ => 0

/-- `ℓ`-adic valuation class of the weights: `0` on `T1`, `3` on `T2`, `5` on `T4`. -/
def omg (s : ℕ) : ℕ := if s < α then 0 else if s ≤ A then 3 else 5

/-- multiplicity of `X + s` in the product of two basis vectors. -/
def mm (x y : Ix α A d) (s : ℕ) : ℕ := mmF (A + 1) (fun t => nuV α A d x t + nuV α A d y t) s

theorem mm_lt (x y : Ix α A d) (s : ℕ) (hs : s < A + 1) :
    mm α A d x y s = nuV α A d x ⟨s, hs⟩ + nuV α A d y ⟨s, hs⟩ := by
  simp [mm, mmF, hs]

theorem mm_ge (x y : Ix α A d) (s : ℕ) (hs : A + 1 ≤ s) : mm α A d x y s = 0 := by
  simp [mm, mmF, show ¬ s < A + 1 by omega]

variable {α A d}

/-- **The exponent bound.**  Every node term of every Gram entry has `ℓ`-exponent at least
`e_x + f_y (+ 1 on B × A)`. -/
theorem bound (hαA : α ≤ A) (x y : Ix α A d) (s : ℕ) :
    exV α A d x + eyV α A d y + corr α A d x y ≤ omg α A s + mm α A d x y s := by
  by_cases hs : s < A + 1
  · rw [mm_lt α A d x y s hs]
    rcases x with ⟨r, i⟩ | u | m <;> rcases y with ⟨r', i'⟩ | u' | m' <;>
      simp only [nuV, exV, eyV, corr, omg, nu0] <;>
      (try have h1 := i.2) <;> (try have h2 := i'.2) <;> (try have h3 := r.2) <;> (try have h4 := r'.2) <;>
      (try have h5 := u.2) <;> (try have h6 := u'.2) <;> split_ifs <;> omega
  · rw [mm_ge α A d x y s (by omega)]
    rcases x with ⟨r, i⟩ | u | m <;> rcases y with ⟨r', i'⟩ | u' | m' <;>
      simp only [exV, eyV, corr, omg] <;> (try have h1 := i.2) <;> (try have h2 := i'.2) <;> split_ifs <;> omega

end Basis

end CatalanCore.Lai.NV7

end

section
/-!
# The Gram matrix of Lai's node functional on the `E′` lattice, modulo `ℓ`

`gram_Z`: for the node functional `L = nodeL (6n) (laiCoef n) u e` with `ℓ³u_k = U_k`, `ℓ⁴e_k = E_k`
in `ℤ_(ℓ)`, the Gram matrix `G_xy = L(φ_x φ_y)` satisfies `ℓ⁴ G_xy = ℓ^{e_x} Z_xy ℓ^{f_y}` with `Z` over
`ℤ_(ℓ)` and `Z̄_xy` the explicit sum of the first-order node terms whose exponent is exactly `e_x + f_y`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Main term of a node expansion, in `ZMod ℓ`. -/
def Mb (m j : ℕ) (U E ρ : ZMod ℓ) : ZMod ℓ :=
  if m = 0 then E * ρ else (-(j : ZMod ℓ)) ^ (m - 1) * ((m : ZMod ℓ) * U - (j : ZMod ℓ) * E) * ρ

theorem redQ_Mr (m j : ℕ) (U E ρ : LocRing ℓ) :
    redQ ℓ (Mr m j U E ρ) = Mb m j (redQ ℓ U) (redQ ℓ E) (redQ ℓ ρ) := by
  unfold Mr Mb
  split_ifs
  · rw [map_mul]
  · simp only [map_mul, map_pow, map_neg, map_sub, map_natCast]

/-- the value at `-s` of the cofactor `RRF`, reduced mod `ℓ`. -/
noncomputable def rhoZ (ℓ : ℕ) (a w : ℕ) (ν : Fin a → ℕ) (s : ℕ) : ZMod ℓ :=
  if h : s < a then (-(s : ZMod ℓ)) ^ w * ∏ r ∈ (univ : Finset (Fin a)).erase ⟨s, h⟩,
      (((r : ℕ) : ZMod ℓ) - s) ^ ν r
  else (-(s : ZMod ℓ)) ^ w * ∏ r : Fin a, (((r : ℕ) : ZMod ℓ) - s) ^ ν r

theorem RRF_rho (a w : ℕ) (ν : Fin a → ℕ) (s : ℕ) :
    ∃ ρ : LocRing ℓ, (ρ : ℚ) = (RRF a w ν s).eval (-(s : ℚ)) ∧ redQ ℓ ρ = rhoZ ℓ a w ν s := by
  unfold RRF rhoZ
  by_cases h : s < a
  · simp only [h, dite_true]
    refine ⟨(-(s : LocRing ℓ)) ^ w * ∏ r ∈ (univ : Finset (Fin a)).erase ⟨s, h⟩,
      (((r : ℕ) : LocRing ℓ) - (s : LocRing ℓ)) ^ ν r, ?_, ?_⟩
    · push_cast
      rw [eval_mul, eval_pow, eval_X, eval_prod]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [eval_pow, eval_add, eval_X, eval_C]; ring
    · simp only [map_mul, map_pow, map_neg, map_prod, map_sub, map_natCast]
  · simp only [h, dite_false]
    refine ⟨(-(s : LocRing ℓ)) ^ w * ∏ r : Fin a, (((r : ℕ) : LocRing ℓ) - (s : LocRing ℓ)) ^ ν r, ?_, ?_⟩
    · push_cast
      unfold Pd
      rw [eval_mul, eval_pow, eval_X, eval_prod]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [eval_pow, eval_add, eval_X, eval_C]; ring
    · simp only [map_mul, map_pow, map_neg, map_prod, map_sub, map_natCast]

variable {α A d : ℕ}

theorem gram_Z (n : ℕ) (hαA : α ≤ A) (w0 : ℕ → ℕ)
    (hw : ∀ k ≤ 6 * n, (laiCoef n k : ℚ) = (ℓ : ℚ) ^ (omg α A (k % ℓ)) * (w0 k : ℚ))
    (u e : ℕ → ℚ) (U E : ℕ → LocRing ℓ)
    (hU : ∀ k ≤ 6 * n, (ℓ : ℚ) ^ 3 * u k = (U k : ℚ))
    (hE : ∀ k ≤ 6 * n, (ℓ : ℚ) ^ 4 * e k = (E k : ℚ)) :
    ∃ Z : Matrix (Ix α A d) (Ix α A d) (LocRing ℓ),
      (∀ x y, (ℓ : ℚ) ^ 4 *
          CatalanCore.Lai.NV.nodeL (6 * n) (fun k => (laiCoef n k : ℚ)) u e (vecV α A d x * vecV α A d y) =
        (ℓ : ℚ) ^ (exV α A d x) * ((Z x y : LocRing ℓ) : ℚ) * (ℓ : ℚ) ^ (eyV α A d y)) ∧
      ∀ x y, redQ ℓ (Z x y) = ∑ k ∈ range (6 * n + 1),
        if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
          (w0 k : ZMod ℓ) * Mb (mm α A d x y (k % ℓ)) (k / ℓ) (redQ ℓ (U k)) (redQ ℓ (E k))
            (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
              (fun t => nuV α A d x t + nuV α A d y t) (k % ℓ)) else 0 := by
  classical
  have key : ∀ x y : Ix α A d, ∃ Zxy : LocRing ℓ,
      (ℓ : ℚ) ^ 4 * CatalanCore.Lai.NV.nodeL (6 * n) (fun k => (laiCoef n k : ℚ)) u e
          (vecV α A d x * vecV α A d y) =
        (ℓ : ℚ) ^ (exV α A d x + eyV α A d y) * (Zxy : ℚ) ∧
      redQ ℓ Zxy = ∑ k ∈ range (6 * n + 1),
        if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
          (w0 k : ZMod ℓ) * Mb (mm α A d x y (k % ℓ)) (k / ℓ) (redQ ℓ (U k)) (redQ ℓ (E k))
            (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
              (fun t => nuV α A d x t + nuV α A d y t) (k % ℓ)) else 0 := by
    intro x y
    set ν : Fin (A + 1) → ℕ := fun t => nuV α A d x t + nuV α A d y t with hν
    set W : ℕ := wV α A d x + wV α A d y with hW
    have hf : vecV α A d x * vecV α A d y = Pd (A + 1) W ν := by
      unfold vecV; rw [Pd_mul]
    -- per-node data
    have hnode : ∀ k : ℕ, ∃ ρ z : LocRing ℓ, k ≤ 6 * n →
        redQ ℓ ρ = rhoZ ℓ (A + 1) W ν (k % ℓ) ∧
        (ℓ : ℚ) ^ 4 * ((laiCoef n k : ℚ) * (u k * (derivative (vecV α A d x * vecV α A d y)).eval (-(k : ℚ)) +
            e k * (vecV α A d x * vecV α A d y).eval (-(k : ℚ)))) =
          (ℓ : ℚ) ^ (omg α A (k % ℓ) + mm α A d x y (k % ℓ)) *
            (((w0 k : LocRing ℓ) * Mr (mm α A d x y (k % ℓ)) (k / ℓ) (U k) (E k) ρ : LocRing ℓ) +
              (ℓ : ℚ) * (z : ℚ)) := by
      intro k
      by_cases hk : k ≤ 6 * n
      · obtain ⟨ρ, hρ1, hρ2⟩ := RRF_rho (ℓ := ℓ) (A + 1) W ν (k % ℓ)
        obtain ⟨z, hz⟩ := node_expand k (omg α A (k % ℓ)) (w0 k) (u k) (e k) (U k) (E k) ρ (hU k hk)
          (hE k hk) (mm α A d x y (k % ℓ)) (RRF (A + 1) W ν (k % ℓ)) (RRF_int (A + 1) W ν (k % ℓ)) hρ1
        refine ⟨ρ, z, fun _ => ⟨hρ2, ?_⟩⟩
        have hdec : vecV α A d x * vecV α A d y =
            (X + C ((k % ℓ : ℕ) : ℚ)) ^ (mm α A d x y (k % ℓ)) * RRF (A + 1) W ν (k % ℓ) := by
          rw [hf]; exact Pd_decomp (A + 1) W ν (k % ℓ)
        rw [hdec, hw k hk]
        rw [hz]
        push_cast
        ring
      · exact ⟨0, 0, fun h => absurd h hk⟩
    choose ρf zf hnf using hnode
    obtain ⟨Z, hZ1, hZ2⟩ := sum_scaled (ℓ := ℓ) (range (6 * n + 1))
      (fun k => omg α A (k % ℓ) + mm α A d x y (k % ℓ)) (exV α A d x + eyV α A d y)
      (fun k _ => by
        have := bound hαA x y (k % ℓ)
        omega)
      (fun k => (w0 k : LocRing ℓ) * Mr (mm α A d x y (k % ℓ)) (k / ℓ) (U k) (E k) (ρf k)) zf
    refine ⟨Z, ?_, ?_⟩
    · rw [CatalanCore.Lai.NV.nodeL_apply, Finset.mul_sum, ← hZ1]
      refine Finset.sum_congr rfl fun k hk => ?_
      exact (hnf k (by have := Finset.mem_range.1 hk; omega)).2
    · rw [hZ2]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
      split_ifs
      · rw [map_mul, redQ_Mr, (hnf k hk').1]
        simp
      · rfl
  choose Zf hZf1 hZf2 using key
  refine ⟨Matrix.of Zf, fun x y => ?_, fun x y => hZf2 x y⟩
  simp only [Matrix.of_apply]
  rw [hZf1 x y, pow_add]
  ring

end CatalanCore.Lai.NV7

end

section
/-!
# Evaluation of the leading terms `Z̄_xy` (generic in the node data)

The sum over nodes `k = s + jℓ ≤ 6n` is reorganised by residue `s` and level `j`; the exponent
condition `ω(s) + mm(s) = e_x + f_y` is solved explicitly for each pair of basis types.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Reindexing `k = s + jℓ`. -/
theorem sum_range_div_mod {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ → M) (J N : ℕ) (hℓ0 : 0 < ℓ)
    (hN : N ≤ J * ℓ) :
    ∑ k ∈ range N, g (k % ℓ) (k / ℓ) =
      ∑ s ∈ range ℓ, ∑ j ∈ range J, if s + j * ℓ < N then g s j else 0 := by
  classical
  rw [Finset.sum_comm]
  rw [← Finset.sum_product']
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k => (k / ℓ, k % ℓ)) (fun p => p.2 + p.1 * ℓ) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk' := Finset.mem_range.1 hk
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    refine ⟨⟨?_, Nat.mod_lt _ hℓ0⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hℓ0]; nlinarith
    · have := Nat.mod_add_div' k ℓ
      show k % ℓ + k / ℓ * ℓ < N
      omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    exact Finset.mem_range.2 hp.2
  · intro k hk
    exact Nat.mod_add_div' k ℓ
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    have h1 : (p.2 + p.1 * ℓ) % ℓ = p.2 := by
      rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hp.1.2
    have h2 : (p.2 + p.1 * ℓ) / ℓ = p.1 := by
      rw [Nat.add_mul_div_right _ _ hℓ0, Nat.div_eq_of_lt hp.1.2]; simp
    simp only [h1, h2]
  · intro k hk
    rfl

/-- Sum over the nodes of a residue predicate, for a term vanishing at `j = 0`. -/
theorem sum_nodes_pred (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (T : ℕ → ZMod ℓ)
    (hT0 : ∀ k, k < ℓ → T k = 0) (h6 : 6 * n + 1 ≤ 3 * ℓ) :
    ∑ k ∈ range (6 * n + 1), (if P (k % ℓ) then T k else 0) =
      ∑ s ∈ range ℓ, if P s then
        ((if s + ℓ ≤ 6 * n then T (s + ℓ) else 0) + (if s + 2 * ℓ ≤ 6 * n then T (s + 2 * ℓ) else 0))
        else 0 := by
  have h := sum_range_div_mod (ℓ := ℓ) (fun s j => if P s then T (s + j * ℓ) else 0) 3 (6 * n + 1)
    hℓ.out.pos (by omega)
  have e1 : ∑ k ∈ range (6 * n + 1), (if P (k % ℓ) then T k else 0) =
      ∑ k ∈ range (6 * n + 1), (fun s j => if P s then T (s + j * ℓ) else 0) (k % ℓ) (k / ℓ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Nat.mod_add_div']
  rw [e1, h]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := Finset.mem_range.1 hs
  by_cases hP : P s
  · simp only [hP, if_true]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, zero_mul, add_zero]
    rw [hT0 s hs']
    simp only [ite_self, zero_add]
    have e1' : 1 * ℓ = ℓ := one_mul ℓ
    simp only [e1', show s + ℓ < 6 * n + 1 ↔ s + ℓ ≤ 6 * n by omega,
      show s + 2 * ℓ < 6 * n + 1 ↔ s + 2 * ℓ ≤ 6 * n by omega]
  · simp [hP]

variable {α A d : ℕ}

theorem eq_AA (hαA : α ≤ A) (r r' : Fin α) (i i' : Fin 3) (s : ℕ) :
    omg α A s + mm α A d (Sum.inl (r, i)) (Sum.inl (r', i')) s =
      exV α A d (Sum.inl (r, i)) + eyV α A d (Sum.inl (r', i')) ↔ (s = r ∧ (r : ℕ) = r') := by
  have h1 := i.2; have h2 := i'.2; have h3 := r.2; have h4 := r'.2
  by_cases hs : s < A + 1
  · rw [mm_lt α A d _ _ s hs]
    simp only [nuV, exV, eyV, omg, nu0, Fin.val_mk]
    split_ifs <;> omega
  · rw [mm_ge α A d _ _ s (by omega)]
    simp only [exV, eyV, omg]
    split_ifs <;> omega

theorem eq_EE (hαA : α ≤ A) (u u' : Fin (A + 1 - α)) (s : ℕ) :
    omg α A s + mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inl u')) s =
      exV α A d (Sum.inr (Sum.inl u)) + eyV α A d (Sum.inr (Sum.inl u')) ↔
        (s = α + u ∧ (u : ℕ) = u') := by
  have h1 := u.2; have h2 := u'.2
  by_cases hs : s < A + 1
  · rw [mm_lt α A d _ _ s hs]
    simp only [nuV, exV, eyV, omg, nu0, Fin.val_mk]
    split_ifs <;> omega
  · rw [mm_ge α A d _ _ s (by omega)]
    simp only [exV, eyV, omg]
    split_ifs <;> omega

theorem eq_EG (hαA : α ≤ A) (u : Fin (A + 1 - α)) (m : Fin d) (s : ℕ) :
    omg α A s + mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inr m)) s =
      exV α A d (Sum.inr (Sum.inl u)) + eyV α A d (Sum.inr (Sum.inr m)) ↔ s = α + u := by
  have h1 := u.2
  by_cases hs : s < A + 1
  · rw [mm_lt α A d _ _ s hs]
    simp only [nuV, exV, eyV, omg, nu0, Fin.val_mk]
    split_ifs <;> omega
  · rw [mm_ge α A d _ _ s (by omega)]
    simp only [exV, eyV, omg]
    split_ifs <;> omega

theorem eq_GE (hαA : α ≤ A) (u : Fin (A + 1 - α)) (m : Fin d) (s : ℕ) :
    omg α A s + mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inl u)) s =
      exV α A d (Sum.inr (Sum.inr m)) + eyV α A d (Sum.inr (Sum.inl u)) ↔ s = α + u := by
  have h1 := u.2
  by_cases hs : s < A + 1
  · rw [mm_lt α A d _ _ s hs]
    simp only [nuV, exV, eyV, omg, nu0, Fin.val_mk]
    split_ifs <;> omega
  · rw [mm_ge α A d _ _ s (by omega)]
    simp only [exV, eyV, omg]
    split_ifs <;> omega

theorem eq_GG (hαA : α ≤ A) (m m' : Fin d) (s : ℕ) :
    omg α A s + mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) s =
      exV α A d (Sum.inr (Sum.inr m)) + eyV α A d (Sum.inr (Sum.inr m')) ↔ α ≤ s := by
  by_cases hs : s < A + 1
  · rw [mm_lt α A d _ _ s hs]
    simp only [nuV, exV, eyV, omg, nu0, Fin.val_mk]
    split_ifs <;> omega
  · rw [mm_ge α A d _ _ s (by omega)]
    simp only [exV, eyV, omg]
    split_ifs <;> omega

end CatalanCore.Lai.NV7

end
