module

public import CatalanCore.Content.UnitClass
public import CatalanCore.Lai.NV7Gram

@[expose] public section

/-! # `CatalanCore.Lai.NV7Inst`: class arithmetic, node values and explicit leading entries (ledger LN06, LN07). -/

section
/-!
# Class arithmetic and numerical constants of the `E′` reduction (Lai's `J_n`, `2n < ℓ < 8n/3`)

For `k = s + jℓ` the digit data of `6n - k` and `2n + k`, the values of `δ`, `u_j`, `v_j`, and the
`κ`-constants of the unit parts in `ZMod ℓ`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem Hq_vals : Hq 1 0 = 0 ∧ Hq 1 1 = 1 ∧ Hq 1 2 = 3 / 2 ∧ Hq 1 3 = 11 / 6 ∧
    Hq 3 0 = 0 ∧ Hq 3 1 = 1 ∧ Hq 3 2 = 9 / 8 ∧ Hq 4 0 = 0 ∧ Hq 4 1 = 1 ∧ Hq 4 2 = 17 / 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Hq, Finset.sum_range_succ] <;> norm_num

/-- Digit data of the node `k = s + jℓ`. -/
theorem div_class (n α A s j : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs : s < ℓ)
    (hj : j ≤ 2) (hk : s + j * ℓ ≤ 6 * n) :
    (s + j * ℓ) / ℓ = j ∧
    (2 * n + (s + j * ℓ)) / ℓ = j + (if α ≤ s then 1 else 0) ∧
    (6 * n - (s + j * ℓ)) / ℓ = 2 - j - (if A < s then 1 else 0) := by
  have hℓ0 := hℓ.out.pos
  interval_cases j
  · refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_eq_of_lt (by omega)
    · split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · exact Nat.div_eq_of_lt (by omega)
    · split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · refine ⟨?_, ?_, ?_⟩
    · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · split_ifs with h
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)
    · split_ifs with h
      · exfalso; omega
      · exact Nat.div_eq_of_lt_le (by omega) (by omega)

theorem laiDelta_class (n α A s j : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs : s < ℓ)
    (hj : j ≤ 2) (hk : s + j * ℓ ≤ 6 * n) :
    laiDelta n ℓ (s + j * ℓ) = 5 * Hq 1 j - 3 * Hq 1 (j + (if α ≤ s then 1 else 0)) -
      2 * Hq 1 (2 - j - (if A < s then 1 else 0)) := by
  obtain ⟨h1, h2, h3⟩ := div_class n α A s j hα hA hAl hs hj hk
  unfold laiDelta
  rw [h1, h2, h3]

/-- numerical values of `v_j = -2 (H_j(3) δ + 3 H_j(4))`. -/
theorem vL_T1_1 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs : s < α)
    (hk : s + 1 * ℓ ≤ 6 * n) (hl : α ≤ A) : vL n ℓ (s + 1 * ℓ) 1 = -6 := by
  have := laiDelta_class (ℓ := ℓ) n α A s 1 hα hA hAl (by omega) (by omega) hk
  unfold vL
  rw [this, if_neg (by omega), if_neg (by omega)]
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  norm_num [a, b, c, d, e, f, g, h, i, j]

theorem vL_T1_2 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs : s < α)
    (hk : s + 2 * ℓ ≤ 6 * n) (hl : α ≤ A) : vL n ℓ (s + 2 * ℓ) 2 = -105 / 8 := by
  have := laiDelta_class (ℓ := ℓ) n α A s 2 hα hA hAl (by omega) (by omega) hk
  unfold vL
  rw [this, if_neg (by omega), if_neg (by omega)]
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  norm_num [a, b, c, d, e, f, g, h, i, j]

theorem vL_T2_1 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs1 : α ≤ s)
    (hs2 : s ≤ A) (hk : s + 1 * ℓ ≤ 6 * n) : vL n ℓ (s + 1 * ℓ) 1 = -3 := by
  have := laiDelta_class (ℓ := ℓ) n α A s 1 hα hA hAl (by omega) (by omega) hk
  unfold vL
  rw [this, if_pos hs1, if_neg (by omega)]
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  norm_num [a, b, c, d, e, f, g, h, i, j]

theorem vL_T2_2 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hs1 : α ≤ s)
    (hs2 : s ≤ A) (hk : s + 2 * ℓ ≤ 6 * n) : vL n ℓ (s + 2 * ℓ) 2 = -87 / 8 := by
  have := laiDelta_class (ℓ := ℓ) n α A s 2 hα hA hAl (by omega) (by omega) hk
  unfold vL
  rw [this, if_pos hs1, if_neg (by omega)]
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  norm_num [a, b, c, d, e, f, g, h, i, j]

theorem vL_T4_1 (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) (hαA : α ≤ A)
    (hs1 : A < s) (hs : s < ℓ) (hk : s + 1 * ℓ ≤ 6 * n) : vL n ℓ (s + 1 * ℓ) 1 = -7 := by
  have := laiDelta_class (ℓ := ℓ) n α A s 1 hα hA hAl hs (by omega) hk
  unfold vL
  rw [this, if_pos (by omega), if_pos hs1]
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  norm_num [a, b, c, d, e, f, g, h, i, j]

theorem uL_vals : uL 0 = 0 ∧ uL 1 = -2 ∧ uL 2 = -9 / 4 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  refine ⟨?_, ?_, ?_⟩ <;> simp [uL, e, f, g] <;> norm_num

theorem vL_zero (n p k : ℕ) : vL n p k 0 = 0 := by
  obtain ⟨a, b, c, d, e, f, g, h, i, j⟩ := Hq_vals
  simp [vL, e, h]

/-- redQ of a `ℤ_(ℓ)` element determined by `N x = m`. -/
theorem redQ_of_mul_eq (x : LocRing ℓ) (N : ℕ) (m : ℤ) (hN : (N : ZMod ℓ) ≠ 0)
    (h : (N : ℚ) * (x : ℚ) = (m : ℚ)) : redQ ℓ x = (m : ZMod ℓ) / N := by
  have h1 : (N : LocRing ℓ) * x = (m : LocRing ℓ) := by
    apply Subtype.ext
    push_cast
    exact h
  have h2 := congrArg (redQ ℓ) h1
  rw [map_mul, map_natCast, map_intCast] at h2
  rw [eq_div_iff hN, mul_comm]
  exact h2

end CatalanCore.Lai.NV7

end

section
open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem r6_eq (n α A : ℕ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) : r6 n ℓ = A := by
  unfold r6
  rw [← hA, show A + 2 * ℓ = A + ℓ * 2 by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hAl]

theorem q6_eq (n α A : ℕ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) : q6 n ℓ = 2 := by
  unfold q6
  apply Nat.div_eq_of_lt_le <;> omega

theorem r2_eq (n α : ℕ) (hα : α + 2 * n = ℓ) (hα1 : 1 ≤ α) : r2 n ℓ = 2 * n := by
  unfold r2
  exact Nat.mod_eq_of_lt (by omega)

theorem q2_eq (n α : ℕ) (hα : α + 2 * n = ℓ) (hα1 : 1 ≤ α) : q2 n ℓ = 0 := by
  unfold q2
  exact Nat.div_eq_of_lt (by omega)

theorem sig_eq (n α A s : ℕ) (hα : α + 2 * n = ℓ) (hα1 : 1 ≤ α) (hA : A + 2 * ℓ = 6 * n)
    (hAl : A < ℓ) (hαA : α ≤ A + 1) : sig n ℓ s = omg α A s := by
  unfold sig omg
  rw [r6_eq n α A hA hAl, r2_eq n α hα hα1]
  split_ifs <;> omega

theorem bflag_eq (n α A s : ℕ) (hA : A + 2 * ℓ = 6 * n) (hAl : A < ℓ) :
    bflag n ℓ s = if A < s then 1 else 0 := by
  unfold bflag; rw [r6_eq n α A hA hAl]

theorem eflag_eq (n α s : ℕ) (hα : α + 2 * n = ℓ) (hα1 : 1 ≤ α) :
    eflag n ℓ s = if α ≤ s then 1 else 0 := by
  unfold eflag; rw [r2_eq n α hα hα1]
  split_ifs <;> omega

section Kappa

variable (h2 : (2 : ZMod ℓ) ≠ 0)

include h2 in
theorem kappa_T1_1 : kappa ℓ 2 0 0 0 1 = 4 := by
  simp [kappa, fz, Nat.factorial]
  norm_num

include h2 in
theorem kappa_T1_2 : kappa ℓ 2 0 0 0 2 = 1 := by
  simp [kappa, fz, Nat.factorial]
  field_simp

include h2 in
theorem kappa_T2_1 : kappa ℓ 2 0 0 1 1 = -32 := by
  simp [kappa, fz, Nat.factorial]
  field_simp
  norm_num

include h2 in
theorem kappa_T2_2 : kappa ℓ 2 0 0 1 2 = -27 := by
  simp [kappa, fz, Nat.factorial]
  field_simp
  norm_num

include h2 in
theorem kappa_T4_1 : kappa ℓ 2 0 1 1 1 = -32 := by
  simp [kappa, fz, Nat.factorial]
  field_simp
  norm_num

end Kappa

end CatalanCore.Lai.NV7

end

section
/-!
# Explicit leading entries `Z̄_xy` of the `E′` Gram matrix

All statements are in `ZMod ℓ`, in terms of the node values (`NodeVals`): the unit parts `w0`, and the
residues of `U_k = ℓ³u_k`, `E_k = ℓ⁴e_k`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `ĉ(s)`: the unit part at the residue `s` (`T1`: `b = ε = 0`; `T2`: `ε = 1`; `T4`: `b = ε = 1`). -/
noncomputable def chatc (ℓ n α A s : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  chat ℓ A (2 * n) (if A < s then 1 else 0) (if α ≤ s then 1 else 0) s

/-- `W(s) = ĉ(s) · Pcore(s)`. -/
noncomputable def Wt (ℓ n α A s : ℕ) [Fact ℓ.Prime] : ZMod ℓ := chatc ℓ n α A s * PcoreR ℓ α A s

/-- Residues of the node data at the NV point (`b̄ = redQ b`). -/
structure NodeVals (ℓ n α A : ℕ) [Fact ℓ.Prime] (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ) :
    Prop where
  U0 : ∀ k, k < ℓ → redQ ℓ (U k) = 0
  E0 : ∀ k, k < ℓ → redQ ℓ (E k) = 0
  T1w1 : ∀ s, s < α → (w0 (s + 1 * ℓ) : ZMod ℓ) = 4 * chatc ℓ n α A s
  T1w2 : ∀ s, s < α → (w0 (s + 2 * ℓ) : ZMod ℓ) = 1 * chatc ℓ n α A s
  T1U1 : ∀ s, s < α → redQ ℓ (U (s + 1 * ℓ)) = b * (-2)
  T1U2 : ∀ s, s < α → redQ ℓ (U (s + 2 * ℓ)) = b * (-9 / 4)
  T1E1 : ∀ s, s < α → redQ ℓ (E (s + 1 * ℓ)) = b * (-6)
  T1E2 : ∀ s, s < α → redQ ℓ (E (s + 2 * ℓ)) = b * (-105 / 8)
  T2w1 : ∀ s, α ≤ s → s ≤ A → (w0 (s + 1 * ℓ) : ZMod ℓ) = -32 * chatc ℓ n α A s
  T2w2 : ∀ s, α ≤ s → s ≤ A → (w0 (s + 2 * ℓ) : ZMod ℓ) = -27 * chatc ℓ n α A s
  T2U1 : ∀ s, α ≤ s → s ≤ A → redQ ℓ (U (s + 1 * ℓ)) = b * (-2)
  T2U2 : ∀ s, α ≤ s → s ≤ A → redQ ℓ (U (s + 2 * ℓ)) = b * (-9 / 4)
  T2E1 : ∀ s, α ≤ s → s ≤ A → redQ ℓ (E (s + 1 * ℓ)) = b * (-3)
  T2E2 : ∀ s, α ≤ s → s ≤ A → redQ ℓ (E (s + 2 * ℓ)) = b * (-87 / 8)
  T4w1 : ∀ s, A < s → s < ℓ → (w0 (s + 1 * ℓ) : ZMod ℓ) = -32 * chatc ℓ n α A s
  T4U1 : ∀ s, A < s → s < ℓ → redQ ℓ (U (s + 1 * ℓ)) = b * (-2)
  T4E1 : ∀ s, A < s → s < ℓ → redQ ℓ (E (s + 1 * ℓ)) = b * (-7)

/-- the node term of the pair `(x, y)` at the node `k`. -/
noncomputable def Tk (α A d : ℕ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ) (x y : Ix α A d) (k : ℕ) : ZMod ℓ :=
  (w0 k : ZMod ℓ) * Mb (mm α A d x y (k % ℓ)) (k / ℓ) (redQ ℓ (U k)) (redQ ℓ (E k))
    (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y) (fun t => nuV α A d x t + nuV α A d y t) (k % ℓ))

theorem Mb_zero_zero (m : ℕ) (ρ : ZMod ℓ) : Mb m 0 (0 : ZMod ℓ) 0 ρ = 0 := by
  unfold Mb; split_ifs <;> simp

variable {α A d : ℕ}

theorem Tk_zero (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (k : ℕ) (hk : k < ℓ) :
    Tk α A d w0 U E x y k = 0 := by
  unfold Tk
  rw [Nat.div_eq_of_lt hk, hv.U0 k hk, hv.E0 k hk, Mb_zero_zero, mul_zero]

/-- Reduction of the node sum of a pair to its support. -/
theorem Zbar_reduce (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (h6 : 6 * n + 1 ≤ 3 * ℓ) (x y : Ix α A d)
    (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ s, omg α A s + mm α A d x y s = exV α A d x + eyV α A d y ↔ P s) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
        Tk α A d w0 U E x y k else 0) =
    ∑ s ∈ range ℓ, if P s then
      ((if s + ℓ ≤ 6 * n then Tk α A d w0 U E x y (s + ℓ) else 0) +
        (if s + 2 * ℓ ≤ 6 * n then Tk α A d w0 U E x y (s + 2 * ℓ) else 0)) else 0 := by
  classical
  have h1 : (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d x y (k % ℓ) = exV α A d x + eyV α A d y then
        Tk α A d w0 U E x y k else 0) =
      ∑ k ∈ range (6 * n + 1), if P (k % ℓ) then Tk α A d w0 U E x y k else 0 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hP]
  rw [h1]
  exact sum_nodes_pred n P (Tk α A d w0 U E x y) (fun k hk => Tk_zero n b w0 U E hv x y k hk) h6

theorem Mb_scale (m j : ℕ) (b U E ρ : ZMod ℓ) :
    Mb m j (b * U) (b * E) ρ = b * ρ * Mb m j U E 1 := by
  unfold Mb; split_ifs <;> ring

theorem mod_div_node (s j : ℕ) (hs : s < ℓ) : (s + j * ℓ) % ℓ = s ∧ (s + j * ℓ) / ℓ = j := by
  constructor
  · rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hs
  · rw [Nat.add_mul_div_right _ _ hℓ.out.pos, Nat.div_eq_of_lt hs]; simp

/-- The Fin-indexed cofactor value equals `(-s)^w · Pcore(s)`. -/
theorem rhoZ_core (α A w s : ℕ) (ν : Fin (A + 1) → ℕ)
    (hν : ∀ t : Fin (A + 1), (t : ℕ) ≠ s → ν t = 2 * (if (t : ℕ) < α then 3 else 1)) :
    rhoZ ℓ (A + 1) w ν s = (-(s : ZMod ℓ)) ^ w * PcoreR ℓ α A s := by
  unfold rhoZ PcoreR
  by_cases h : s < A + 1
  · rw [dif_pos h, if_pos h]
    congr 1
    refine Finset.prod_nbij (fun r : Fin (A + 1) => (r : ℕ)) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [mem_erase, mem_univ, and_true] at hr
      simp only [mem_erase, mem_range]
      exact ⟨fun h' => hr (Fin.ext h'), r.2⟩
    · intro r _ r' _ hrr; exact Fin.ext hrr
    · intro t ht
      simp only [coe_erase, coe_range, Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff] at ht
      refine ⟨⟨t, ht.1⟩, ?_, rfl⟩
      simp only [coe_erase, coe_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
      intro h'; exact ht.2 (by simpa using congrArg Fin.val h')
    · intro r hr
      simp only [mem_erase, mem_univ, and_true] at hr
      rw [hν r (fun h' => hr (Fin.ext h'))]
  · rw [dif_neg h, if_neg h]
    congr 1
    rw [← Fin.prod_univ_eq_prod_range (fun t : ℕ => (((t : ℕ) : ZMod ℓ) - s) ^
      (2 * (if t < α then 3 else 1))) (A + 1)]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [hν r (by have := r.2; omega)]

theorem node_T1_1 (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (s : ℕ) (hs : s < α) (hsl : s < ℓ) :
    Tk α A d w0 U E x y (s + 1 * ℓ) = 4 * chatc ℓ n α A s *
      Mb (mm α A d x y s) 1 (b * (-2)) (b * (-6))
        (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
          (fun t => nuV α A d x t + nuV α A d y t) s) := by
  obtain ⟨h1, h2⟩ := mod_div_node (ℓ := ℓ) s 1 hsl
  unfold Tk
  rw [h1, h2, hv.T1w1 s hs, hv.T1U1 s hs, hv.T1E1 s hs]

theorem node_T1_2 (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (s : ℕ) (hs : s < α) (hsl : s < ℓ) :
    Tk α A d w0 U E x y (s + 2 * ℓ) = 1 * chatc ℓ n α A s *
      Mb (mm α A d x y s) 2 (b * (-9 / 4)) (b * (-105 / 8))
        (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
          (fun t => nuV α A d x t + nuV α A d y t) s) := by
  obtain ⟨h1, h2⟩ := mod_div_node (ℓ := ℓ) s 2 hsl
  unfold Tk
  rw [h1, h2, hv.T1w2 s hs, hv.T1U2 s hs, hv.T1E2 s hs]

theorem node_T2_1 (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (s : ℕ) (hs1 : α ≤ s) (hs2 : s ≤ A)
    (hsl : s < ℓ) :
    Tk α A d w0 U E x y (s + 1 * ℓ) = -32 * chatc ℓ n α A s *
      Mb (mm α A d x y s) 1 (b * (-2)) (b * (-3))
        (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
          (fun t => nuV α A d x t + nuV α A d y t) s) := by
  obtain ⟨h1, h2⟩ := mod_div_node (ℓ := ℓ) s 1 hsl
  unfold Tk
  rw [h1, h2, hv.T2w1 s hs1 hs2, hv.T2U1 s hs1 hs2, hv.T2E1 s hs1 hs2]

theorem node_T2_2 (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (s : ℕ) (hs1 : α ≤ s) (hs2 : s ≤ A)
    (hsl : s < ℓ) :
    Tk α A d w0 U E x y (s + 2 * ℓ) = -27 * chatc ℓ n α A s *
      Mb (mm α A d x y s) 2 (b * (-9 / 4)) (b * (-87 / 8))
        (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
          (fun t => nuV α A d x t + nuV α A d y t) s) := by
  obtain ⟨h1, h2⟩ := mod_div_node (ℓ := ℓ) s 2 hsl
  unfold Tk
  rw [h1, h2, hv.T2w2 s hs1 hs2, hv.T2U2 s hs1 hs2, hv.T2E2 s hs1 hs2]

theorem node_T4_1 (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
    (hv : NodeVals ℓ n α A b w0 U E) (x y : Ix α A d) (s : ℕ) (hs1 : A < s) (hsl : s < ℓ) :
    Tk α A d w0 U E x y (s + 1 * ℓ) = -32 * chatc ℓ n α A s *
      Mb (mm α A d x y s) 1 (b * (-2)) (b * (-7))
        (rhoZ ℓ (A + 1) (wV α A d x + wV α A d y)
          (fun t => nuV α A d x t + nuV α A d y t) s) := by
  obtain ⟨h1, h2⟩ := mod_div_node (ℓ := ℓ) s 1 hsl
  unfold Tk
  rw [h1, h2, hv.T4w1 s hs1 hsl, hv.T4U1 s hs1 hsl, hv.T4E1 s hs1 hsl]


end CatalanCore.Lai.NV7

end

section
open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α A d : ℕ}

section Pairs

variable (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
  (hv : NodeVals ℓ n α A b w0 U E) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hαA : α ≤ A)
  (hAl : A + 1 < ℓ)

include hv hα hA hαA hAl in
theorem Zbar_AA (r r' : Fin α) (i i' : Fin 3) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d (Sum.inl (r, i)) (Sum.inl (r', i')) (k % ℓ) =
          exV α A d (Sum.inl (r, i)) + eyV α A d (Sum.inl (r', i')) then
        Tk α A d w0 U E (Sum.inl (r, i)) (Sum.inl (r', i')) k else 0) =
      if r = r' then b * Wt ℓ n α A r *
        (4 * Mb ((i : ℕ) + i') 1 (-2) (-6) 1 + 1 * Mb ((i : ℕ) + i') 2 (-9 / 4) (-105 / 8) 1)
      else 0 := by
  classical
  have h6 : 6 * n + 1 ≤ 3 * ℓ := by omega
  have hr := r.2; have hr' := r'.2; have hi := i.2; have hi' := i'.2
  rw [Zbar_reduce n b w0 U E hv h6 _ _ (fun s => s = (r : ℕ) ∧ (r : ℕ) = r')
    (eq_AA hαA r r' i i')]
  rw [Finset.sum_eq_single (r : ℕ)]
  · by_cases hrr : (r : ℕ) = r'
    · have hrr' : r = r' := Fin.ext hrr
      subst hrr'
      simp only [true_and, if_true]
      have hP := (eq_AA (d := d) hαA r r i i' r).2 ⟨rfl, rfl⟩
      have hom : omg α A (r : ℕ) = 0 := by simp [omg, hr]
      have hmm : mm α A d (Sum.inl (r, i)) (Sum.inl (r, i')) r = (i : ℕ) + i' := by
        simp only [exV, eyV, hom] at hP; omega
      rw [if_pos (by omega), if_pos (by omega)]
      rw [show (r : ℕ) + ℓ = (r : ℕ) + 1 * ℓ by ring]
      rw [node_T1_1 n b w0 U E hv _ _ (r : ℕ) hr (by omega),
        node_T1_2 n b w0 U E hv _ _ (r : ℕ) hr (by omega)]
      have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inl (r, i)) + wV α A d (Sum.inl (r, i')))
          (fun t => nuV α A d (Sum.inl (r, i)) t + nuV α A d (Sum.inl (r, i')) t) r =
          PcoreR ℓ α A r := by
        rw [rhoZ_core α A _ r _ (fun t ht => by
          simp only [nuV, nu0]
          rw [if_neg ht, if_neg ht]
          omega)]
        simp [wV]
      rw [hrho, hmm, Mb_scale, Mb_scale]
      unfold Wt
      ring
    · have hrr' : ¬ r = r' := fun h => hrr (by rw [h])
      simp [hrr, hrr']
  · intro s _ hne
    simp [hne]
  · intro h; exfalso; apply h; rw [mem_range]; omega

include hv hα hA hαA hAl in
theorem Zbar_EE (u u' : Fin (A + 1 - α)) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inl u')) (k % ℓ) =
          exV α A d (Sum.inr (Sum.inl u)) + eyV α A d (Sum.inr (Sum.inl u')) then
        Tk α A d w0 U E (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inl u')) k else 0) =
      if u = u' then b * Wt ℓ n α A (α + u) *
        (-32 * Mb 0 1 (-2) (-3) 1 + -27 * Mb 0 2 (-9 / 4) (-87 / 8) 1)
      else 0 := by
  classical
  have h6 : 6 * n + 1 ≤ 3 * ℓ := by omega
  have hu := u.2; have hu' := u'.2
  rw [Zbar_reduce n b w0 U E hv h6 _ _ (fun s => s = α + (u : ℕ) ∧ (u : ℕ) = u')
    (eq_EE hαA u u')]
  rw [Finset.sum_eq_single (α + (u : ℕ))]
  · by_cases huu : (u : ℕ) = u'
    · have huu' : u = u' := Fin.ext huu
      subst huu'
      simp only [true_and, if_true]
      have hP := (eq_EE (d := d) hαA u u (α + u)).2 ⟨rfl, rfl⟩
      have hom : omg α A (α + (u : ℕ)) = 3 := by unfold omg; rw [if_neg (by omega), if_pos (by omega)]
      have hmm : mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inl u)) (α + u) = 0 := by
        simp only [exV, eyV, hom] at hP; omega
      rw [if_pos (by omega), if_pos (by omega)]
      rw [show α + (u : ℕ) + ℓ = α + (u : ℕ) + 1 * ℓ by ring]
      rw [node_T2_1 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega),
        node_T2_2 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega)]
      have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inr (Sum.inl u)) + wV α A d (Sum.inr (Sum.inl u)))
          (fun t => nuV α A d (Sum.inr (Sum.inl u)) t + nuV α A d (Sum.inr (Sum.inl u)) t) (α + u) =
          PcoreR ℓ α A (α + u) := by
        rw [rhoZ_core α A _ (α + u) _ (fun t ht => by
          simp only [nuV, nu0]
          rw [if_neg ht]
          omega)]
        simp [wV]
      rw [hrho, hmm, Mb_scale, Mb_scale]
      unfold Wt
      ring
    · have huu' : ¬ u = u' := fun h => huu (by rw [h])
      simp [huu, huu']
  · intro s _ hne
    simp [hne]
  · intro h; exfalso; apply h; rw [mem_range]; omega

end Pairs

end CatalanCore.Lai.NV7

end

section
open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {α A d : ℕ}

section Pairs3

variable (n : ℕ) (b : ZMod ℓ) (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ)
  (hv : NodeVals ℓ n α A b w0 U E) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hαA : α ≤ A)
  (hAl : A + 1 < ℓ)

include hv hα hA hαA hAl in
theorem Zbar_EG (u : Fin (A + 1 - α)) (m : Fin d) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inr m)) (k % ℓ) =
          exV α A d (Sum.inr (Sum.inl u)) + eyV α A d (Sum.inr (Sum.inr m)) then
        Tk α A d w0 U E (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inr m)) k else 0) =
      b * Wt ℓ n α A (α + u) * (-((α + (u : ℕ) : ℕ) : ZMod ℓ)) ^ (m : ℕ) *
        (-32 * Mb 1 1 (-2) (-3) 1 + -27 * Mb 1 2 (-9 / 4) (-87 / 8) 1) := by
  classical
  have h6 : 6 * n + 1 ≤ 3 * ℓ := by omega
  have hu := u.2
  rw [Zbar_reduce n b w0 U E hv h6 _ _ (fun s => s = α + (u : ℕ)) (eq_EG hαA u m)]
  rw [Finset.sum_eq_single (α + (u : ℕ))]
  · simp only [if_true]
    have hP := (eq_EG (d := d) hαA u m (α + u)).2 rfl
    have hom : omg α A (α + (u : ℕ)) = 3 := by unfold omg; rw [if_neg (by omega), if_pos (by omega)]
    have hmm : mm α A d (Sum.inr (Sum.inl u)) (Sum.inr (Sum.inr m)) (α + u) = 1 := by
      simp only [exV, eyV, hom] at hP; omega
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show α + (u : ℕ) + ℓ = α + (u : ℕ) + 1 * ℓ by ring]
    rw [node_T2_1 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega),
      node_T2_2 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega)]
    have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inr (Sum.inl u)) + wV α A d (Sum.inr (Sum.inr m)))
        (fun t => nuV α A d (Sum.inr (Sum.inl u)) t + nuV α A d (Sum.inr (Sum.inr m)) t) (α + u) =
        (-((α + (u : ℕ) : ℕ) : ZMod ℓ)) ^ (m : ℕ) * PcoreR ℓ α A (α + u) := by
      rw [rhoZ_core α A _ (α + u) _ (fun t ht => by
        simp only [nuV, nu0]
        rw [if_neg ht]
        omega)]
      simp [wV]
    rw [hrho, hmm, Mb_scale, Mb_scale]
    unfold Wt
    ring
  · intro s _ hne
    simp [hne]
  · intro h; exfalso; apply h; rw [mem_range]; omega

include hv hα hA hαA hAl in
theorem Zbar_GE (u : Fin (A + 1 - α)) (m : Fin d) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inl u)) (k % ℓ) =
          exV α A d (Sum.inr (Sum.inr m)) + eyV α A d (Sum.inr (Sum.inl u)) then
        Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inl u)) k else 0) =
      b * Wt ℓ n α A (α + u) * (-((α + (u : ℕ) : ℕ) : ZMod ℓ)) ^ (m : ℕ) *
        (-32 * Mb 1 1 (-2) (-3) 1 + -27 * Mb 1 2 (-9 / 4) (-87 / 8) 1) := by
  classical
  have h6 : 6 * n + 1 ≤ 3 * ℓ := by omega
  have hu := u.2
  rw [Zbar_reduce n b w0 U E hv h6 _ _ (fun s => s = α + (u : ℕ)) (eq_GE hαA u m)]
  rw [Finset.sum_eq_single (α + (u : ℕ))]
  · simp only [if_true]
    have hP := (eq_GE (d := d) hαA u m (α + u)).2 rfl
    have hom : omg α A (α + (u : ℕ)) = 3 := by unfold omg; rw [if_neg (by omega), if_pos (by omega)]
    have hmm : mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inl u)) (α + u) = 1 := by
      simp only [exV, eyV, hom] at hP; omega
    rw [if_pos (by omega), if_pos (by omega)]
    rw [show α + (u : ℕ) + ℓ = α + (u : ℕ) + 1 * ℓ by ring]
    rw [node_T2_1 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega),
      node_T2_2 n b w0 U E hv _ _ (α + (u : ℕ)) (by omega) (by omega) (by omega)]
    have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inr (Sum.inr m)) + wV α A d (Sum.inr (Sum.inl u)))
        (fun t => nuV α A d (Sum.inr (Sum.inr m)) t + nuV α A d (Sum.inr (Sum.inl u)) t) (α + u) =
        (-((α + (u : ℕ) : ℕ) : ZMod ℓ)) ^ (m : ℕ) * PcoreR ℓ α A (α + u) := by
      rw [rhoZ_core α A _ (α + u) _ (fun t ht => by
        simp only [nuV, nu0]
        rw [if_neg ht]
        omega)]
      simp [wV]
    rw [hrho, hmm, Mb_scale, Mb_scale]
    unfold Wt
    ring
  · intro s _ hne
    simp [hne]
  · intro h; exfalso; apply h; rw [mem_range]; omega

include hv hα hA hαA hAl in
theorem Zbar_GG (m m' : Fin d) :
    (∑ k ∈ range (6 * n + 1),
      if omg α A (k % ℓ) + mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (k % ℓ) =
          exV α A d (Sum.inr (Sum.inr m)) + eyV α A d (Sum.inr (Sum.inr m')) then
        Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) k else 0) =
      b * ((-32 * Mb 2 1 (-2) (-3) 1 + -27 * Mb 2 2 (-9 / 4) (-87 / 8) 1) *
          ∑ s ∈ Ico α (A + 1), Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m') +
        (-32 * Mb 0 1 (-2) (-7) 1) *
          ∑ s ∈ Ico (A + 1) ℓ, Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m')) := by
  classical
  have h6 : 6 * n + 1 ≤ 3 * ℓ := by omega
  rw [Zbar_reduce n b w0 U E hv h6 _ _ (fun s => α ≤ s) (eq_GG hαA m m')]
  rw [← Finset.sum_range_add_sum_Ico _ (show A + 1 ≤ ℓ by omega),
    ← Finset.sum_range_add_sum_Ico _ (show α ≤ A + 1 by omega)]
  have e0 : ∑ s ∈ range α, (if α ≤ s then
      ((if s + ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + ℓ) else 0) +
        (if s + 2 * ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + 2 * ℓ)
          else 0)) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rw [if_neg (by have := mem_range.1 hs; omega)]
  have e2 : ∑ s ∈ Ico α (A + 1), (if α ≤ s then
      ((if s + ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + ℓ) else 0) +
        (if s + 2 * ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + 2 * ℓ)
          else 0)) else 0) =
      b * ((-32 * Mb 2 1 (-2) (-3) 1 + -27 * Mb 2 2 (-9 / 4) (-87 / 8) 1) *
          ∑ s ∈ Ico α (A + 1), Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m')) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := mem_Ico.1 hs
    have hP := (eq_GG (d := d) hαA m m' s).2 hs'.1
    have hom : omg α A s = 3 := by unfold omg; rw [if_neg (by omega), if_pos (by omega)]
    have hmm : mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) s = 2 := by
      simp only [exV, eyV, hom] at hP; omega
    rw [if_pos hs'.1, if_pos (by omega), if_pos (by omega)]
    rw [show s + ℓ = s + 1 * ℓ by ring]
    rw [node_T2_1 n b w0 U E hv _ _ s hs'.1 (by omega) (by omega),
      node_T2_2 n b w0 U E hv _ _ s hs'.1 (by omega) (by omega)]
    have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inr (Sum.inr m)) + wV α A d (Sum.inr (Sum.inr m')))
        (fun t => nuV α A d (Sum.inr (Sum.inr m)) t + nuV α A d (Sum.inr (Sum.inr m')) t) s =
        (-(s : ZMod ℓ)) ^ ((m : ℕ) + m') * PcoreR ℓ α A s := by
      rw [rhoZ_core α A _ s _ (fun t ht => by simp only [nuV, nu0]; omega)]
      simp [wV]
    rw [hrho, hmm, Mb_scale, Mb_scale]
    unfold Wt
    ring
  have e4 : ∑ s ∈ Ico (A + 1) ℓ, (if α ≤ s then
      ((if s + ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + ℓ) else 0) +
        (if s + 2 * ℓ ≤ 6 * n then Tk α A d w0 U E (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) (s + 2 * ℓ)
          else 0)) else 0) =
      b * ((-32 * Mb 0 1 (-2) (-7) 1) *
          ∑ s ∈ Ico (A + 1) ℓ, Wt ℓ n α A s * (-(s : ZMod ℓ)) ^ ((m : ℕ) + m')) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hs' := mem_Ico.1 hs
    have hP := (eq_GG (d := d) hαA m m' s).2 (by omega)
    have hom : omg α A s = 5 := by unfold omg; rw [if_neg (by omega), if_neg (by omega)]
    have hmm : mm α A d (Sum.inr (Sum.inr m)) (Sum.inr (Sum.inr m')) s = 0 := by
      simp only [exV, eyV, hom] at hP; omega
    rw [if_pos (by omega), if_pos (by omega), if_neg (by omega), add_zero]
    rw [show s + ℓ = s + 1 * ℓ by ring]
    rw [node_T4_1 n b w0 U E hv _ _ s hs'.1 hs'.2]
    have hrho : rhoZ ℓ (A + 1) (wV α A d (Sum.inr (Sum.inr m)) + wV α A d (Sum.inr (Sum.inr m')))
        (fun t => nuV α A d (Sum.inr (Sum.inr m)) t + nuV α A d (Sum.inr (Sum.inr m')) t) s =
        (-(s : ZMod ℓ)) ^ ((m : ℕ) + m') * PcoreR ℓ α A s := by
      rw [rhoZ_core α A _ s _ (fun t ht => by simp only [nuV, nu0]; omega)]
      simp [wV]
    rw [hrho, hmm, Mb_scale]
    unfold Wt
    ring
  rw [e0, e2, e4]
  ring

end Pairs3

end CatalanCore.Lai.NV7

end

section
/-!
# The node values at an NV point: construction of `NodeVals`
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Lai CatalanCore.Content

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem redQ_ofEq (U b c zU : LocRing ℓ) (h : (U : ℚ) = (b : ℚ) * (c : ℚ) + (ℓ : ℚ) * (zU : ℚ)) :
    redQ ℓ U = redQ ℓ b * redQ ℓ c := by
  have h1 : U = b * c + (ℓ : LocRing ℓ) * zU := by
    apply Subtype.ext
    push_cast
    exact h
  rw [h1, map_add, map_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

theorem exists_nodeVals (n α A : ℕ) (hα : α + 2 * n = ℓ) (hA : A + 2 * ℓ = 6 * n) (hα1 : 1 ≤ α)
    (hαA : α ≤ A) (hAl : A + 1 < ℓ) (h2 : (2 : ZMod ℓ) ≠ 0) (h8 : 8 * n < ℓ ^ 2)
    (a b X' : LocRing ℓ) :
    ∃ (w0 : ℕ → ℕ) (U E : ℕ → LocRing ℓ),
      (∀ k ≤ 6 * n, (laiCoef n k : ℚ) = (ℓ : ℚ) ^ (omg α A (k % ℓ)) * (w0 k : ℚ)) ∧
      (∀ k ≤ 6 * n, (ℓ : ℚ) ^ 3 * (-3 * (a : ℚ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) = (U k : ℚ)) ∧
      (∀ k ≤ 6 * n, (ℓ : ℚ) ^ 4 * (laiH n k * (3 * (a : ℚ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - (a : ℚ) * Hq 3 k - (b : ℚ) * Hq 4 k)) = (E k : ℚ)) ∧
      NodeVals ℓ n α A (redQ ℓ b) w0 U E := by
  have h3ℓ : 3 ≤ ℓ := by omega
  have hp := hℓ.out
  -- unit parts
  have hw : ∀ k, ∃ w : ℕ, k ≤ 6 * n → (laiCoef n k = ℓ ^ sig n ℓ (k % ℓ) * w ∧
      (w : ZMod ℓ) = kappa ℓ (q6 n ℓ) (q2 n ℓ) (bflag n ℓ (k % ℓ)) (eflag n ℓ (k % ℓ)) (k / ℓ) *
        chat ℓ (r6 n ℓ) (r2 n ℓ) (bflag n ℓ (k % ℓ)) (eflag n ℓ (k % ℓ)) (k % ℓ)) := by
    intro k
    by_cases hk : k ≤ 6 * n
    · obtain ⟨w, h1, h2', _⟩ := laiCoef_unit (p := ℓ) (n := n) (by omega) h3ℓ k hk
      exact ⟨w, fun _ => ⟨h1, h2'⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose w0 hw0 using hw
  have hUE : ∀ k, ∃ U E zU zE : LocRing ℓ, k ≤ 6 * n →
      ((ℓ : ℚ) ^ 3 * (-3 * (a : ℚ) * Hq 2 k - 2 * (b : ℚ) * Hq 3 k) = (U : ℚ) ∧
      (ℓ : ℚ) ^ 4 * (laiH n k * (3 * (a : ℚ) * Hq 2 k + 2 * (b : ℚ) * Hq 3 k) +
          6 * ((X' : ℚ) / (ℓ : ℚ) ^ 3 - (a : ℚ) * Hq 3 k - (b : ℚ) * Hq 4 k)) = (E : ℚ) ∧
      (U : ℚ) = (b : ℚ) * uL (k / ℓ) + (ℓ : ℚ) * (zU : ℚ) ∧
      (E : ℚ) = (b : ℚ) * vL n ℓ k (k / ℓ) + (ℓ : ℚ) * (zE : ℚ)) := by
    intro k
    by_cases hk : k ≤ 6 * n
    · obtain ⟨U, E, zU, zE, h1, h2', h3, h4⟩ := nv_UE n k hk h8 a b X'
      exact ⟨U, E, zU, zE, fun _ => ⟨h1, h2', h3, h4⟩⟩
    · exact ⟨0, 0, 0, 0, fun h => absurd h hk⟩
  choose U E zU zE hUE using hUE
  -- reductions
  have hl2 : ∀ j, j < ℓ → (uL j) ∈ LocRing ℓ := fun j hj => uL_mem j hj
  have hredU : ∀ k, k ≤ 6 * n → ∀ c : LocRing ℓ, (c : ℚ) = uL (k / ℓ) →
      redQ ℓ (U k) = redQ ℓ b * redQ ℓ c := by
    intro k hk c hc
    refine redQ_ofEq (U k) b c (zU k) ?_
    rw [hc]; exact (hUE k hk).2.2.1
  have hredE : ∀ k, k ≤ 6 * n → ∀ c : LocRing ℓ, (c : ℚ) = vL n ℓ k (k / ℓ) →
      redQ ℓ (E k) = redQ ℓ b * redQ ℓ c := by
    intro k hk c hc
    refine redQ_ofEq (E k) b c (zE k) ?_
    rw [hc]; exact (hUE k hk).2.2.2
  have hd8 : (8 : ZMod ℓ) ≠ 0 := by
    have : (8 : ZMod ℓ) = 2 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have hd4 : (4 : ZMod ℓ) ≠ 0 := by
    have : (4 : ZMod ℓ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  have hd1 : ((1 : ℕ) : ZMod ℓ) ≠ 0 := by simp
  -- constants as elements of ℤ_(ℓ)
  have cst : ∀ (q : ℚ) (N : ℕ) (m : ℤ), q ∈ LocRing ℓ → (N : ZMod ℓ) ≠ 0 → (N : ℚ) * q = m →
      ∀ c : LocRing ℓ, (c : ℚ) = q → redQ ℓ c = (m : ZMod ℓ) / N := by
    intro q N m hq hN h c hc
    exact redQ_of_mul_eq c N m hN (by rw [hc]; exact h)
  refine ⟨w0, U, E, ?_, fun k hk => (hUE k hk).1, fun k hk => (hUE k hk).2.1, ?_⟩
  · intro k hk
    have := (hw0 k hk).1
    rw [sig_eq n α A (k % ℓ) hα hα1 hA (by omega) (by omega)] at this
    exact_mod_cast this
  · -- NodeVals
    have hwk : ∀ s j : ℕ, s < ℓ → s + j * ℓ ≤ 6 * n → (w0 (s + j * ℓ) : ZMod ℓ) =
        kappa ℓ 2 0 (if A < s then 1 else 0) (if α ≤ s then 1 else 0) j * chatc ℓ n α A s := by
      intro s j hs hk
      have hh := (hw0 (s + j * ℓ) hk).2
      obtain ⟨hm, hd⟩ := mod_div_node (ℓ := ℓ) s j hs
      rw [hh, hm, hd, q6_eq n α A hA (by omega), q2_eq n α hα hα1, r6_eq n α A hA (by omega),
        r2_eq n α hα hα1, bflag_eq n α A s hA (by omega), eflag_eq n α s hα hα1]
      rfl
    have hu1 : ∀ k, k ≤ 6 * n → k / ℓ = 1 → redQ ℓ (U k) = redQ ℓ b * (-2) := by
      intro k hk h1
      have hc : (((-2 : LocRing ℓ)) : ℚ) = uL (k / ℓ) := by
        rw [h1, (uL_vals).2.1]; simp; rfl
      have := hredU k hk (-2) hc
      rw [this, map_neg, map_ofNat]
    have hu2 : ∀ k, k ≤ 6 * n → k / ℓ = 2 → redQ ℓ (U k) = redQ ℓ b * (-9 / 4) := by
      intro k hk h1
      have hc : redQ ℓ (⟨uL 2, hl2 2 (by omega)⟩ : LocRing ℓ) = (-9 : ZMod ℓ) / 4 := by
        have := redQ_of_mul_eq (ℓ := ℓ) ⟨uL 2, hl2 2 (by omega)⟩ 4 (-9) hd4 (by
          show ((4 : ℕ) : ℚ) * uL 2 = ((-9 : ℤ) : ℚ)
          rw [(uL_vals).2.2]; norm_num)
        simpa using this
      have := hredU k hk ⟨uL 2, hl2 2 (by omega)⟩ (by rw [h1])
      rw [this, hc]
    have hv : ∀ k j (v : ℚ) (N : ℕ) (m : ℤ), k ≤ 6 * n → k / ℓ = j → vL n ℓ k j = v →
        (N : ZMod ℓ) ≠ 0 → (N : ℚ) * v = m → redQ ℓ (E k) = redQ ℓ b * ((m : ZMod ℓ) / N) := by
      intro k j v N m hk hj hvv hN hNm
      have hjl : j < ℓ := by
        rw [← hj, Nat.div_lt_iff_lt_mul hℓ.out.pos]; nlinarith
      have hmem : vL n ℓ k j ∈ LocRing ℓ := by
        have := vL_mem (p := ℓ) n k j h8 hk hjl
        exact this
      have := hredE k hk ⟨vL n ℓ k j, hmem⟩ (by rw [hj])
      rw [this]
      congr 1
      exact redQ_of_mul_eq (ℓ := ℓ) ⟨vL n ℓ k j, hmem⟩ N m hN (by
        show (N : ℚ) * vL n ℓ k j = (m : ℚ)
        rw [hvv]; exact hNm)
    refine
      { U0 := fun k hk => ?_
        E0 := fun k hk => ?_
        T1w1 := fun s hs => ?_
        T1w2 := fun s hs => ?_
        T1U1 := fun s hs => ?_
        T1U2 := fun s hs => ?_
        T1E1 := fun s hs => ?_
        T1E2 := fun s hs => ?_
        T2w1 := fun s hs hs' => ?_
        T2w2 := fun s hs hs' => ?_
        T2U1 := fun s hs hs' => ?_
        T2U2 := fun s hs hs' => ?_
        T2E1 := fun s hs hs' => ?_
        T2E2 := fun s hs hs' => ?_
        T4w1 := fun s hs hs' => ?_
        T4U1 := fun s hs hs' => ?_
        T4E1 := fun s hs hs' => ?_ }
    · have hk' : k ≤ 6 * n := by omega
      have := hredU k hk' 0 (by rw [Nat.div_eq_of_lt hk, (uL_vals).1]; rfl)
      rw [this]; simp
    · have hk' : k ≤ 6 * n := by omega
      have := hredE k hk' 0 (by rw [Nat.div_eq_of_lt hk, vL_zero]; rfl)
      rw [this]; simp
    · rw [hwk s 1 (by omega) (by omega), if_neg (by omega), if_neg (by omega), kappa_T1_1 h2]
    · rw [hwk s 2 (by omega) (by omega), if_neg (by omega), if_neg (by omega), kappa_T1_2 h2]
    · exact hu1 _ (by omega) (mod_div_node s 1 (by omega)).2
    · exact hu2 _ (by omega) (mod_div_node s 2 (by omega)).2
    · simpa using hv _ 1 (-6) 1 (-6) (by omega) (mod_div_node s 1 (by omega)).2
        (vL_T1_1 n α A s hα hA (by omega) hs (by omega) hαA) (by simp) (by norm_num)
    · have := hv (s + 2 * ℓ) 2 (-105 / 8) 8 (-105) (by omega) (mod_div_node s 2 (by omega)).2
        (vL_T1_2 n α A s hα hA (by omega) hs (by omega) hαA) (by simpa using hd8) (by norm_num)
      rw [this]; push_cast; ring
    · rw [hwk s 1 (by omega) (by omega), if_neg (by omega), if_pos hs, kappa_T2_1 h2]
    · rw [hwk s 2 (by omega) (by omega), if_neg (by omega), if_pos hs, kappa_T2_2 h2]
    · exact hu1 _ (by omega) (mod_div_node s 1 (by omega)).2
    · exact hu2 _ (by omega) (mod_div_node s 2 (by omega)).2
    · simpa using hv _ 1 (-3) 1 (-3) (by omega) (mod_div_node s 1 (by omega)).2
        (vL_T2_1 n α A s hα hA (by omega) hs hs' (by omega)) (by simp) (by norm_num)
    · have := hv (s + 2 * ℓ) 2 (-87 / 8) 8 (-87) (by omega) (mod_div_node s 2 (by omega)).2
        (vL_T2_2 n α A s hα hA (by omega) hs hs' (by omega)) (by simpa using hd8) (by norm_num)
      rw [this]; push_cast; ring
    · rw [hwk s 1 hs' (by omega), if_pos hs, if_pos (by omega), kappa_T4_1 h2]
    · exact hu1 _ (by omega) (mod_div_node s 1 hs').2
    · simpa using hv _ 1 (-7) 1 (-7) (by omega) (mod_div_node s 1 hs').2
        (vL_T4_1 n α A s hα hA (by omega) hαA hs hs' (by omega)) (by simp) (by norm_num)

end CatalanCore.Lai.NV7

end

section
/-!
# The seven rational identities of Theorem NV7 (ledger LN07)

`det M₀ = 1095/2`, `D = 3117/8`, `C = -1117/2`, `G₂ = 1799/2`, `G₄ = 224` and the Schur constant
`G₄ - (G₂ - C²/D) = 779689/6234`, all in `ZMod ℓ` (`ℓ` odd).  `H₁ = -1/49`, `H₂ = -1` are in
`Dual5` (`tau_zero_deg_l`, `tau_k2`).
-/

open Matrix Finset CatalanCore.Lai

namespace CatalanCore.Lai.NV7

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- `h_m = 4 Mb(m,1,-2,-6) + Mb(m,2,-9/4,-105/8)`. -/
def hh (ℓ : ℕ) [Fact ℓ.Prime] (m : ℕ) : ZMod ℓ :=
  4 * Mb m 1 (-2) (-6) 1 + 1 * Mb m 2 (-9 / 4) (-105 / 8) 1

def Dc (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ := -32 * Mb 0 1 (-2) (-3) 1 + -27 * Mb 0 2 (-9 / 4) (-87 / 8) 1
def Cc (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ := -32 * Mb 1 1 (-2) (-3) 1 + -27 * Mb 1 2 (-9 / 4) (-87 / 8) 1
def G2c (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ := -32 * Mb 2 1 (-2) (-3) 1 + -27 * Mb 2 2 (-9 / 4) (-87 / 8) 1
def G4c (ℓ : ℕ) [Fact ℓ.Prime] : ZMod ℓ := -32 * Mb 0 1 (-2) (-7) 1

theorem ne48 (h2 : (2 : ZMod ℓ) ≠ 0) : (4 : ZMod ℓ) ≠ 0 ∧ (8 : ZMod ℓ) ≠ 0 := by
  constructor
  · have : (4 : ZMod ℓ) = 2 ^ 2 := by norm_num
    rw [this]; exact pow_ne_zero _ h2
  · have : (8 : ZMod ℓ) = 2 ^ 3 := by norm_num
    rw [this]; exact pow_ne_zero _ h2

section
variable (h2 : (2 : ZMod ℓ) ≠ 0)

include h2 in
theorem detH : (Matrix.of fun i i' : Fin 3 => hh ℓ ((i : ℕ) + i')).det = 1095 / 2 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  rw [det_fin_three]
  simp only [Matrix.of_apply, hh, Mb]
  simp
  field_simp
  ring

include h2 in
theorem Dc_val : Dc ℓ = 3117 / 8 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  simp only [Dc, Mb]; simp; field_simp; ring

include h2 in
theorem Cc_val : Cc ℓ = -1117 / 2 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  simp only [Cc, Mb]; simp; field_simp; ring

include h2 in
theorem G2c_val : G2c ℓ = 1799 / 2 := by
  obtain ⟨h4, h8⟩ := ne48 h2
  simp only [G2c, Mb]; simp; field_simp; ring

theorem G4c_val : G4c ℓ = 224 := by
  simp only [G4c, Mb]; simp; ring

include h2 in
theorem schur_val (h3 : (3 : ZMod ℓ) ≠ 0) (h1039 : (1039 : ZMod ℓ) ≠ 0) :
    G4c ℓ - (G2c ℓ - Cc ℓ ^ 2 / Dc ℓ) = 779689 / 6234 := by
  have h3117 : (3117 : ZMod ℓ) ≠ 0 := by
    have : (3117 : ZMod ℓ) = 3 * 1039 := by norm_num
    rw [this]; exact mul_ne_zero h3 h1039
  have h6234 : (6234 : ZMod ℓ) ≠ 0 := by
    have : (6234 : ZMod ℓ) = 2 * 3 * 1039 := by norm_num
    rw [this]; exact mul_ne_zero (mul_ne_zero h2 h3) h1039
  obtain ⟨h4, h8⟩ := ne48 h2
  rw [G4c_val, G2c_val h2, Cc_val h2, Dc_val h2]
  field_simp
  ring

end

end CatalanCore.Lai.NV7

end
