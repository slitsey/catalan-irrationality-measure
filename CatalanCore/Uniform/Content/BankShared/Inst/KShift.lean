import CatalanCore.Uniform.Content.BankShared.Check.Expr
set_option Elab.async false

/-! # The pole shifts of a k-shift frame and their master lattice (lane K; kshift-instance-2026-10-29)

A k-shift frame has, besides the multiples of `p`, the pole lattices `q_i t ≡ o_i (mod p)`
(`Δ_t = Σ_i w_i q_i / (q_i t - u_i)`, `Σ w_i = 0`; P6: shifts `(3, 2)`, `(2, 1)`).  At a prime `p` the pole index
of shift `i` is the `k_i` with `q_i k_i = j_i p + o_i`, `0 < j_i < q_i`.

**Master lattice.**  Fix `Q` with `q_i ∣ Q` and a master offset `oM` (the member `a = Q - oM` of the two-term
checker), and a multiplier `s_i` with `s_i oM ≡ o_i (mod q_i)`.  If `Q k = j p + oM` then

  `k_i = t_i k - (b_i p + c_i)`,  `t_i = (Q / q_i) s_i`,  `b_i = ⌊s_i j / q_i⌋`,  `c_i = (s_i oM - o_i) / q_i`,

with `q_i k_i = (s_i j mod q_i) p + o_i` (`Shift.kOf_spec`).  So every pole index of every shift is an integer
affine function of `p` and the ONE master pole index `k`, in each master root class `j`: a k-shift catalogue
compiles, class by class, into the one-lattice expressions of `Check.Expr` (`KTerm.Expr`). -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm

/-- A pole shift `o / q` with its multiplier `s` against the master offset. -/
structure Shift where
  q : ℕ
  o : ℕ
  s : ℕ

namespace Shift

/-- `t = (Q / q) s`. -/
def t (Q : ℕ) (x : Shift) : ℕ := Q / x.q * x.s
/-- `c = (s oM - o) / q`. -/
def c (oM : ℕ) (x : Shift) : ℕ := (x.s * oM - x.o) / x.q
/-- `b = ⌊s j / q⌋`. -/
def b (j : ℕ) (x : Shift) : ℕ := x.s * j / x.q
/-- The root class of the shift: `s j mod q`. -/
def jj (j : ℕ) (x : Shift) : ℕ := x.s * j % x.q
/-- The pole index at the master root `k`. -/
def kOf (Q oM j k p : ℕ) (x : Shift) : ℕ := x.t Q * k - (x.b j * p + x.c oM)

/-- **Root transport**: `Q k = j p + oM` gives `q (t k - (b p + c)) = (s j mod q) p + o`, without truncation. -/
theorem kOf_spec {Q oM j k p : ℕ} {x : Shift} (hx : 0 < x.q) (hQ : Q % x.q = 0)
    (ho : x.o ≤ x.s * oM) (hc : (x.s * oM - x.o) % x.q = 0) (hk : Q * k = j * p + oM) :
    x.b j * p + x.c oM ≤ x.t Q * k ∧ x.q * x.kOf Q oM j k p = x.jj j * p + x.o := by
  show x.b j * p + x.c oM ≤ Q / x.q * x.s * k ∧
    x.q * (Q / x.q * x.s * k - (x.b j * p + x.c oM)) = x.jj j * p + x.o
  have e1 : x.q * (Q / x.q) = Q := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hQ)
  have e2 : x.q * x.c oM = x.s * oM - x.o := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc)
  have e3 : x.q * x.b j + x.jj j = x.s * j := Nat.div_add_mod (x.s * j) x.q
  obtain ⟨d, hd⟩ : ∃ d, Q / x.q = d := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, x.c oM = C := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, x.b j = B := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J, x.jj j = J := ⟨_, rfl⟩
  rw [hd] at e1 ⊢
  rw [hC] at e2 ⊢
  rw [hB] at e3 ⊢
  rw [hJ] at e3 ⊢
  have e1z : (x.q : ℤ) * d = Q := by exact_mod_cast e1
  have e2z : (x.q : ℤ) * C = x.s * oM - x.o := by
    have h : ((x.q * C : ℕ) : ℤ) = ((x.s * oM - x.o : ℕ) : ℤ) := by rw [e2]
    rw [Nat.cast_sub ho] at h
    push_cast at h
    exact h
  have e3z : (x.q : ℤ) * B + J = x.s * j := by exact_mod_cast e3
  have hkz : (Q : ℤ) * k = j * p + oM := by exact_mod_cast hk
  have key : (x.q : ℤ) * (d * x.s * k) = x.q * (B * p + C) + (J * p + x.o) := by
    linear_combination (x.s * k : ℤ) * e1z + (x.s : ℤ) * hkz - e2z - (p : ℤ) * e3z
  have hle : B * p + C ≤ d * x.s * k := by
    have h1 : (x.q : ℤ) * (B * p + C) ≤ x.q * (d * x.s * k) := by
      rw [key]
      have : (0 : ℤ) ≤ J * p + x.o := by positivity
      linarith
    have h2 : x.q * (B * p + C) ≤ x.q * (d * x.s * k) := by exact_mod_cast h1
    exact Nat.le_of_mul_le_mul_left h2 hx
  refine ⟨hle, ?_⟩
  have h : ((x.q * (d * x.s * k - (B * p + C)) : ℕ) : ℤ) = ((J * p + x.o : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hle]
    linear_combination key
  exact_mod_cast h

end Shift

/-- The `i`-th shift of a list (`⟨1, 0, 0⟩`, i.e. `t = b = c = 0`, beyond its length). -/
def shAt : List Shift → ℕ → Shift
  | [], _ => ⟨1, 0, 0⟩
  | x :: _, 0 => x
  | _ :: l, i + 1 => shAt l i

theorem shAt_mem : ∀ (l : List Shift) (i : ℕ), i < l.length → shAt l i ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | x :: _, 0, _ => List.mem_cons_self
  | _ :: l, i + 1, h => List.mem_cons_of_mem _ (shAt_mem l i (by simp at h; omega))

theorem shAt_out : ∀ (l : List Shift) (i : ℕ), l.length ≤ i → shAt l i = ⟨1, 0, 0⟩
  | [], _, _ => rfl
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: l, i + 1, h => shAt_out l i (by simp at h; omega)

/-- Beyond the list the transported index is `0` with no truncation. -/
theorem kOf_out (Q oM j k p : ℕ) :
    (⟨1, 0, 0⟩ : Shift).b j * p + (⟨1, 0, 0⟩ : Shift).c oM ≤ (⟨1, 0, 0⟩ : Shift).t Q * k := by
  simp [Shift.t, Shift.b, Shift.c]

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.Shift.kOf_spec
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.shAt_mem
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.shAt_out
