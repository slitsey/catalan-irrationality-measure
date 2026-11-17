module

public import CatalanCore.Lai.ContentL2
public import CatalanCore.Lai.ContentL12
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `CatalanCore.Lai.ContentLemmaR`: Lemma R (unit part of the leading W-sum) modulo `p²`

Content note `N9-LAI-CONTENT-EXACT-2026-11-16`, Lemma R.  For `√(8n) < p < 3n` let `W` be a tie class
(`σ(s) = σ_W`, `λ - σ_W` even).  Put `μ'_r = μ_r + [r ∉ W]`,
`f(s) = ĉ_s ∏_{r ≠ s} (s - r)^{2 μ'_r}` (`ĉ_s = Cs`, the low-digit factorial ratio of Lemma G), and
`Q̂(s) = ∏_r (s - r)^{m_r} = Q(s)³ Z(s)²` (`m_r = 3, 2, 0` on `N, Z, W`).

* `lemmaR_p2` (the main theorem): there is a unit `K` of `ℤ/p²`, independent of `s`, with
  `f(s) = K · Q̂(s) · (1 + p Ξ(s))` for all `s ∈ W`, where
  `Ξ(s) = (λ-1) H_s - 2 b H_{r₆+p-s} + 3 (1-ε) H_{r₂+s}` (`b, ε` the carry flags of `W`).
  The three harmonic digit functions have total weight `λ - 1 - 2 b + 3 (1-ε) = 2 μ_W - 2`
  (`xiR_weight`) and their arguments lie in `[0, p)` on `W` (`xiR_args`).
  There are no extra rational terms `n_β/(s-β)` (the paper's `n_β` vanish).
* `lemmaR_p`: the reduction modulo `p`, `f(s) ≡ K Q̂(s)`.
* Proof (no reflection, no divisor bookkeeping): the exact identity `fR_E1`
  `f · PB² PC³ = Cs · Q̂ · PA^(λ+4)` (from Lemma S: `g_r + σ_r = m_r + λ + 4`), closed forms and ratios of
  the tail products `Jt` (`PA, PB, PC`), the low-digit step `Cs_step`, and one induction step along the
  interval `W` (`fR_step`): `F(t+1) = F(t) · (1 + p d)`, `Ξ(t+1) - Ξ(t) = d`, using `p - a = -a (1 - p/a)`.
* `QhatPoly`, `QhatPoly_eval`, `QhatPoly_monic`, `QhatPoly_natDegree`: `Q̂` as a monic polynomial.
-/

open Finset CatalanCore.Content

namespace CatalanCore.Lai

section TailProducts

/-- `∏_{a ≤ r < p, r ≠ s} (s - r)` in `ℤ/p²` (the tail products `PA, PB, PC` of Lemma R). -/
def Jt (p a s : ℕ) : ZMod (p ^ 2) :=
  ∏ r ∈ Ico a p, if r = s then 1 else ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2)))

lemma nat_prod_sub (d : ℕ) : ∏ k ∈ range d, (d - k) = d.factorial := by
  rw [← Finset.prod_range_add_one_eq_factorial, ← Finset.prod_range_reflect (fun j => j + 1) d]
  refine Finset.prod_congr rfl (fun k hk => ?_)
  have := Finset.mem_range.1 hk
  omega

lemma nat_fact_mul_prod (j m : ℕ) :
    j.factorial * ∏ k ∈ range m, (j + 1 + k) = (j + m).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, show j + (m + 1) = (j + m) + 1 by ring,
      Nat.factorial_succ]
    ring

lemma prod_Ico_below (n a d : ℕ) :
    (∏ r ∈ Ico a (a + d), if r = a + d then (1 : ZMod (n ^ 2)) else (((a + d : ℕ) : ZMod (n ^ 2)) - (r : ZMod (n ^ 2))))
      = (d.factorial : ZMod (n ^ 2)) := by
  have h1 : ∀ r ∈ Ico a (a + d),
      (if r = a + d then (1 : ZMod (n ^ 2)) else (((a + d : ℕ) : ZMod (n ^ 2)) - (r : ZMod (n ^ 2)))) =
      (((a + d : ℕ) : ZMod (n ^ 2)) - (r : ZMod (n ^ 2))) := by
    intro r hr
    have := Finset.mem_Ico.1 hr
    rw [if_neg (by omega)]
  rw [Finset.prod_congr rfl h1, Finset.prod_Ico_eq_prod_range]
  have h2 : ∀ k ∈ range (a + d - a), (((a + d : ℕ) : ZMod (n ^ 2)) - ((a + k : ℕ) : ZMod (n ^ 2))) =
      (((d - k : ℕ) : ℕ) : ZMod (n ^ 2)) := by
    intro k hk
    have := Finset.mem_range.1 hk
    have e : a + d - a = d := by omega
    rw [e] at this
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Finset.prod_congr rfl h2, ← Nat.cast_prod, Nat.add_sub_cancel_left, nat_prod_sub]

lemma prod_Ico_above (n s e : ℕ) :
    (∏ r ∈ Ico (s + 1) (s + 1 + e), if r = s then (1 : ZMod (n ^ 2)) else ((s : ZMod (n ^ 2)) - (r : ZMod (n ^ 2))))
      = (-1) ^ e * (e.factorial : ZMod (n ^ 2)) := by
  have h1 : ∀ r ∈ Ico (s + 1) (s + 1 + e),
      (if r = s then (1 : ZMod (n ^ 2)) else ((s : ZMod (n ^ 2)) - (r : ZMod (n ^ 2)))) =
      ((s : ZMod (n ^ 2)) - (r : ZMod (n ^ 2))) := by
    intro r hr
    have := Finset.mem_Ico.1 hr
    rw [if_neg (by omega)]
  rw [Finset.prod_congr rfl h1, Finset.prod_Ico_eq_prod_range]
  have h2 : ∀ k ∈ range (s + 1 + e - (s + 1)), ((s : ZMod (n ^ 2)) - ((s + 1 + k : ℕ) : ZMod (n ^ 2))) =
      (-1) * (((k + 1 : ℕ)) : ZMod (n ^ 2)) := by
    intro k _
    push_cast
    ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Nat.add_sub_cancel_left, ← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]

/-- `s = a + d ≥ a`: `Jt = (-1)^e d! e!` where `e = p - 1 - s`. -/
theorem Jt_ge (p a d e : ℕ) (hp : p = a + d + 1 + e) :
    Jt p a (a + d) = (-1) ^ e * (d.factorial : ZMod (p ^ 2)) * (e.factorial : ZMod (p ^ 2)) := by
  subst hp
  unfold Jt
  rw [← Finset.prod_Ico_consecutive _ (show a ≤ a + d by omega) (show a + d ≤ a + d + 1 + e by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show a + d < a + d + 1 + e by omega)]
  have hb : a + d + 1 + e - (a + d + 1) = e := by omega
  rw [prod_Ico_below, if_pos rfl, one_mul]
  have := prod_Ico_above (n := a + d + 1 + e) (a + d) e
  rw [this]
  ring

/-- `s = a - 1 - j < a`, `p = a + m`: `Jt (j)! = (-1)^m (j + m)!`. -/
theorem Jt_lt (p s j m : ℕ) (hp : p = s + 1 + j + m) :
    Jt p (s + 1 + j) s * (j.factorial : ZMod (p ^ 2)) = (-1) ^ m * ((j + m).factorial : ZMod (p ^ 2)) := by
  subst hp
  unfold Jt
  have h1 : ∀ r ∈ Ico (s + 1 + j) (s + 1 + j + m),
      (if r = s then (1 : ZMod ((s + 1 + j + m) ^ 2)) else ((s : ZMod ((s + 1 + j + m) ^ 2)) - (r : ZMod ((s + 1 + j + m) ^ 2)))) =
      ((s : ZMod ((s + 1 + j + m) ^ 2)) - (r : ZMod ((s + 1 + j + m) ^ 2))) := by
    intro r hr
    have := Finset.mem_Ico.1 hr
    rw [if_neg (by omega)]
  rw [Finset.prod_congr rfl h1, Finset.prod_Ico_eq_prod_range]
  have h2 : ∀ k ∈ range (s + 1 + j + m - (s + 1 + j)),
      ((s : ZMod ((s + 1 + j + m) ^ 2)) - ((s + 1 + j + k : ℕ) : ZMod ((s + 1 + j + m) ^ 2))) =
      (-1) * (((j + 1 + k : ℕ)) : ZMod ((s + 1 + j + m) ^ 2)) := by
    intro k _
    push_cast
    ring
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    Nat.add_sub_cancel_left, mul_assoc, ← Nat.cast_prod, ← Nat.cast_mul,
    Nat.mul_comm (∏ i ∈ range m, (j + 1 + i)) j.factorial, nat_fact_mul_prod]

end TailProducts

section Jet

variable {p : ℕ} [hp : Fact p.Prime]

/-- First-order unit `1 + p x` in `ℤ/p²`. -/
def jetp (p : ℕ) (x : ZMod (p ^ 2)) : ZMod (p ^ 2) := 1 + (p : ZMod (p ^ 2)) * x

lemma jetp_mul (x y : ZMod (p ^ 2)) : jetp p x * jetp p y = jetp p (x + y) := by
  unfold jetp
  have hs := pp_sq (p := p)
  linear_combination (x * y) * hs

lemma jetp_zero : jetp p (0 : ZMod (p ^ 2)) = 1 := by unfold jetp; ring

lemma jetp_pow (x : ZMod (p ^ 2)) (k : ℕ) : jetp p x ^ k = jetp p ((k : ZMod (p ^ 2)) * x) := by
  induction k with
  | zero => simp [jetp_zero]
  | succ k ih =>
    rw [pow_succ (jetp p x) k, ih, jetp_mul]
    congr 1
    push_cast
    ring

lemma jetp_neg_mul (x : ZMod (p ^ 2)) : jetp p x * jetp p (-x) = 1 := by
  rw [jetp_mul, add_neg_cancel, jetp_zero]

lemma isUnit_jetp (x : ZMod (p ^ 2)) : IsUnit (jetp p x) :=
  isUnit_one_add_p (p := p) x

/-- `p - a = -a (1 - p w)` when `a w = 1` (`p² = 0`). -/
lemma p_sub_eq {a w : ZMod (p ^ 2)} (h : a * w = 1) :
    (p : ZMod (p ^ 2)) - a = -a * jetp p (-w) := by
  unfold jetp
  linear_combination (-(p : ZMod (p ^ 2))) * h

lemma isUnit_natCast_p2 {m : ℕ} (h1 : 1 ≤ m) (h2 : m < p) : IsUnit ((m : ℕ) : ZMod (p ^ 2)) :=
  isUnit_cast_p2 (p := p) h1 h2

lemma natInv_mul {m : ℕ} (h1 : 1 ≤ m) (h2 : m < p) :
    ((m : ℕ) : ZMod (p ^ 2)) * ((m : ℕ) : ZMod (p ^ 2))⁻¹ = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_natCast_p2 h1 h2)

end Jet

section Ratios

variable {p : ℕ} [hp : Fact p.Prime]

/-- Ratio for the tail product at `s = a + d ≥ a`. -/
theorem Jt_succ_ge (a d e : ℕ) (hpe : p = a + d + 2 + e) :
    Jt p a (a + d + 1) * ((e + 1 : ℕ) : ZMod (p ^ 2)) =
      -((d + 1 : ℕ) : ZMod (p ^ 2)) * Jt p a (a + d) := by
  have h1 := Jt_ge p a (d + 1) e (by omega)
  have h2 := Jt_ge p a d (e + 1) (by omega)
  rw [show a + d + 1 = a + (d + 1) by ring, h1, h2]
  push_cast [Nat.factorial_succ]
  ring

/-- Ratio for the tail product at `s + 1 < a`. -/
theorem Jt_succ_lt (s j m : ℕ) (hpe : p = s + 2 + j + m) :
    Jt p (s + 2 + j) s * ((j + 1 : ℕ) : ZMod (p ^ 2)) =
      Jt p (s + 2 + j) (s + 1) * ((j + 1 + m : ℕ) : ZMod (p ^ 2)) := by
  have h1 := Jt_lt p s (j + 1) m (by omega)
  have h2 := Jt_lt p (s + 1) j m (by omega)
  rw [show s + 1 + (j + 1) = s + 2 + j by ring] at h1
  rw [show s + 1 + 1 + j = s + 2 + j by ring] at h2
  have hu : IsUnit ((j.factorial : ℕ) : ZMod (p ^ 2)) := isUnit_fact_p2 (p := p) j (by omega)
  apply hu.mul_right_cancel
  rw [show j + 1 + m = (j + m) + 1 by ring, Nat.factorial_succ] at h1
  rw [Nat.factorial_succ] at h1
  push_cast at h1 h2 ⊢
  linear_combination h1 - ((j : ZMod (p ^ 2)) + m + 1) * h2

end Ratios

section CsStep

variable {p : ℕ} [hp : Fact p.Prime]

lemma Bwi_succ (m : ℕ) (hm : m + 1 < p) :
    ((m + 1 : ℕ) : ZMod (p ^ 2)) * Bwi p (m + 1) = Bwi p m := by
  have h1 := Bw_mul_Bwi (p := p) (m + 1) hm
  have h2 := Bw_mul_Bwi (p := p) m (by omega)
  have h3 : Bw p (m + 1) = ((m + 1 : ℕ) : ZMod (p ^ 2)) * Bw p m := by
    unfold Bw; rw [Nat.factorial_succ]; push_cast; ring
  rw [h3] at h1
  linear_combination (Bwi p m) * h1 - ((m + 1 : ℕ) : ZMod (p ^ 2)) * Bwi p (m + 1) * h2

lemma Bw_succ (m : ℕ) : Bw p (m + 1) = ((m + 1 : ℕ) : ZMod (p ^ 2)) * Bw p m := by
  unfold Bw; rw [Nat.factorial_succ]; push_cast; ring

end CsStep

section CsStep2

variable {p : ℕ} [hp : Fact p.Prime]

/-- One step of the low-digit factor `Cs` inside a class. -/
theorem Cs_step (r6 r2 t B C b ε : ℕ) (ht : t + 1 < p)
    (hB : r6 + b * p = t + 1 + B) (hB1 : B + 1 < p)
    (hC : r2 + t + 1 = ε * p + C + 1) :
    Cs p r6 r2 b ε (t + 1) * ((t + 1 : ℕ) : ZMod (p ^ 2)) ^ 5 =
      Cs p r6 r2 b ε t * ((B + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 * ((C + 1 : ℕ) : ZMod (p ^ 2)) ^ 3 := by
  unfold Cs
  have e1 : r6 + b * p - (t + 1) = B := by omega
  have e2 : r6 + b * p - t = B + 1 := by omega
  have e3 : r2 + (t + 1) - ε * p = C + 1 := by omega
  have e4 : r2 + t - ε * p = C := by omega
  rw [e1, e2, e3, e4]
  have hu := Bwi_succ (p := p) t ht
  have hb := Bwi_succ (p := p) B hB1
  have hc := Bw_succ (p := p) C
  calc (Bw p r6 * Bwi p (t + 1) * Bwi p B) ^ 2 * (Bw p (C + 1) * Bwi p (t + 1) * Bwi p r2) ^ 3 *
        ((t + 1 : ℕ) : ZMod (p ^ 2)) ^ 5
      = (Bw p r6 * (((t + 1 : ℕ) : ZMod (p ^ 2)) * Bwi p (t + 1)) * Bwi p B) ^ 2 *
        (Bw p (C + 1) * (((t + 1 : ℕ) : ZMod (p ^ 2)) * Bwi p (t + 1)) * Bwi p r2) ^ 3 := by ring
    _ = (Bw p r6 * Bwi p t * (((B + 1 : ℕ) : ZMod (p ^ 2)) * Bwi p (B + 1))) ^ 2 *
        ((((C + 1 : ℕ) : ZMod (p ^ 2)) * Bw p C) * Bwi p t * Bwi p r2) ^ 3 := by
      rw [hu, ← hb, hc]
    _ = _ := by ring

lemma isUnit_Bw (m : ℕ) (hm : m < p) : IsUnit (Bw p m) := isUnit_fact_p2 (p := p) m hm

lemma isUnit_Bwi (m : ℕ) (hm : m < p) : IsUnit (Bwi p m) :=
  IsUnit.of_mul_eq_one (Bw p m) (by rw [mul_comm]; exact Bw_mul_Bwi (p := p) m hm)

lemma isUnit_Cs (r6 r2 b ε s : ℕ) (hr6 : r6 < p) (hr2 : r2 < p) (hs : s < p)
    (hB : r6 + b * p - s < p) (hC : r2 + s - ε * p < p) :
    IsUnit (Cs p r6 r2 b ε s) := by
  unfold Cs
  exact (((isUnit_Bw r6 hr6).mul (isUnit_Bwi s hs)).mul (isUnit_Bwi _ hB)).pow 2 |>.mul
    ((((isUnit_Bw _ hC).mul (isUnit_Bwi s hs)).mul (isUnit_Bwi r2 hr2)).pow 3)

end CsStep2

section PeDef

variable {p : ℕ}

/-- `∏_{r<p, r≠s} (s - r)^{e r}` in `ℤ/p²`. -/
def Pe (p : ℕ) (e : ℕ → ℕ) (s : ℕ) : ZMod (p ^ 2) :=
  ∏ r ∈ range p, if r = s then 1 else ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ e r

lemma Pe_congr (e1 e2 : ℕ → ℕ) (s : ℕ) (h : ∀ r < p, e1 r = e2 r) :
    Pe p e1 s = Pe p e2 s := by
  unfold Pe
  refine Finset.prod_congr rfl (fun r hr => ?_)
  rw [h r (Finset.mem_range.1 hr)]

lemma Pe_add (e1 e2 : ℕ → ℕ) (s : ℕ) :
    Pe p (fun r => e1 r + e2 r) s = Pe p e1 s * Pe p e2 s := by
  unfold Pe
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  split_ifs <;> simp [pow_add]

lemma Pe_smul (k : ℕ) (e : ℕ → ℕ) (s : ℕ) :
    Pe p (fun r => k * e r) s = Pe p e s ^ k := by
  unfold Pe
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  split_ifs
  · simp
  · rw [← pow_mul, mul_comm]

lemma Pe_ind (a s : ℕ) : Pe p (fun r => if a ≤ r then 1 else 0) s = Jt p a s := by
  unfold Pe Jt
  have h1 : ∀ r ∈ range p,
      (if r = s then (1 : ZMod (p ^ 2)) else ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ (if a ≤ r then 1 else 0)) =
      if a ≤ r then (if r = s then 1 else ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2)))) else 1 := by
    intro r _
    split_ifs <;> simp
  rw [Finset.prod_congr rfl h1, ← Finset.prod_filter]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

lemma Pe_const (k s : ℕ) : Pe p (fun _ => k) s = Jt p 0 s ^ k := by
  rw [← Pe_ind, ← Pe_smul]
  exact Pe_congr _ _ s (fun r _ => by simp)

end PeDef

section ClassData

variable {n p : ℕ} [hp : Fact p.Prime]

/-- exponent of the factor `(s - r)` in `f(s)`: `2 μ'_r = 2 μ_r + 2 [r ∉ W]`. -/
noncomputable def gexp (n p σW r : ℕ) : ℕ := 2 * mu n p r + (if sig n p r = σW then 0 else 2)

/-- multiplicity of the root `r` in `Q̂ = Q³ Z²`: `3` on `N`, `2` on `Z`, `0` on `W`. -/
noncomputable def mexp (n p σW r : ℕ) : ℕ :=
  (if sig n p r = σW then 0 else 2) + (if (lam n p - (sig n p r : ℤ)) % 2 ≠ 0 then 1 else 0)

/-- `f(s) = ĉ_s ∏_{r≠s} (s-r)^{2μ'_r}` of Lemma R, in `ℤ/p²`. -/
noncomputable def fR (n p σW s : ℕ) : ZMod (p ^ 2) :=
  Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * Pe p (gexp n p σW) s

/-- `Q̂(s) = ∏_r (s - r)^{m_r} = Q(s)³ Z(s)²`, in `ℤ/p²`. -/
noncomputable def Qhat (n p σW s : ℕ) : ZMod (p ^ 2) :=
  ∏ r ∈ range p, ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ mexp n p σW r

lemma sig_decomp (n p r : ℕ) :
    sig n p r = 2 * (if r6 n p + 1 ≤ r then 1 else 0) + 3 * (if p - r2 n p ≤ r then 1 else 0) := by
  unfold sig
  split_ifs <;> omega

lemma gexp_add (h : Rng n p) (σW r : ℕ) (hr : r < p) :
    gexp n p σW r + sig n p r = mexp n p σW r + ((lam n p).toNat + 4) := by
  have h3 := (lemmaS h).2.2.1 r hr
  have h0 := (lemmaS h).1
  unfold gexp mexp
  split_ifs at h3 ⊢ <;> omega

/-- **(E1)**: `f(s) PB(s)² PC(s)³ = Cs(s) Q̂(s) PA(s)^{λ+4}`. -/
theorem fR_E1 (h : Rng n p) (σW s : ℕ) (hms : mexp n p σW s = 0) :
    fR n p σW s * (Jt p (r6 n p + 1) s ^ 2 * Jt p (p - r2 n p) s ^ 3) =
      Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * Qhat n p σW s *
        Jt p 0 s ^ ((lam n p).toNat + 4) := by
  have hmain : Pe p (gexp n p σW) s * (Jt p (r6 n p + 1) s ^ 2 * Jt p (p - r2 n p) s ^ 3) =
      Qhat n p σW s * Jt p 0 s ^ ((lam n p).toNat + 4) := by
    have hq : Qhat n p σW s = Pe p (mexp n p σW) s := by
      unfold Qhat Pe
      refine Finset.prod_congr rfl (fun r _ => ?_)
      by_cases hr : r = s
      · subst hr; rw [hms]; simp
      · simp [hr]
    rw [hq, ← Pe_ind (r6 n p + 1) s, ← Pe_ind (p - r2 n p) s, ← Pe_ind 0 s, ← Pe_smul 2,
      ← Pe_smul 3, ← Pe_smul ((lam n p).toNat + 4), ← Pe_add, ← Pe_add, ← Pe_add]
    refine Pe_congr _ _ s (fun r hr => ?_)
    have h1 := gexp_add h σW r hr
    have h2 := sig_decomp n p r
    split_ifs at * <;> omega
  unfold fR
  calc _ = Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s *
        (Pe p (gexp n p σW) s * (Jt p (r6 n p + 1) s ^ 2 * Jt p (p - r2 n p) s ^ 3)) := by ring
    _ = _ := by rw [hmain]; ring

end ClassData

section Units

variable {p : ℕ} [hp : Fact p.Prime]

lemma isUnit_sub_cast (s r : ℕ) (hs : s < p) (hr : r < p) (hne : r ≠ s) :
    IsUnit ((s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) := by
  rcases lt_or_gt_of_ne hne.symm with h | h
  · have e : (s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2)) = -(((r - s : ℕ)) : ZMod (p ^ 2)) := by
      rw [Nat.cast_sub h.le]; ring
    rw [e]
    exact (isUnit_natCast_p2 (m := r - s) (by omega) (by omega)).neg
  · have e : (s : ZMod (p ^ 2)) - (r : ZMod (p ^ 2)) = (((s - r : ℕ)) : ZMod (p ^ 2)) := by
      rw [Nat.cast_sub h.le]
    rw [e]
    exact isUnit_natCast_p2 (m := s - r) (by omega) (by omega)

lemma isUnit_Jt (a s : ℕ) (hs : s < p) : IsUnit (Jt p a s) := by
  unfold Jt
  refine IsUnit.prod_iff.2 (fun r hr => ?_)
  have := (Finset.mem_Ico.1 hr).2
  by_cases h : r = s
  · simp [h]
  · rw [if_neg h]; exact isUnit_sub_cast s r hs this h

lemma isUnit_Pe (e : ℕ → ℕ) (s : ℕ) (hs : s < p) : IsUnit (Pe p e s) := by
  unfold Pe
  refine IsUnit.prod_iff.2 (fun r hr => ?_)
  have := Finset.mem_range.1 hr
  by_cases h : r = s
  · simp [h]
  · rw [if_neg h]; exact (isUnit_sub_cast s r hs this h).pow _

lemma isUnit_Qhat {n : ℕ} (σW s : ℕ) (hs : s < p) (hms : mexp n p σW s = 0) :
    IsUnit (Qhat n p σW s) := by
  unfold Qhat
  refine IsUnit.prod_iff.2 (fun r hr => ?_)
  have := Finset.mem_range.1 hr
  by_cases h : r = s
  · subst h; rw [hms]; simp
  · exact (isUnit_sub_cast s r hs this h).pow _

end Units

section Sides

variable {p : ℕ} [hp : Fact p.Prime]

lemma Jt_succ_ge' (a d e s : ℕ) (hpe : p = a + d + 2 + e) (hs : s = a + d) :
    Jt p a (s + 1) * ((e + 1 : ℕ) : ZMod (p ^ 2)) =
      -((d + 1 : ℕ) : ZMod (p ^ 2)) * Jt p a s := by
  subst hs; exact Jt_succ_ge a d e hpe

lemma Jt_succ_lt' (a s j m : ℕ) (ha : a = s + 2 + j) (hpe : p = s + 2 + j + m) :
    Jt p a s * ((j + 1 : ℕ) : ZMod (p ^ 2)) =
      Jt p a (s + 1) * ((j + 1 + m : ℕ) : ZMod (p ^ 2)) := by
  subst ha; exact Jt_succ_lt s j m hpe

/-- the `PA` step: `Jt p 0 (t+1) = Jt p 0 t * jetp (1/(t+1))`. -/
lemma PA_step (t : ℕ) (ht : t + 1 < p) :
    Jt p 0 (t + 1) = Jt p 0 t * jetp p (((t + 1 : ℕ) : ZMod (p ^ 2))⁻¹) := by
  obtain ⟨e, he⟩ : ∃ e, p = 0 + t + 2 + e := ⟨p - t - 2, by omega⟩
  have h := Jt_succ_ge' 0 t e t he (by omega)
  have hu := natInv_mul (p := p) (m := t + 1) (by omega) ht
  set u : ZMod (p ^ 2) := ((t + 1 : ℕ) : ZMod (p ^ 2)) with hu_def
  set w : ZMod (p ^ 2) := u⁻¹ with hw_def
  have hv : ((e + 1 : ℕ) : ZMod (p ^ 2)) = -u * jetp p (-w) := by
    rw [← p_sub_eq hu]
    have : e + 1 + (t + 1) = p := by omega
    have h2 := congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) this
    simp only [Nat.cast_add, Nat.cast_one] at h2 ⊢
    rw [hu_def] at *
    push_cast at h2 ⊢
    linear_combination h2
  rw [hv] at h
  have huu : IsUnit u := isUnit_natCast_p2 (m := t + 1) (by omega) ht
  have h3 : Jt p 0 (t + 1) * jetp p (-w) = Jt p 0 t := by
    apply (huu.neg).mul_left_cancel
    linear_combination h
  have := jetp_neg_mul (p := p) w
  calc Jt p 0 (t + 1) = Jt p 0 (t + 1) * (jetp p (-w) * jetp p (-(-w))) := by
        rw [jetp_neg_mul]; ring
    _ = (Jt p 0 (t + 1) * jetp p (-w)) * jetp p (-(-w)) := by ring
    _ = _ := by rw [h3, neg_neg]

lemma PB_side0 (a s j m : ℕ) (ha : a = s + 2 + j) (hpe : p = s + 2 + j + m) :
    ((j + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 * Jt p a s ^ 2 =
      ((j + 1 + m : ℕ) : ZMod (p ^ 2)) ^ 2 * Jt p a (s + 1) ^ 2 := by
  have h := Jt_succ_lt' a s j m ha hpe
  calc _ = (Jt p a s * ((j + 1 : ℕ) : ZMod (p ^ 2))) ^ 2 := by ring
    _ = (Jt p a (s + 1) * ((j + 1 + m : ℕ) : ZMod (p ^ 2))) ^ 2 := by rw [h]
    _ = _ := by ring

lemma jetp_sq_cancel (w : ZMod (p ^ 2)) : jetp p (-w) ^ 2 * jetp p (2 * w) = 1 := by
  rw [pow_two (jetp p (-w)), jetp_mul, jetp_mul]
  have : -w + -w + 2 * w = 0 := by ring
  rw [this, jetp_zero]

lemma jetp_cube_cancel (w : ZMod (p ^ 2)) : jetp p (-w) ^ 3 * jetp p (3 * w) = 1 := by
  rw [jetp_pow (-w) 3, jetp_mul]
  have : ((3 : ℕ) : ZMod (p ^ 2)) * -w + 3 * w = 0 := by push_cast; ring
  rw [this, jetp_zero]

lemma PB_side1 (a d e s : ℕ) (hpe : p = a + d + 2 + e) (hs : s = a + d) (X w : ZMod (p ^ 2))
    (hX : X + ((d + 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2))) (hw : X * w = 1) :
    X ^ 2 * Jt p a s ^ 2 =
      ((e + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 * jetp p (2 * w) * Jt p a (s + 1) ^ 2 := by
  have h := Jt_succ_ge' a d e s hpe hs
  have hy : ((d + 1 : ℕ) : ZMod (p ^ 2)) = -X * jetp p (-w) := by
    rw [← p_sub_eq hw]; linear_combination hX
  rw [hy] at h
  have hj := jetp_sq_cancel (p := p) w
  calc X ^ 2 * Jt p a s ^ 2 = X ^ 2 * Jt p a s ^ 2 * (jetp p (-w) ^ 2 * jetp p (2 * w)) := by
        rw [hj]; ring
    _ = (Jt p a (s + 1) * ((e + 1 : ℕ) : ZMod (p ^ 2))) ^ 2 * jetp p (2 * w) := by
        rw [h]; ring
    _ = _ := by ring

lemma PC_side1 (a d e s : ℕ) (hpe : p = a + d + 2 + e) (hs : s = a + d) :
    ((d + 1 : ℕ) : ZMod (p ^ 2)) ^ 3 * Jt p a s ^ 3 =
      -(((e + 1 : ℕ) : ZMod (p ^ 2)) ^ 3) * Jt p a (s + 1) ^ 3 := by
  have h := Jt_succ_ge' a d e s hpe hs
  calc _ = (-(Jt p a (s + 1) * ((e + 1 : ℕ) : ZMod (p ^ 2)))) ^ 3 * (-1) ^ 3 * (-1) := by
        rw [h]; ring
    _ = _ := by ring

lemma PC_side0 (a s j m : ℕ) (ha : a = s + 2 + j) (hpe : p = s + 2 + j + m) (X w : ZMod (p ^ 2))
    (hX : X + ((j + 1 : ℕ) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2))) (hw : X * w = 1) :
    X ^ 3 * Jt p a s ^ 3 =
      -(((j + 1 + m : ℕ) : ZMod (p ^ 2)) ^ 3) * jetp p (3 * w) * Jt p a (s + 1) ^ 3 := by
  have h := Jt_succ_lt' a s j m ha hpe
  have hy : ((j + 1 : ℕ) : ZMod (p ^ 2)) = -X * jetp p (-w) := by
    rw [← p_sub_eq hw]; linear_combination hX
  rw [hy] at h
  have hj := jetp_cube_cancel (p := p) w
  -- h : PC(s) * (-X jetp(-w)) = PC(s+1) * v
  calc X ^ 3 * Jt p a s ^ 3
      = X ^ 3 * Jt p a s ^ 3 * (jetp p (-w) ^ 3 * jetp p (3 * w)) := by rw [hj]; ring
    _ = -((Jt p a s * (-X * jetp p (-w))) ^ 3) * jetp p (3 * w) := by ring
    _ = -((Jt p a (s + 1) * ((j + 1 + m : ℕ) : ZMod (p ^ 2))) ^ 3) * jetp p (3 * w) := by rw [h]
    _ = _ := by ring

end Sides

section Combine

variable {R : Type*} [CommRing R]

/-- Pure algebra of the local step. -/
lemma step_combine (Cs0 Cs1 PA0 PA1 PB0 PB1 PC0 PC1 u v xB xC jB jC Jw Jm : R) (N : ℕ)
    (hCs : Cs1 * u ^ 5 = Cs0 * xB ^ 2 * xC ^ 3)
    (hB : xB ^ 2 * PB0 ^ 2 = v ^ 2 * jB * PB1 ^ 2)
    (hC : xC ^ 3 * PC0 ^ 3 = -(v ^ 3) * jC * PC1 ^ 3)
    (hA : PA1 = PA0 * Jw) (hv : v = -u * Jm) :
    (Cs1 * PA1 ^ N * (PB0 ^ 2 * PC0 ^ 3)) * u ^ 5 =
      (Cs0 * PA0 ^ N * (PB1 ^ 2 * PC1 ^ 3) * (Jm ^ 5 * jB * jC * Jw ^ N)) * u ^ 5 := by
  calc (Cs1 * PA1 ^ N * (PB0 ^ 2 * PC0 ^ 3)) * u ^ 5
      = (Cs1 * u ^ 5) * PA1 ^ N * (PB0 ^ 2 * PC0 ^ 3) := by ring
    _ = (Cs0 * xB ^ 2 * xC ^ 3) * PA1 ^ N * (PB0 ^ 2 * PC0 ^ 3) := by rw [hCs]
    _ = Cs0 * (xB ^ 2 * PB0 ^ 2) * (xC ^ 3 * PC0 ^ 3) * PA1 ^ N := by ring
    _ = Cs0 * (v ^ 2 * jB * PB1 ^ 2) * (-(v ^ 3) * jC * PC1 ^ 3) * (PA0 * Jw) ^ N := by
        rw [hB, hC, hA]
    _ = (-(v ^ 5)) * Cs0 * PA0 ^ N * (PB1 ^ 2 * PC1 ^ 3) * (jB * jC * Jw ^ N) := by ring
    _ = _ := by rw [hv]; ring

end Combine

section Step

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The harmonic correction `Ξ(s)` of Lemma R:
`(λ-1) H_s - 2 b H_{r₆+p-s} + 3 (1-ε) H_{r₂+s}`. -/
noncomputable def xiR (n p s : ℕ) : ZMod (p ^ 2) :=
  (((lam n p - 1 : ℤ)) : ZMod (p ^ 2)) * Hz p s
    - 2 * (bflag n p s : ZMod (p ^ 2)) * Hz p (r6 n p + p - s)
    + 3 * (1 - (eflag n p s : ZMod (p ^ 2))) * Hz p (r2 n p + s)

lemma cast_toNat_lam (h : Rng n p) :
    (((lam n p).toNat : ℕ) : ZMod (p ^ 2)) = ((lam n p : ℤ) : ZMod (p ^ 2)) := by
  have h0 := (lemmaS h).1
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]

/-- **Local step of Lemma R.** -/
theorem fR_step (h : Rng n p) (σW t : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) (ht : t + 1 < p)
    (h0 : sig n p t = σW) (h1 : sig n p (t + 1) = σW) :
    fR n p σW (t + 1) * Qhat n p σW t * jetp p (xiR n p t) =
      fR n p σW t * Qhat n p σW (t + 1) * jetp p (xiR n p (t + 1)) := by
  have hp0 : 0 < p := hp.out.pos
  have hr6 : r6 n p < p := r6_lt n p hp0
  have hr2 : r2 n p < p := r2_lt n p hp0
  obtain ⟨hb1, he1, hbc, hec⟩ := flag_cases n p t hr2 ht (h0.trans h1.symm)
  -- the data B, C
  set b := bflag n p t with hb_def
  set ε := eflag n p t with hε_def
  obtain ⟨B, hB⟩ : ∃ B, r6 n p + b * p = t + 1 + B := ⟨r6 n p + b * p - (t + 1), by
    rcases hbc with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] <;> omega⟩
  have hB1 : B + 1 < p := by rcases hbc with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] at hB <;> omega
  obtain ⟨C, hC⟩ : ∃ C, r2 n p + t + 1 = ε * p + C + 1 := ⟨r2 n p + t - ε * p, by
    rcases hec with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] <;> omega⟩
  have hC1 : C + 1 < p := by rcases hec with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] at hC <;> omega
  -- units
  have huu : IsUnit (((t + 1 : ℕ)) : ZMod (p ^ 2)) := isUnit_natCast_p2 (by omega) ht
  have hxB : IsUnit (((B + 1 : ℕ)) : ZMod (p ^ 2)) := isUnit_natCast_p2 (by omega) hB1
  have hxC : IsUnit (((C + 1 : ℕ)) : ZMod (p ^ 2)) := isUnit_natCast_p2 (by omega) hC1
  have hu_inv := natInv_mul (p := p) (m := t + 1) (by omega) ht
  have hxB_inv := natInv_mul (p := p) (m := B + 1) (by omega) hB1
  have hxC_inv := natInv_mul (p := p) (m := C + 1) (by omega) hC1
  set u : ZMod (p ^ 2) := ((t + 1 : ℕ) : ZMod (p ^ 2)) with hu_def
  set wu : ZMod (p ^ 2) := u⁻¹ with hwu_def
  set wx : ZMod (p ^ 2) := ((B + 1 : ℕ) : ZMod (p ^ 2))⁻¹ with hwx_def
  set wc : ZMod (p ^ 2) := ((C + 1 : ℕ) : ZMod (p ^ 2))⁻¹ with hwc_def
  set v : ZMod (p ^ 2) := ((p - 1 - t : ℕ) : ZMod (p ^ 2)) with hv_def
  have hv : v = -u * jetp p (-wu) := by
    rw [← p_sub_eq hu_inv]
    have : p - 1 - t + (t + 1) = p := by omega
    have h2 : (((p - 1 - t + (t + 1) : ℕ)) : ZMod (p ^ 2)) = (p : ZMod (p ^ 2)) := by rw [this]
    rw [Nat.cast_add] at h2
    rw [hv_def, hu_def]
    linear_combination h2
  -- the Cs step
  have hCs := Cs_step (p := p) (r6 n p) (r2 n p) t B C b ε ht hB hB1 hC
  -- PA
  have hPA := PA_step (p := p) t ht
  -- PB
  have hPB : ((B + 1 : ℕ) : ZMod (p ^ 2)) ^ 2 * Jt p (r6 n p + 1) t ^ 2 =
      v ^ 2 * jetp p (2 * (b : ZMod (p ^ 2)) * wx) * Jt p (r6 n p + 1) (t + 1) ^ 2 := by
    rcases hbc with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
    · rw [h0'] at hB
      have := PB_side0 (p := p) (r6 n p + 1) t B (p - 1 - t - B - 1) (by omega) (by omega)
      rw [h0']
      simp only [Nat.cast_zero, mul_zero, zero_mul, jetp_zero, mul_one]
      have e : B + 1 + (p - 1 - t - B - 1) = p - 1 - t := by omega
      rw [e] at this
      exact this
    · rw [h0'] at hB
      have := PB_side1 (p := p) (r6 n p + 1) (t - (r6 n p + 1)) (p - 2 - t) t (by omega) (by omega)
        (((B + 1 : ℕ) : ZMod (p ^ 2))) wx ?_ hxB_inv
      · rw [h0']
        have e : p - 2 - t + 1 = p - 1 - t := by omega
        rw [e] at this
        simpa using this
      · have e : B + 1 + (t - (r6 n p + 1) + 1) = p := by omega
        have h2 := congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) e
        simp only [Nat.cast_add] at h2
        rw [Nat.cast_add]
        simpa [add_assoc] using h2
  -- PC
  have hPC : ((C + 1 : ℕ) : ZMod (p ^ 2)) ^ 3 * Jt p (p - r2 n p) t ^ 3 =
      -(v ^ 3) * jetp p (3 * (1 - (ε : ZMod (p ^ 2))) * wc) * Jt p (p - r2 n p) (t + 1) ^ 3 := by
    rcases hec with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
    · rw [h0'] at hC
      have := PC_side0 (p := p) (p - r2 n p) t (p - r2 n p - t - 2) (r2 n p) (by omega) (by omega)
        (((C + 1 : ℕ) : ZMod (p ^ 2))) wc ?_ hxC_inv
      · rw [h0']
        have e : p - r2 n p - t - 2 + 1 + r2 n p = p - 1 - t := by omega
        rw [e] at this
        simpa using this
      · have e : C + 1 + (p - r2 n p - t - 2 + 1) = p := by omega
        have h2 := congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) e
        simp only [Nat.cast_add] at h2
        rw [Nat.cast_add]
        simpa [add_assoc] using h2
    · rw [h0'] at hC
      have := PC_side1 (p := p) (p - r2 n p) C (p - 2 - t) t (by omega) (by omega)
      rw [h0']
      have e : p - 2 - t + 1 = p - 1 - t := by omega
      rw [e] at this
      simpa [jetp_zero] using this
  -- combine
  have hcomb := step_combine (Cs p (r6 n p) (r2 n p) b ε t) (Cs p (r6 n p) (r2 n p) b ε (t + 1))
    (Jt p 0 t) (Jt p 0 (t + 1)) (Jt p (r6 n p + 1) t) (Jt p (r6 n p + 1) (t + 1))
    (Jt p (p - r2 n p) t) (Jt p (p - r2 n p) (t + 1)) u v ((B + 1 : ℕ) : ZMod (p ^ 2))
    ((C + 1 : ℕ) : ZMod (p ^ 2)) (jetp p (2 * (b : ZMod (p ^ 2)) * wx))
    (jetp p (3 * (1 - (ε : ZMod (p ^ 2))) * wc)) (jetp p wu) (jetp p (-wu)) ((lam n p).toNat + 4)
    hCs hPB hPC hPA hv
  have hu5 : IsUnit (u ^ 5) := huu.pow 5
  have hS := hu5.mul_right_cancel hcomb
  -- the jet exponent
  set N : ℕ := (lam n p).toNat + 4 with hN
  have hNc : (N : ZMod (p ^ 2)) = ((lam n p : ℤ) : ZMod (p ^ 2)) + 4 := by
    rw [hN]; push_cast; rw [cast_toNat_lam h]
  set d : ZMod (p ^ 2) := (((lam n p - 1 : ℤ)) : ZMod (p ^ 2)) * wu + 2 * (b : ZMod (p ^ 2)) * wx
    + 3 * (1 - (ε : ZMod (p ^ 2))) * wc with hd_def
  have hJ : jetp p (-wu) ^ 5 * jetp p (2 * (b : ZMod (p ^ 2)) * wx) *
      jetp p (3 * (1 - (ε : ZMod (p ^ 2))) * wc) * jetp p wu ^ N = jetp p d := by
    rw [jetp_pow (-wu) 5, jetp_pow wu N, jetp_mul, jetp_mul, jetp_mul]
    congr 1
    rw [hNc, hd_def]
    push_cast
    ring
  rw [hJ] at hS
  -- the harmonic step
  have hXi : xiR n p (t + 1) = xiR n p t + d := by
    unfold xiR
    rw [hb1, he1, ← hb_def, ← hε_def]
    have hHu : Hz p (t + 1) = Hz p t + wu := Hz_succ t
    have hHb : b = 1 → Hz p (r6 n p + p - t) = Hz p (r6 n p + p - (t + 1)) + wx := by
      intro hb
      have e1 : r6 n p + p - t = (r6 n p + p - (t + 1)) + 1 := by
        rcases hbc with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> omega
      have e2 : r6 n p + p - (t + 1) = B := by
        rcases hbc with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] at hB <;> omega
      rw [e1, Hz_succ, e2]
    have hHc : ε = 0 → Hz p (r2 n p + (t + 1)) = Hz p (r2 n p + t) + wc := by
      intro hε
      have e1 : r2 n p + (t + 1) = (r2 n p + t) + 1 := by omega
      have e2 : r2 n p + t = C := by
        rcases hec with ⟨h0', h1'⟩ | ⟨h0', h1'⟩ <;> rw [h0'] at hC <;> omega
      rw [e1, Hz_succ, e2]
    rw [hHu]
    rcases hbc with ⟨hb0, _⟩ | ⟨hb0, _⟩ <;> rcases hec with ⟨he0, _⟩ | ⟨he0, _⟩
    · rw [hd_def]; simp only [hb0, he0, Nat.cast_zero, mul_zero, zero_mul, sub_zero, zero_add]
      rw [hHc he0]; ring
    · rw [hd_def]; simp only [hb0, he0, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, sub_zero, sub_self]
      ring
    · rw [hd_def]; simp only [hb0, he0, Nat.cast_zero, Nat.cast_one, mul_zero, zero_mul, sub_zero]
      rw [hHb hb0, hHc he0]; ring
    · rw [hd_def]; simp only [hb0, he0, Nat.cast_one, sub_self]
      rw [hHb hb0]; ring
  -- E1 at t and t+1
  have hms0 : mexp n p σW t = 0 := by
    unfold mexp; rw [h0]; simp [hpar]
  have hms1 : mexp n p σW (t + 1) = 0 := by
    unfold mexp; rw [h1]; simp [hpar]
  have E0 := fR_E1 h σW t hms0
  have E1 := fR_E1 h σW (t + 1) hms1
  rw [← hb_def, ← hε_def] at E0
  rw [hb1, he1] at E1
  have hX0 : IsUnit (Jt p (r6 n p + 1) t ^ 2 * Jt p (p - r2 n p) t ^ 3) :=
    ((isUnit_Jt _ _ (by omega)).pow 2).mul ((isUnit_Jt _ _ (by omega)).pow 3)
  have hX1 : IsUnit (Jt p (r6 n p + 1) (t + 1) ^ 2 * Jt p (p - r2 n p) (t + 1) ^ 3) :=
    ((isUnit_Jt _ _ ht).pow 2).mul ((isUnit_Jt _ _ ht).pow 3)
  have hJ2 : jetp p (xiR n p t) * jetp p d = jetp p (xiR n p (t + 1)) := by
    rw [jetp_mul, hXi]
  apply (hX0.mul hX1).mul_right_cancel
  linear_combination (Qhat n p σW t * jetp p (xiR n p t) *
      (Jt p (r6 n p + 1) t ^ 2 * Jt p (p - r2 n p) t ^ 3)) * E1 +
    (Qhat n p σW t * Qhat n p σW (t + 1) * jetp p (xiR n p t)) * hS -
    (Qhat n p σW (t + 1) * jetp p (xiR n p (t + 1)) *
      (Jt p (r6 n p + 1) (t + 1) ^ 2 * Jt p (p - r2 n p) (t + 1) ^ 3)) * E0 +
    (Qhat n p σW t * Qhat n p σW (t + 1) * Cs p (r6 n p) (r2 n p) b ε t * Jt p 0 t ^ N *
      (Jt p (r6 n p + 1) (t + 1) ^ 2 * Jt p (p - r2 n p) (t + 1) ^ 3)) * hJ2

end Step

section Main

variable {n p : ℕ} [hp : Fact p.Prime]

/-- **Lemma R modulo `p²` (content note, Lemma R).**  Let `W = {s < p : σ(s) = σ_W}` be a tie class
(`λ - σ_W` even).  With `f(s) = ĉ_s ∏_{r≠s} (s-r)^{2 μ'_r}` (`μ'_r = μ_r + [r ∉ W]`, `ĉ_s = Cs` the
low-digit factorial ratio of Lemma G) and `Q̂(s) = ∏_r (s-r)^{m_r} = Q(s)³ Z(s)²`, there is a unit `K`
(independent of `s`) with
`f(s) = K · Q̂(s) · (1 + p Ξ(s))`  in `ℤ/p²` for every `s ∈ W`,
where `Ξ(s) = (λ-1) H_s - 2 b H_{r₆+p-s} + 3 (1-ε) H_{r₂+s}` (`b, ε` the carry flags of `W`),
a combination of three harmonic digit functions of total weight `2 μ_W - 2` (`xiR_weight`). -/
theorem lemmaR_p2 (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) :
    ∃ K : ZMod (p ^ 2), IsUnit K ∧ ∀ s < p, sig n p s = σW →
      fR n p σW s = K * Qhat n p σW s * jetp p (xiR n p s) := by
  classical
  by_cases hex : ∃ s, s < p ∧ sig n p s = σW
  swap
  · exact ⟨1, isUnit_one, fun s hs hsg => absurd ⟨s, hs, hsg⟩ hex⟩
  have hu0 : Nat.find hex < p ∧ sig n p (Nat.find hex) = σW := Nat.find_spec hex
  have hmin : ∀ s, s < p → sig n p s = σW → Nat.find hex ≤ s :=
    fun s hs hsg => Nat.find_min' hex ⟨hs, hsg⟩
  set u0 := Nat.find hex with hu0_def
  have hp0 : 0 < p := hp.out.pos
  have hr6 : r6 n p < p := r6_lt n p hp0
  have hr2 : r2 n p < p := r2_lt n p hp0
  have hms : ∀ t, sig n p t = σW → mexp n p σW t = 0 := by
    intro t ht; unfold mexp; rw [ht]; simp [hpar]
  have hfU : IsUnit (fR n p σW u0) := by
    unfold fR
    refine (isUnit_Cs _ _ _ _ _ hr6 hr2 hu0.1 ?_ ?_).mul (isUnit_Pe _ _ hu0.1)
    · unfold bflag; split_ifs <;> omega
    · unfold eflag; split_ifs <;> omega
  have hQU : IsUnit (Qhat n p σW u0) := isUnit_Qhat σW u0 hu0.1 (hms u0 hu0.2)
  have hD : IsUnit (Qhat n p σW u0 * jetp p (xiR n p u0)) := hQU.mul (isUnit_jetp _)
  have hDi := ZMod.mul_inv_of_unit _ hD
  refine ⟨fR n p σW u0 * (Qhat n p σW u0 * jetp p (xiR n p u0))⁻¹, ?_, ?_⟩
  · exact hfU.mul (IsUnit.of_mul_eq_one (Qhat n p σW u0 * jetp p (xiR n p u0))
      (by rw [mul_comm]; exact hDi))
  · have key : ∀ d, u0 + d < p → sig n p (u0 + d) = σW →
        fR n p σW (u0 + d) = fR n p σW u0 * (Qhat n p σW u0 * jetp p (xiR n p u0))⁻¹ *
          Qhat n p σW (u0 + d) * jetp p (xiR n p (u0 + d)) := by
      intro d
      induction d with
      | zero =>
        intro _ _
        simp only [add_zero]
        linear_combination (-fR n p σW u0) * hDi
      | succ d ih =>
        intro hd1 hs1
        have e0 := sig_mono n p (show u0 ≤ u0 + d by omega)
        have e1 := sig_mono n p (show u0 + d ≤ u0 + d + 1 by omega)
        have hs0 : sig n p (u0 + d) = σW := by
          have : u0 + (d + 1) = u0 + d + 1 := by omega
          rw [this] at hs1
          omega
        have IH := ih (by omega) hs0
        have hL := fR_step h σW (u0 + d) hpar (by omega) hs0 (by
          have : u0 + (d + 1) = u0 + d + 1 := by omega
          rw [this] at hs1; exact hs1)
        have hQt : IsUnit (Qhat n p σW (u0 + d)) :=
          isUnit_Qhat σW (u0 + d) (by omega) (hms _ hs0)
        have hcast : u0 + (d + 1) = u0 + d + 1 := by omega
        rw [hcast]
        apply (hQt.mul (isUnit_jetp (xiR n p (u0 + d)))).mul_right_cancel
        linear_combination hL + (Qhat n p σW (u0 + d + 1) * jetp p (xiR n p (u0 + d + 1))) * IH
    intro s hs hsg
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hmin s hs hsg)
    exact key d hs hsg

/-- The total weight of the harmonic terms of `Ξ(s)` is `2 μ_W - 2`. -/
theorem xiR_weight (h : Rng n p) (σW s : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0)
    (hs : s < p) (hsg : sig n p s = σW) :
    (lam n p - 1 : ℤ) - 2 * (bflag n p s : ℤ) + 3 * (1 - (eflag n p s : ℤ)) =
      2 * (mu n p s : ℤ) - 2 := by
  have h3 := (lemmaS h).2.2.1 s hs
  have h2 := sig_eq_flags n p s
  rw [hsg] at h3 h2
  simp only [hpar, if_true] at h3
  have hb : (bflag n p s : ℤ) ≤ 1 := by unfold bflag; split_ifs <;> omega
  have he : (eflag n p s : ℤ) ≤ 1 := by unfold eflag; split_ifs <;> omega
  omega

/-- Arguments of the harmonic digit functions stay in `[0, p)` on `W`. -/
theorem xiR_args (h : Rng n p) (s : ℕ) (hs : s < p) :
    s < p ∧ (bflag n p s = 1 → r6 n p + p - s < p ∧ s ≤ r6 n p + p) ∧
      (eflag n p s = 0 → r2 n p + s < p) := by
  have hp0 : 0 < p := hp.out.pos
  have hr6 : r6 n p < p := r6_lt n p hp0
  have hr2 : r2 n p < p := r2_lt n p hp0
  refine ⟨hs, ?_, ?_⟩
  · intro hb; unfold bflag at hb; split_ifs at hb <;> omega
  · intro he; unfold eflag at he; split_ifs at he <;> omega

lemma jetp_cast_one (x : ZMod (p ^ 2)) :
    (ZMod.castHom (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) (ZMod p)) (jetp p x) = 1 := by
  unfold jetp
  simp

/-- **Lemma R modulo `p`**: `f(s) Q̂(s') = f(s') Q̂(s)` on `W`, i.e. `f = K₁ Q̂` (the unit `K₁`). -/
theorem lemmaR_p (h : Rng n p) (σW : ℕ) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) :
    ∃ K : ZMod (p ^ 2), IsUnit K ∧ ∀ s < p, sig n p s = σW →
      (ZMod.castHom (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) (ZMod p)) (fR n p σW s) =
        (ZMod.castHom (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)) (ZMod p)) (K * Qhat n p σW s) := by
  obtain ⟨K, hK, hf⟩ := lemmaR_p2 h σW hpar
  refine ⟨K, hK, fun s hs hsg => ?_⟩
  rw [hf s hs hsg, map_mul, jetp_cast_one, mul_one]

end Main

section Extras

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `Q̂` has multiplicity `0` on `W`. -/
lemma mexp_W (σW r : ℕ) (hr : sig n p r = σW) (hpar : (lam n p - (σW : ℤ)) % 2 = 0) :
    mexp n p σW r = 0 := by
  unfold mexp; rw [hr]; simp [hpar]

/-- `Q̂` has multiplicity `2` on `Z` (other tie class). -/
lemma mexp_Z (σW r : ℕ) (hr : sig n p r ≠ σW) (hev : (lam n p - (sig n p r : ℤ)) % 2 = 0) :
    mexp n p σW r = 2 := by
  unfold mexp; simp [hr, hev]

/-- `Q̂` has multiplicity `3` on `N` (parity-odd classes). -/
lemma mexp_N (σW r : ℕ) (hr : sig n p r ≠ σW) (hod : (lam n p - (sig n p r : ℤ)) % 2 ≠ 0) :
    mexp n p σW r = 3 := by
  unfold mexp; simp [hr, hod]

/-- `Q̂` as a polynomial over `ℤ/p²`: `∏_{r<p} (X - r)^{m_r} = Q³ Z²`. -/
noncomputable def QhatPoly (n p σW : ℕ) : Polynomial (ZMod (p ^ 2)) :=
  ∏ r ∈ range p, (Polynomial.X - Polynomial.C (r : ZMod (p ^ 2))) ^ mexp n p σW r

lemma QhatPoly_eval (σW s : ℕ) :
    (QhatPoly n p σW).eval (s : ZMod (p ^ 2)) = Qhat n p σW s := by
  unfold QhatPoly Qhat
  simp [Polynomial.eval_prod]

lemma QhatPoly_monic (σW : ℕ) : (QhatPoly n p σW).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun r _ => (Polynomial.monic_X_sub_C _).pow _)

lemma QhatPoly_natDegree (σW : ℕ) :
    (QhatPoly n p σW).natDegree = ∑ r ∈ range p, mexp n p σW r := by
  haveI : Fact (1 < p ^ 2) := ⟨by have := hp.out.one_lt; nlinarith⟩
  unfold QhatPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun r _ => (Polynomial.monic_X_sub_C _).pow _)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Polynomial.Monic.natDegree_pow (Polynomial.monic_X_sub_C _), Polynomial.natDegree_X_sub_C]
  ring

end Extras

end CatalanCore.Lai

#print axioms CatalanCore.Lai.Jt_ge
#print axioms CatalanCore.Lai.Jt_lt
#print axioms CatalanCore.Lai.Cs_step
#print axioms CatalanCore.Lai.fR_E1
#print axioms CatalanCore.Lai.fR_step
#print axioms CatalanCore.Lai.lemmaR_p2
#print axioms CatalanCore.Lai.xiR_weight
#print axioms CatalanCore.Lai.xiR_args
#print axioms CatalanCore.Lai.lemmaR_p
#print axioms CatalanCore.Lai.QhatPoly_natDegree
#print axioms CatalanCore.Lai.QhatPoly_eval
