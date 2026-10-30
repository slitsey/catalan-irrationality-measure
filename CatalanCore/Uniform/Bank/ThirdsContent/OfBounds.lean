module

public import CatalanCore.Uniform.Bank.ThirdsContent.Assemble

@[expose] public section
set_option Elab.async false

/-! # Thirds content from `GLE` bounds (lane B, B4b)

`thirds_content_of_bounds`: the cleanest interface.  The price of a member at a prime is its
OPTIMAL clearing exponent `lpOpt i p = min {n | GLE p n (Q i)}` (finite by the crude exponent).
Then every layer (tropical, M3D, LP1/LP2, rank, UF) enters only by proving a `GLE p n (Q i)`
statement; the hypotheses `tail / pre / cov` ask only for SOME `n` with `GLE p n (Q i)` below the
template line.  Adding the UF layer adds more admissible `n`, changes no statement.
Exceptional primes are discharged (`thirds_content_of_layers`).  `Lam` is a parameter. -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Uniform.Content.Member CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset

open Classical in
/-- The optimal clearing exponent of a member at a prime (`0` at non-primes). -/
noncomputable def lpOpt (Fr : Frame) (depth : ℕ) (i : (FamE Fr depth).ι) (p : ℕ) : ℕ :=
  if hp : p.Prime then
    haveI : Fact p.Prime := ⟨hp⟩
    if h : ∃ n, GLE p n ((FamE Fr depth).Q i) then Nat.find h else 0
  else 0

theorem lpOpt_gle (Fr : Frame) (depth : ℕ) (i : (FamE Fr depth).ι) (p : ℕ) [hp : Fact p.Prime]
    (h : ∃ n, GLE p n ((FamE Fr depth).Q i)) : GLE p (lpOpt Fr depth i p) ((FamE Fr depth).Q i) := by
  classical
  unfold lpOpt
  rw [dif_pos hp.out, dif_pos h]
  exact Nat.find_spec h

theorem lpOpt_le (Fr : Frame) (depth : ℕ) (i : (FamE Fr depth).ι) (p : ℕ) [hp : Fact p.Prime]
    {n : ℕ} (h : GLE p n ((FamE Fr depth).Q i)) : lpOpt Fr depth i p ≤ n := by
  classical
  unfold lpOpt
  rw [dif_pos hp.out, dif_pos ⟨n, h⟩]
  exact Nat.find_min' _ h

theorem exists_gle_even (Fr : Frame) (depth : ℕ) (i : (FamE Fr depth).ι)
    (hi : (FamE Fr depth).Adm i) (p : ℕ) [Fact p.Prime] :
    ∃ n, GLE p n ((FamE Fr depth).Q i) :=
  ⟨_, altGeom_gle_Ecrude (3 / 10) c310_pos (by norm_num) Fr depth i hi.2 p⟩

theorem thirds_content_of_bounds (Fr : Frame) (depth : ℕ) (M : ℕ) [NeZero M] (Lam : ℝ)
    (B : SmallBudget) (tmpl : ℝ → ZMod M → Template) (τ : ℝ)
    (hmass : ∀ ε : ℝ, 0 < ε → contentConstant M (tmpl ε) ≤ Lam + ε)
    (tend_le : ∀ ε : ℝ, 0 < ε → ∀ c : ZMod M, IsUnit c → (tmpl ε c).tend ≤ τ)
    (tail : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ p : ℕ, p.Prime → (p : ZMod M) = c → ⌊(tmpl ε c).tend * G310.scale i⌋₊ < p →
        ∀ [Fact p.Prime], GLE p 0 ((FamE Fr depth).Q i))
    (pre : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
      p ≤ ⌊(tmpl ε c).t1 * G310.scale i⌋₊ → p.Prime → (p : ZMod M) = c →
        ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
          (n : ℝ) ≤ (tmpl ε c).α0 * G310.scale i + B.X (G310.scale i) p)
    (cov : ∀ ε : ℝ, 0 < ε → ∀ i, (FamE Fr depth).Adm i → ∀ c : ZMod M, IsUnit c →
      ∀ P ∈ (tmpl ε c).l, ∀ p : ℕ, ⌊P.s * G310.scale i⌋₊ < p → p ≤ ⌊P.t * G310.scale i⌋₊ →
        p.Prime → (p : ZMod M) = c → ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
          (n : ℝ) ≤ P.α * G310.scale i + P.β * p + P.C) :
    HasScaledContent (FamE Fr depth) G310.scale Lam := by
  classical
  refine thirds_content_of_layers Fr depth M Lam (lpOpt Fr depth)
    (fun i => ⌊τ * G310.scale i⌋₊ + 1) ?_ ?_ B tmpl hmass ?_ ?_ ?_ ?_
  · intro i hi p _ _
    exact lpOpt_gle Fr depth i p (exists_gle_even Fr depth i hi p)
  · intro i hi p hp hM hc
    have hunit : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hM
    haveI : Fact p.Prime := ⟨hp⟩
    have hlt : ⌊(tmpl 1 (p : ZMod M)).tend * G310.scale i⌋₊ < p := by
      have : ⌊(tmpl 1 (p : ZMod M)).tend * G310.scale i⌋₊ ≤ ⌊τ * G310.scale i⌋₊ :=
        Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le 1 one_pos _ hunit)
          (Nat.cast_nonneg _))
      omega
    exact Nat.le_zero.1 (lpOpt_le Fr depth i p (tail 1 one_pos i hi _ hunit p hp rfl hlt))
  · intro ε hε i hi c hc p hp hpc hlt
    haveI : Fact p.Prime := ⟨hp⟩
    exact Nat.le_zero.1 (lpOpt_le Fr depth i p (tail ε hε i hi c hc p hp hpc hlt))
  · intro ε hε i hi c hc
    have : ⌊(tmpl ε c).tend * G310.scale i⌋₊ ≤ ⌊τ * G310.scale i⌋₊ :=
      Nat.floor_le_floor (mul_le_mul_of_nonneg_right (tend_le ε hε c hc) (Nat.cast_nonneg _))
    omega
  · intro ε hε i hi c hc p h1 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn, hb⟩ := pre ε hε i hi c hc p h1 hp hpc
    exact (Nat.cast_le.2 (lpOpt_le Fr depth i p hn)).trans hb
  · intro ε hε i hi c hc P hP p h1 h2 hp hpc
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn, hb⟩ := cov ε hε i hi c hc P hP p h1 h2 hp hpc
    exact (Nat.cast_le.2 (lpOpt_le Fr depth i p hn)).trans hb

end CatalanCore.Uniform.Bank.ThirdsContent
