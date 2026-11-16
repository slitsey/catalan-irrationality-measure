module

public import CatalanCore.Zeta5.Frames.InnerAlloc

@[expose] public section

/-!
# ZC32, step 6: the parity gain as a named hypothesis

The parity gain `k` of Z5-PARITY (final report): for the inner allocation of `InnerHyp`, let
`S = {a ≠ 0 : ℓ_K(a) even}` (the even group of classes), `ε = epsSet`, `T = innerT`. Then

* `T` odd:  `k = [#{a ∈ S : ℓ_N(a) even, a ∉ ε} − #{b ∈ S : ℓ_N(b) odd, b ∈ ε, L_b > 0}]₊ − L₀`,
* `T` even: `k = [#{a ∈ S : ℓ_N(a) even, a ∈ ε} − #{b ∈ S : ℓ_N(b) odd, b ∉ ε}]₊ − L₀`

(truncated subtraction). `ParityGain` is the statement `v_p^G(Δ_K) ≥ 2 Σ w + k` (statement (H′)
assembled with `radical_T_odd/even` and `parity_gain_delta`), proved by Z5-PADIC; it enters
ZC32 as the explicit hypothesis `hpar`, only for the primes with `K/p ≤ 200` used by ZC38.
-/

open Finset

namespace Apery

open Classical in
/-- The even group `S = {a ≠ 0 : ℓ_K(a) even}`. -/
noncomputable def parS (p n : ℕ) : Finset (Fin (p / 2 + 1)) :=
  Finset.univ.filter (fun a => a ≠ 0 ∧ lK p n a % 2 = 0)

open Classical in
/-- The parity gain `k` of Z5-PARITY. -/
noncomputable def kpar (p n L0 : ℕ) : ℕ :=
  if innerT p n L0 % 2 = 1 then
    ((parS p n).filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∉ epsSet p n L0)).card
      - ((parS p n).filter (fun b : Fin (p / 2 + 1) => lN p n b % 2 = 1 ∧ b ∈ epsSet p n L0 ∧
          0 < innerL p n L0 b)).card - L0
  else
    ((parS p n).filter (fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∈ epsSet p n L0)).card
      - ((parS p n).filter (fun b : Fin (p / 2 + 1) => lN p n b % 2 = 1 ∧ b ∉ epsSet p n L0)).card - L0

/-- **The parity gain (hypothesis `hpar` of ZC32).** For the inner allocation with reserve
`L₀ = 4M + 10` and `K/p ≤ 200`: `v_p^G(Δ_K) ≥ 2 Σ w + k`. -/
def ParityGain : Prop :=
  ∀ (p n M : ℕ) (H : InnerHyp p n M (4 * M + 10)), 40 * n ≤ 200 * p →
    GV p (Δ n) (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n (4 * M + 10) a)),
      winner H.m_pos (innerL p n (4 * M + 10)) (Bse p (40 * n) (3 * n)) s
        + (kpar p n (4 * M + 10) : ℚ))

end Apery
