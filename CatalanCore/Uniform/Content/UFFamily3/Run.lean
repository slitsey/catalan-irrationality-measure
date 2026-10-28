module

public import CatalanCore.Uniform.Content.UFFamily2.Gen

@[expose] public section

/-!
# UF families: kill certificates along whole runs (lane H, H12)

The kill of a border node `v` against the representative `t₀` uses the LU records of the joint type
of the RUN START `ts ≤ v` and the shift (W2) from `ts` to `v` inside a nonsingular window:

* `fiber_std`: the `FiberList` of a border node `v` (not a multiple of `p`, `r ≤ v < r + p`):
  the core nodes `v - j p`, `1 ≤ j ≤ A`, i.e. the type `famType q A B 1 A` with `A = ⌊v/p⌋`,
  `B = ⌊(q v - o)/p⌋`.
* `killRunCert`: `KillCert` of `v` against `t₀` from the types at `t₀` and `ts`, the shift
  `ShiftData ts v`, and two checked `LuData` records (one record per run, not per node).
* `altKillRun`: the same for the alternating geometry, the shift being `alt_shiftData`
  (`NoSingWin ts (v - ts)` and `⌊v/p⌋ = ⌊ts/p⌋`).  `altKillRun_all`: every `v` of a run.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **The fiber of a border node** `v` (`r ≤ v < r + p`, `p ∤ v`): the core nodes `v - j p`,
`1 ≤ j ≤ A = ⌊v/p⌋`. -/
noncomputable def fiber_std {r v : ℕ} (c : ι → ℕ) (hcr : ∀ a, c a < r)
    (hcov : ∀ x, x < r → ∃ a, c a = x) (hcinj : Function.Injective c) (hr0 : 0 < r) (hrv : r ≤ v)
    (hvr : v < r + p) (hndv : ¬ p ∣ v) (hqo : o ≤ q) (A B : ℕ) (hA : v / p = A)
    (hB : (q * v - o) / p = B) : FiberList p q o c v (famType q A B 1 A) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine fiberList_range q o r v 1 A A B c hcr hcov hcinj hrv hqo le_rfl (by omega)
    (fun j hj1 hj2 => by omega) ?_ ?_ hA hB
  · have h1 := Nat.lt_mul_div_succ v hp
    rw [hA] at h1
    have e : (1 + A) * p = p * (A + 1) := by ring
    rw [e]; exact h1
  · by_cases h0 : A = 0
    · exact Or.inl h0
    · right
      have h1 : v / p * p ≤ v := Nat.div_mul_le_self v p
      have h2 : v / p * p ≠ v := fun h => hndv ⟨v / p, by rw [mul_comm]; exact h.symm⟩
      have h3 : v / p * p < v := lt_of_le_of_ne h1 h2
      rw [hA] at h3
      rwa [Nat.add_sub_cancel_left]

/-- **Kill certificate of `v` against `t₀` from the types at `t₀` and at the run start `ts`.**
One LU record per run: `ShiftData ts v` carries the data to every node of the run. -/
noncomputable def killRunCert (T : TwoTermData Fr q o) (hqp : q < p) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N)
    (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (hcinj : Function.Injective c)
    {r : ℕ} (hr0 : 0 < r) (hcr : ∀ a, c a < r) (hcov : ∀ x, x < r → ∃ a, c a = x) (hqo : o ≤ q)
    (t0 ts v : ℕ) (ht0N : t0 < N) (htsN : ts < N) (ht0r : r ≤ t0) (ht0p : t0 < r + p)
    (hnt0 : ¬ p ∣ t0) (htsr : r ≤ ts) (htsp : ts < r + p) (hnts : ¬ p ∣ ts)
    (hshift : ShiftData (twoTermPoleData T hNp.le hsq hnorm hnorm0) c ts v)
    (u0 : ℤ) (AJ BJ AK BK : ℕ) (hAJ : t0 / p = AJ) (hBJ : (q * t0 - o) / p = BJ)
    (hAK : ts / p = AK) (hBK : (q * ts - o) / p = BK) (DJ DK : ℤ)
    (hJ : IntOK q o (p % q) Fr.norm u0 (famType q AJ BJ 1 AJ) DJ)
    (hK : IntOK q o (p % q) Fr.norm u0 (famType q AK BK 1 AK) DK) (XJ XK : LuData)
    (oJ : XJ.ok (famType q AJ BJ 1 AJ).nodes.length
      (mkFib q o (p % q) Fr.norm u0 (famType q AJ BJ 1 AJ) DJ) DJ = true)
    (oK : XK.ok (famType q AK BK 1 AK).nodes.length
      (mkFib q o (p % q) Fr.norm u0 (famType q AK BK 1 AK) DK) DK = true)
    (hqp' : q < p) (hnd : ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b) :
    KillCert (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp c xs ys hc hx hy t0 v :=
  KillCert.ofTypes T hqp hNp hsq hnorm hnorm0 c xs ys hc hx hy hcinj t0 v ts ht0N htsN hshift u0
    (famType q AJ BJ 1 AJ) (famType q AK BK 1 AK) DJ DK
    (fiber_std c hcr hcov hcinj hr0 ht0r ht0p hnt0 hqo AJ BJ hAJ hBJ)
    (fiber_std c hcr hcov hcinj hr0 htsr htsp hnts hqo AK BK hAK hBK) hJ hK
    (LuData.crossZ_zmod_ne oJ oK hnd)

end CatalanCore.Uniform.Content.UFFamily3
