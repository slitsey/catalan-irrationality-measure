module

public import CatalanCore.Uniform.Content.UFFamily3.Help

@[expose] public section

/-!
# UF thirds families: kill of a run from a pair theorem (lane H, H12)

`kill_of_pair` is the interface between the generated data (a `pair` theorem per ordered pair of
start types: an evaluation point, two checked LU records and a prime-avoiding cross wedge) and the
window cell `cell3Gen`.  `Lprim`/`not_dvd_smooth`: the smooth-gcd step of the data (a prime
`p ≥ 60` divides no divisor of a power of the primorial of the primes `< 60`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3

/-- Primes below `60`. -/
def primes60 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]

/-- Their product. -/
def Lprim : ℕ := primes60.prod

theorem not_dvd_Lprim {p : ℕ} (hp : p.Prime) (h : 60 ≤ p) : ¬ p ∣ Lprim :=
  not_dvd_of_list hp primes60 (fun q hq => by
    simp only [primes60, List.mem_cons, List.not_mem_nil, or_false] at hq
    refine ⟨?_, by omega⟩
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> norm_num)

/-- A prime `≥ 60` does not divide an integer whose absolute value divides `Lprim ^ E`. -/
theorem not_dvd_smooth {p : ℕ} (hp : p.Prime) (h : 60 ≤ p) (g : ℤ) (E : ℕ)
    (hg : g.natAbs ∣ Lprim ^ E) : ¬ (p : ℤ) ∣ g := by
  intro hd
  have h1 : p ∣ g.natAbs := Int.natCast_dvd.1 hd
  exact not_dvd_Lprim hp h (hp.dvd_of_dvd_pow (h1.trans hg))

variable {c : ℚ} {hc : 0 < c} {Fr : Frame}

/-- **Kill of a node `v` of the run starting at `ts` against `t₀` from a pair theorem.** -/
theorem kill_of_pair (T : TwoTermData Fr 3 2) {r p N t0 tv m : ℕ} [Fact p.Prime]
    (W : Win3 c hc 3 2 r p N t0 tv m) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 3 * t - 2)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) (ts v AJ BJ AK BK : ℕ)
    (htsN : ts < N) (htsr : r ≤ ts) (htsp : ts < r + p) (hnts : ¬ p ∣ ts) (htsv : ts ≤ v) (hvp : v < r + p)
    (hdiv : v / p = ts / p)
    (hw : NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) ts (v - ts))
    (hAJ : t0 / p = AJ) (hBJ : (3 * t0 - 2) / p = BJ) (hAK : ts / p = AK)
    (hBK : (3 * ts - 2) / p = BK)
    (hpair : ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 AJ BJ 1 AJ) DJ ∧
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 AK BK 1 AK) DK ∧
      XJ.ok (famType 3 AJ BJ 1 AJ).nodes.length
        (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 AJ BJ 1 AJ) DJ) DJ = true ∧
      XK.ok (famType 3 AK BK 1 AK).nodes.length
        (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 AK BK 1 AK) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b) :
    Nonempty (AltKill c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) t0 v) := by
  obtain ⟨u0, DJ, DK, XJ, XK, hJ, hK, oJ, oK, hnd⟩ := hpair
  exact ⟨altKillRun T W.hr2 W.hr0 W.hqp W.hqo W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) t0 ts v
    (by have := W.ht0b; have := W.hrN; omega) htsN
    W.ht0r (by have := W.ht0b; have := W.hpm; omega) W.hnt0 htsr htsp hnts htsv hvp hdiv hw
    u0 AJ BJ AK BK hAJ hBJ hAK hBK DJ DK hJ hK XJ XK oJ oK hnd⟩

end CatalanCore.Uniform.Content.UFFamily3
