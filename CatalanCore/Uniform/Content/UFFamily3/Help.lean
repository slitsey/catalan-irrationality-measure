module

public import CatalanCore.Uniform.Content.UFFamily3.Gen3

@[expose] public section

/-!
# UF thirds families: shared helpers (lane H, H12)

* `cT = 3/10`, `borderSize_T`: the border size `(3 r + 9)/20` of the thirds geometry at even `r ≥ 4`;
* `altKillRun`: `AltKill` of a border node `v` of a run starting at `ts`, from two checked LU
  records (the run-shift lemma in the alternating geometry);
* divisibility, `N < p²` and `hsq` helpers; `not_dvd_of_list`: a prime above every listed prime does
  not divide their product (smooth gcd of the Bezout switch).
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

/-- The thirds block constant `c = 2 α = 3/10`. -/
def cT : ℚ := 3 / 10

theorem cT_pos : 0 < cT := by unfold cT; norm_num

theorem borderSize_T {r : ℕ} (hr : r % 2 = 0) (h4 : 4 ≤ r) :
    (altGeom cT cT_pos).borderSize r = (3 * r + 9) / 20 := by
  rw [altGeom_borderSize cT cT_pos hr]
  set n := (3 * r + 9) / 20 with hn
  have h1 : 20 * n ≤ 3 * r + 9 := by omega
  have h2 : 3 * r + 9 < 20 * n + 20 := by omega
  have hn1 : 1 ≤ n := by omega
  have h3 : 3 * r ≤ 20 * n + 10 := by omega
  have q3 : (3 * r : ℚ) ≤ 20 * n + 10 := by exact_mod_cast h3
  have q1 : (20 * n : ℚ) ≤ 3 * r + 9 := by exact_mod_cast h1
  have q2 : (3 * r + 9 : ℚ) < 20 * n + 20 := by exact_mod_cast h2
  have e2 : ⌈(cT * r - 1) / 2⌉₊ = n := by
    rw [Nat.ceil_eq_iff (by omega)]
    unfold cT
    have : ((n - 1 : ℕ) : ℚ) = n - 1 := by
      rw [Nat.cast_sub hn1]; simp
    rw [this]
    constructor <;> linarith
  have e1 : n ≤ ⌈cT * r / 2⌉₊ := by
    rw [← e2]
    exact Nat.ceil_mono (by linarith)
  rw [e2]; exact min_eq_right e1

theorem notdvd_between {p a x : ℕ} (h1 : a * p < x) (h2 : x < (a + 1) * p) : ¬ p ∣ x := by
  rintro ⟨j, rfl⟩
  have h3 : a < j := by
    by_contra h; push Not at h
    have := Nat.mul_le_mul_right p h; nlinarith
  have h4 : j < a + 1 := by
    by_contra h; push Not at h
    have := Nat.mul_le_mul_right p h; nlinarith
  omega

theorem notdvd_pole {p P j : ℕ} (h : 3 * P = j * p + 2) (hp : 2 < p) : ¬ p ∣ P := by
  intro ⟨x, hx⟩
  have : p ∣ 2 := by
    have h2 : p ∣ 3 * P := Dvd.dvd.mul_left ⟨x, hx⟩ 3
    rw [h] at h2
    exact (Nat.dvd_add_right (Dvd.intro_left j rfl)).1 h2
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem notdvd_succ_mult {p j : ℕ} (hp : 1 < p) : ¬ p ∣ j * p + 1 := by
  intro h
  have := (Nat.dvd_add_right (Dvd.intro_left j rfl)).1 h
  have := Nat.le_of_dvd (by norm_num) this
  omega

theorem hNp_T {r p : ℕ} (h : 3 * r < 10 * p) (hp : 14 ≤ p) : r + p < p * p := by
  nlinarith

theorem hsq_T {r p : ℕ} (h : 3 * r < 10 * p) (hp : 14 ≤ p) :
    ∀ t, 1 ≤ t → t < r + p → ¬ p ^ 2 ∣ 3 * t - 2 := by
  intro t ht1 ht2 hd
  have h13 : 13 * p ≤ p * p := by nlinarith
  have h3 : 3 * t - 2 < p ^ 2 := by rw [sq]; omega
  have := Nat.eq_zero_of_dvd_of_lt hd h3
  omega

/-- A prime above every prime of a list does not divide the product. -/
theorem not_dvd_of_list {p : ℕ} (hp : p.Prime) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime ∧ q < p) :
    ¬ p ∣ l.prod := by
  induction l with
  | nil => simp; exact hp.one_lt.ne'
  | cons a l ih =>
    rw [List.prod_cons]
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := (hl a (by simp)).1
      have := (Nat.prime_dvd_prime_iff_eq hp this).1 h
      have := (hl a (by simp)).2
      omega
    · exact ih (fun q hq => hl q (by simp [hq])) h

theorem not_dvd_int_of_list {p : ℕ} (hp : p.Prime) (g : ℤ) (l : List ℕ)
    (hl : ∀ q ∈ l, q.Prime ∧ q < p) (hg : g.natAbs = l.prod) : ¬ (p : ℤ) ∣ g := by
  intro h
  have : p ∣ g.natAbs := Int.natCast_dvd.1 h
  rw [hg] at this
  exact not_dvd_of_list hp l hl this

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ}

/-- **Run-shift lemma in the alternating geometry.**  `v` lies in the run `[ts, ..]` (nonsingular
window `(ts, v]`, one `p`-block); the kill certificate of `v` against `t₀` uses the LU records of
the types at `t₀` and at the run start `ts` only. -/
noncomputable def altKillRun (T : TwoTermData Fr q o) {r p N : ℕ} [Fact p.Prime]
    (hr : r % 2 = 0) (hr0 : 0 < r) (hqp : q < p) (hqo : o ≤ q) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (t0 ts v : ℕ) (ht0N : t0 < N) (htsN : ts < N) (ht0r : r ≤ t0) (ht0p : t0 < r + p)
    (hnt0 : ¬ p ∣ t0) (htsr : r ≤ ts) (htsp : ts < r + p) (hnts : ¬ p ∣ ts) (htsv : ts ≤ v)
    (hvp : v < r + p) (hdiv : v / p = ts / p)
    (hw : NoSingWin (twoTermPoleData T hNp.le hsq hnorm hnorm0) ts (v - ts))
    (u0 : ℤ) (AJ BJ AK BK : ℕ) (hAJ : t0 / p = AJ) (hBJ : (q * t0 - o) / p = BJ)
    (hAK : ts / p = AK) (hBK : (q * ts - o) / p = BK) (DJ DK : ℤ)
    (hJ : IntOK q o (p % q) Fr.norm u0 (famType q AJ BJ 1 AJ) DJ)
    (hK : IntOK q o (p % q) Fr.norm u0 (famType q AK BK 1 AK) DK) (XJ XK : LuData)
    (oJ : XJ.ok (famType q AJ BJ 1 AJ).nodes.length
      (mkFib q o (p % q) Fr.norm u0 (famType q AJ BJ 1 AJ) DJ) DJ = true)
    (oK : XK.ok (famType q AK BK 1 AK).nodes.length
      (mkFib q o (p % q) Fr.norm u0 (famType q AK BK 1 AK) DK) DK = true)
    (hnd : ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b) :
    AltKill c hc hr T hNp hsq hnorm hnorm0 hrN t0 v := by
  have hv : ts + (v - ts) = v := by omega
  have sh := alt_shiftData T hNp.le hsq hnorm hnorm0 _ (altGeom_C c hc r) ts (v - ts) htsr
    (by omega) (by rw [hv]; exact hdiv) (by simpa using hw)
  rw [hv] at sh
  exact killRunCert T hqp hNp hsq hnorm hnorm0
    (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
    ((altGeom c hc).geometry r).ys (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN)
    Subtype.val_injective hr0 (alt_core_lt c hc) (alt_hcov c hc r) hqo t0 ts v ht0N htsN
    ht0r ht0p hnt0 htsr htsp hnts sh
    u0 AJ BJ AK BK hAJ hBJ hAK hBK DJ DK hJ hK XJ XK oJ oK hqp hnd

end CatalanCore.Uniform.Content.UFFamily3
