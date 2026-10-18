module

public import CatalanCore.NT.Window

@[expose] public section

/-!
# Standard prime rules and the mod 4 / mod 6 instances (design WP5)

* `PrimeRule.ofDvd`   : `Bad l q := l ∣ q`, weight `1`.
* `PrimeRule.ofSqDvd` : `Bad l q := l² ∣ q ∧ ¬ l³ ∣ q`, weight `1/2` (Lemma 3 style).
Both satisfy `BadBound`, so `exists_prime_window` applies; `mod4` (classes 1, 3) and `mod6`
(class 1) are the rules needed by lambda and P6.
-/

namespace CatalanCore

/-- Bad primes are the divisors of `q`; weight `1`. -/
def PrimeRule.ofDvd (m : ℕ) (r : ZMod m) (hr : IsUnit r) : PrimeRule where
  m := m
  r := r
  hr := hr
  Bad := fun l q ↦ l ∣ q
  weight := 1

instance (m : ℕ) (r : ZMod m) (hr : IsUnit r) [NeZero m] :
    NeZero (PrimeRule.ofDvd m r hr).m := ‹NeZero m›

theorem PrimeRule.ofDvd_badBound (m : ℕ) (r : ZMod m) (hr : IsUnit r) :
    (PrimeRule.ofDvd m r hr).BadBound :=
  PrimeRule.badBound_of_pow_dvd _ (k := 1) one_pos (fun l q (h : l ∣ q) ↦ by simpa using h)
    (by simp [PrimeRule.ofDvd])

/-- Bad primes are those with `l² ∥ q`; weight `1/2`. -/
def PrimeRule.ofSqDvd (m : ℕ) (r : ZMod m) (hr : IsUnit r) : PrimeRule where
  m := m
  r := r
  hr := hr
  Bad := fun l q ↦ l ^ 2 ∣ q ∧ ¬ l ^ 3 ∣ q
  weight := 1 / 2

instance (m : ℕ) (r : ZMod m) (hr : IsUnit r) [NeZero m] :
    NeZero (PrimeRule.ofSqDvd m r hr).m := ‹NeZero m›

theorem PrimeRule.ofSqDvd_badBound (m : ℕ) (r : ZMod m) (hr : IsUnit r) :
    (PrimeRule.ofSqDvd m r hr).BadBound :=
  PrimeRule.badBound_of_pow_dvd _ (k := 2) two_pos (fun l q h ↦ h.1)
    (by simp [PrimeRule.ofSqDvd])

theorem isUnit_mod4_one : IsUnit (1 : ZMod 4) := isUnit_one
theorem isUnit_mod4_three : IsUnit (3 : ZMod 4) := by decide
theorem isUnit_mod6_one : IsUnit (1 : ZMod 6) := isUnit_one

end CatalanCore

namespace CatalanCore.NT

/-- lambda: primes `≡ 3 (mod 4)` (density `1/2`). -/
theorem pnt_mod4_three :
    Filter.Tendsto (fun x : ℝ ↦ thetaClass 4 3 x / x) Filter.atTop (nhds (1 / 2)) := by
  have h := pnt_class (m := 4) (r := 3) isUnit_mod4_three
  have e : (Nat.totient 4 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rwa [e] at h

/-- lambda': primes `≡ 1 (mod 4)` (density `1/2`). -/
theorem pnt_mod4_one :
    Filter.Tendsto (fun x : ℝ ↦ thetaClass 4 1 x / x) Filter.atTop (nhds (1 / 2)) := by
  have h := pnt_class (m := 4) (r := 1) isUnit_mod4_one
  have e : (Nat.totient 4 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rwa [e] at h

/-- P6: primes `≡ 1 (mod 6)` (density `1/2`). -/
theorem pnt_mod6_one :
    Filter.Tendsto (fun x : ℝ ↦ thetaClass 6 1 x / x) Filter.atTop (nhds (1 / 2)) := by
  have h := pnt_class (m := 6) (r := 1) isUnit_mod6_one
  have e : (Nat.totient 6 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 6 = 2 by decide]; norm_num
  rwa [e] at h

/-- Window for lambda (mod 4, class 3), rule `l ∣ q`. -/
theorem window_mod4_three_dvd {a b : ℝ} (ha : 0 < a) (hab : a + 2 < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod 4) = 3 ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ l ∣ q := by
  have := exists_prime_window (PrimeRule.ofDvd 4 3 isUnit_mod4_three)
    (PrimeRule.ofDvd_badBound _ _ _) ha (a := a) (b := b)
    (by simp [PrimeRule.ofDvd, show Nat.totient 4 = 2 by decide]; linarith)
  exact this

/-- Window for P6 (mod 6, class 1), rule `l² ∥ q`, weight `1/2`: needs `b > a + 1`. -/
theorem window_mod6_one_sq {a b : ℝ} (ha : 0 < a) (hab : a + 1 < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod 6) = 1 ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ (l ^ 2 ∣ q ∧ ¬ l ^ 3 ∣ q) := by
  have := exists_prime_window (PrimeRule.ofSqDvd 6 1 isUnit_mod6_one)
    (PrimeRule.ofSqDvd_badBound _ _ _) ha (a := a) (b := b)
    (by simp [PrimeRule.ofSqDvd, show Nat.totient 6 = 2 by decide]; linarith)
  exact this

end CatalanCore.NT

namespace CatalanCore

/-- `R.HasWindow` for `Bad l q := l ∣ q` (weight 1). -/
theorem PrimeRule.ofDvd_hasWindow (m : ℕ) (r : ZMod m) (hr : IsUnit r) [NeZero m] :
    (PrimeRule.ofDvd m r hr).HasWindow :=
  PrimeRule.hasWindow _ (PrimeRule.ofDvd_badBound m r hr)

/-- `R.HasWindow` for `Bad l q := l² ∣ q ∧ ¬ l³ ∣ q` (i.e. `v_l(q) = 2`; weight 1/2). -/
theorem PrimeRule.ofSqDvd_hasWindow (m : ℕ) (r : ZMod m) (hr : IsUnit r) [NeZero m] :
    (PrimeRule.ofSqDvd m r hr).HasWindow :=
  PrimeRule.hasWindow _ (PrimeRule.ofSqDvd_badBound m r hr)

end CatalanCore
