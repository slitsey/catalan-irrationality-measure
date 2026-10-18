module

public import CatalanCore.Measure.Sep
public import Mathlib.NumberTheory.LSeries.PrimesInAP

@[expose] public section

/-!
# Irrationality of the constant of a polynomial family

Generic form of `CatalanLambda.Measure.lambda_irrational`.  For a fixed rational `p/q` we need
arbitrarily large primes `l` in the class with `¬ Bad l q` (Dirichlet; `Bad l q` fails for all
large `l`, hypothesis `hbad`), then `HasNV` gives a member and `sep_core` a contradiction.
-/

namespace CatalanCore.Measure

theorem irrational_of_family (Fam : PolyFamily) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D)
    (R : PrimeRule) (hm : R.m ≠ 0) (hg : 0 < g₁)
    (hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ R.Bad l q)
    (hNV : HasNV Fam R g₁ g₂) : Irrational Fam.const := by
  rintro ⟨r, hr⟩
  have : NeZero R.m := ⟨hm⟩
  set θ : ℝ := (D - Λ) / 2 with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  obtain ⟨N₀, HS⟩ := sep_core Fam hΛ hD hθ0 (by rw [hθ]; linarith)
  obtain ⟨C, l₀, HNV⟩ := hNV
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  have hqpos : 0 < r.den := r.den_pos
  obtain ⟨Nb, hNb⟩ := hbad r.den hqpos
  have hlog0 : 0 ≤ Real.log (r.den : ℝ) := Real.log_nonneg (by exact_mod_cast hqpos)
  obtain ⟨N, hN⟩ := exists_nat_gt (((N₀ : ℝ) + C' + Real.log (r.den : ℝ) / θ + C') / g₁)
  obtain ⟨l, hlN, hlp, hlr⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := R.m) (a := R.r) R.hr
    (max (max l₀ Nb) N)
  have hl0 : l₀ ≤ l := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlN.le
  have hlb : Nb < l := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hlN
  have hlN' : N < l := lt_of_le_of_lt (le_max_right _ _) hlN
  have hlR : (N : ℝ) < l := by exact_mod_cast hlN'
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact r.reduced
  have hrq : (((r.num : ℤ) : ℚ) / (((r.den : ℕ) : ℤ) : ℚ)) = r := by
    push_cast; exact Rat.num_div_den r
  obtain ⟨n, hAdm, hn1, hn2, hQ⟩ := HNV l hlp hl0 hlr r.num (r.den : ℤ) (by exact_mod_cast hqpos)
    hcop (by simpa using hNb l hlb)
  have hgN : (N₀ : ℝ) + C' + Real.log (r.den : ℝ) / θ + C' < g₁ * N := by
    rw [div_lt_iff₀ hg] at hN; linarith
  have hgl : g₁ * N < g₁ * l := mul_lt_mul_of_pos_left hlR hg
  have hdeg : g₁ * l - C' ≤ Fam.deg n := by linarith
  have hdegN : N₀ ≤ Fam.deg n := by
    have : (N₀ : ℝ) ≤ Fam.deg n := by
      have : 0 ≤ Real.log (r.den : ℝ) / θ := by positivity
      linarith
    exact_mod_cast this
  have hclose : |Fam.const - ((r.num : ℤ) : ℝ) / (((r.den : ℕ) : ℤ) : ℝ)| ≤
      Real.exp (-c * Fam.deg n) := by
    have : ((r.num : ℤ) : ℝ) / (((r.den : ℕ) : ℤ) : ℝ) = Fam.const := by
      rw [← hr]; push_cast; exact (Rat.cast_def r).symm
    rw [this]; simp [(Real.exp_pos _).le]
  have key := HS n hAdm hdegN r.num (r.den : ℤ) (by exact_mod_cast hqpos) hQ hclose
  simp only [Int.cast_natCast] at key
  have h1 : Real.log (r.den : ℝ) / θ < Fam.deg n := by linarith
  rw [div_lt_iff₀ hθ0] at h1
  linarith

theorem irrational_of_frame (Fr : Frame) {Λ D c g₁ g₂ : ℝ}
    (hΛ : HasContent (PolyFamily.ofFrame Fr) Λ) (hD : HasDecay (PolyFamily.ofFrame Fr) D c)
    (hη : Λ < D) (R : PrimeRule) (hm : R.m ≠ 0) (hg : 0 < g₁)
    (hbad : ∀ q : ℕ, 0 < q → ∃ N : ℕ, ∀ l : ℕ, N < l → ¬ R.Bad l q)
    (hNV : HasNV (PolyFamily.ofFrame Fr) R g₁ g₂) : Irrational Fr.const :=
  irrational_of_family _ hΛ hD hη R hm hg hbad hNV

end CatalanCore.Measure
