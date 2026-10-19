module

public import CatalanCore.Measure.Exponent

@[expose] public section

/-!
# Pinned-degree measure deduction (the `κ = 0` exponent `c/η`)

`HasNVPin Fam R α β`: for every prime `l` in the class and every (real) target degree `N ≥ N₁`
with `α N ≤ l ≤ β N`, some admissible member of degree in `[N, N + C]` does not vanish at `p/q`.
Because the degree is pinned to `N` independently of the position of `l` in `[αN, βN]`, the
exponent is `c/η` provided the prime window fits: `s η < β - α`.
Same proof as `measure_of_family_real`, with target `N = k log q`.
-/

namespace CatalanCore

/-- Generic pinned NV (G3): class predicate `Cls` and badness `Bad` abstracted. -/
def HasNVPinC (Fam : PolyFamily) (Cls : ℕ → Prop) (Bad : ℕ → ℕ → Prop) (α β : ℝ) : Prop :=
  ∃ (C : ℝ) (N₁ : ℝ), ∀ l : ℕ, l.Prime → Cls l →
    ∀ N : ℝ, N₁ ≤ N → α * N ≤ l → (l : ℝ) ≤ β * N →
    ∀ (p q : ℤ), 0 < q → IsCoprime p q → ¬ Bad l q.natAbs →
      ∃ n, Fam.Adm n ∧ N ≤ (Fam.deg n : ℝ) ∧ (Fam.deg n : ℝ) ≤ N + C ∧
        Fam.evalQ n (p / q) ≠ 0

def HasNVPin (Fam : PolyFamily) (R : PrimeRule) (α β : ℝ) : Prop :=
  HasNVPinC Fam (fun l => (l : ZMod R.m) = R.r) R.Bad α β

namespace Measure

open Real

theorem measure_of_family_pin_realC (Fam : PolyFamily) {Λ D c α β s : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} (hα : 0 < α) (hαβ : α < β)
    (hsη : s * (D - Λ) < β - α)
    (hNV : HasNVPinC Fam Cls Bad α β) (hwin : HasWindowC Cls Bad s) {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(c / (D - Λ) + e)) < |Fam.const - (p : ℝ) / q| := by
  set η : ℝ := D - Λ with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hβα : 0 < β - α := by linarith
  set M : ℝ := c / η with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  set δ : ℝ := e / (2 * M) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  set k : ℝ := (1 + δ) / η with hk
  have hk0 : 0 < k := by rw [hk]; positivity
  have hkη : 1 / η ≤ k := by rw [hk]; gcongr; linarith
  set a : ℝ := α * k with ha
  set b : ℝ := β * k with hb
  have ha0 : 0 < a := by positivity
  have hab : a + s < b := by
    have h1 : s < (β - α) * (1 / η) := by
      rw [mul_one_div, lt_div_iff₀ hη0]; exact hsη
    have h2 : (β - α) * (1 / η) ≤ (β - α) * k := mul_le_mul_of_nonneg_left hkη hβα.le
    rw [ha, hb]; nlinarith
  have hck : c * k = M + e / 2 := by
    have h1 : M * δ = e / 2 := by rw [hδ]; field_simp
    have h2 : c * k = M * (1 + δ) := by rw [hk, hM]; field_simp
    rw [h2]; linarith
  set θ : ℝ := η * (1 + δ / 2) / (1 + δ) with hθ
  have hθ0 : 0 < θ := by rw [hθ]; positivity
  have hθη : θ < η := by
    rw [hθ, div_lt_iff₀ (by positivity)]; nlinarith
  have hθk : θ * k = 1 + δ / 2 := by rw [hθ, hk]; field_simp
  obtain ⟨N₀, HS⟩ := sep_core Fam hΛ hD hθ0 hθη
  obtain ⟨q₁, hq₁⟩ := hwin a b ha0 hab
  obtain ⟨C, N₁, HNV⟩ := hNV
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hCC' : C ≤ C' := le_max_left _ _
  set L₁ : ℝ := max (max (N₁ / k) (N₀ / k)) (max (1 / k) (2 * c * C' / e)) with hL₁
  refine ⟨max q₁ ⌈Real.exp L₁⌉₊, fun p q hq hcop => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hqe : Real.exp L₁ ≤ q :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right _ _) hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : L₁ ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  set L := Real.log q with hLdef
  by_contra hcon
  push Not at hcon
  obtain ⟨l, hlp, hlr, hl1, hl2, hbad⟩ := hq₁ q hq1
  have hN1 : N₁ ≤ k * L := by
    have : N₁ / k ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
    rw [div_le_iff₀ hk0] at this; linarith
  have hN0 : N₀ ≤ k * L := by
    have : N₀ / k ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
    rw [div_le_iff₀ hk0] at this; linarith
  have hL1 : 1 ≤ k * L := by
    have : 1 / k ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
    rw [div_le_iff₀ hk0] at this; linarith
  obtain ⟨n, hAdm, hn1, hn2, hQ⟩ := HNV l hlp hlr (k * L) hN1
    (by rw [ha] at hl1; nlinarith) (by rw [hb] at hl2; nlinarith) (p : ℤ) (q : ℤ)
    (by exact_mod_cast hq0) hcop (by simpa using hbad)
  have hdeg' : N₀ ≤ Fam.deg n := by
    have : (N₀ : ℝ) ≤ Fam.deg n := le_trans hN0 hn1
    exact_mod_cast this
  have hclose : |Fam.const - (p : ℝ) / q| ≤ Real.exp (-c * Fam.deg n) := by
    refine le_trans hcon ?_
    rw [Real.rpow_def_of_pos hqpos, ← hLdef]
    apply Real.exp_le_exp.2
    have hLe : 2 * c * C' / e ≤ L := le_trans (le_max_right _ _) hL |>.trans' (le_max_right _ _)
    have h3 : c * C' ≤ e / 2 * L := by
      rw [div_le_iff₀ he] at hLe; nlinarith
    have h5 : c * (Fam.deg n : ℝ) ≤ c * (k * L) + c * C' := by
      have h6 : (Fam.deg n : ℝ) ≤ k * L + C' := by linarith
      have := mul_le_mul_of_nonneg_left h6 hc.le
      rw [mul_add] at this; exact this
    have h6 : c * (k * L) = (M + e / 2) * L := by rw [← hck]; ring
    linarith
  have key := HS n hAdm hdeg' p (q : ℤ) (by exact_mod_cast hq0) (by simpa using hQ)
    (by simpa using hclose)
  simp only [Int.cast_natCast] at key
  have hfin : θ * (k * L) ≤ θ * Fam.deg n := mul_le_mul_of_nonneg_left hn1 hθ0.le
  have : θ * (k * L) = (1 + δ / 2) * L := by rw [← mul_assoc, hθk]
  have hLpos : 0 < L := by
    have : 0 < k * L := by linarith
    exact pos_of_mul_pos_right this hk0.le
  have h8 : (1 + δ / 2) * L ≤ L := by rw [← this]; exact le_trans hfin key
  have h9 := mul_pos hδ0 hLpos
  linarith

theorem measure_of_family_pin_real (Fam : PolyFamily) {Λ D c α β : ℝ}
    (hΛ : HasContent Fam Λ) (hD : HasDecay Fam D c) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hα : 0 < α) (hαβ : α < β) (hsη : (R.s : ℝ) * (D - Λ) < β - α)
    (hNV : HasNVPin Fam R α β) (hwin : R.HasWindow) {e : ℝ} (he : 0 < e) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(c / (D - Λ) + e)) < |Fam.const - (p : ℝ) / q| :=
  measure_of_family_pin_realC Fam hΛ hD hη hc hα hαβ hsη hNV (PrimeRule.hasWindowC R hwin) he

theorem measure_of_family_pin_leC (Fam : PolyFamily) {c Λ D α β s E' : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    {Cls : ℕ → Prop} {Bad : ℕ → ℕ → Prop} (hα : 0 < α) (hαβ : α < β) (hsη : s * (D - Λ) < β - α)
    (hNV : HasNVPinC Fam Cls Bad (α : ℝ) (β : ℝ)) (hwin : HasWindowC Cls Bad (s : ℝ))
    (hE : c / (D - Λ) ≤ E') : Fam.MeasureLB (E' : ℝ) := by
  intro e he
  obtain ⟨q₀, H⟩ := measure_of_family_pin_realC Fam hΛ hD (by exact_mod_cast hη)
    (by exact_mod_cast hc) (by exact_mod_cast hα) (by exact_mod_cast hαβ) (by exact_mod_cast hsη)
    hNV hwin he
  refine ⟨max q₀ 1, fun p q hq hcop => ?_⟩
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_right _ _) hq
  have h := H p q (le_trans (le_max_left _ _) hq) hcop
  refine lt_of_le_of_lt ?_ h
  apply Real.rpow_le_rpow_of_exponent_le hq1
  have : ((c / (D - Λ) : ℚ) : ℝ) ≤ (E' : ℝ) := by exact_mod_cast hE
  push_cast at this
  linarith

theorem measure_of_family_pin_le (Fam : PolyFamily) {c Λ D α β E' : ℚ}
    (hΛ : HasContent Fam (Λ : ℝ)) (hD : HasDecay Fam (D : ℝ) (c : ℝ)) (hη : Λ < D) (hc : 0 < c)
    (R : PrimeRule) (hα : 0 < α) (hαβ : α < β) (hsη : R.s * (D - Λ) < β - α)
    (hNV : HasNVPin Fam R (α : ℝ) (β : ℝ)) (hwin : R.HasWindow) (hE : c / (D - Λ) ≤ E') :
    Fam.MeasureLB (E' : ℝ) :=
  measure_of_family_pin_leC Fam hΛ hD hη hc hα hαβ hsη hNV (PrimeRule.hasWindowC R hwin) hE

end Measure
end CatalanCore
