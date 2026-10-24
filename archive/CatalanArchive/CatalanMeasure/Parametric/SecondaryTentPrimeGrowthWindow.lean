module
public import CatalanArchive.CatalanMeasure.Parametric.SecondaryTentPrimeGrowth
@[expose] public section
namespace CatalanMeasure.Parametric
open Filter
open scoped BigOperators
noncomputable section

theorem secondaryTentExponent_zero_left {N p : ℕ} (hp : 9*p ≤ 52*N) :
    secondaryTentExponent N p = 0 := by
  have hr : ((9:ℝ)*p-52*N)/2 ≤ 0 := by
    have h : (9:ℝ)*p ≤ 52*N := by exact_mod_cast hp
    linarith
  have hf : (⌊((9:ℝ)*p-52*N)/2⌋ : ℤ) ≤ 0 := by
    simpa using Int.floor_mono hr
  unfold secondaryTentExponent
  rw [max_eq_left ((min_le_left _ _).trans hf)]
  rfl

theorem secondaryTentExponent_zero_right {N p : ℕ} (hp : 44*N ≤ 7*p) :
    secondaryTentExponent N p = 0 := by
  have hr : ((44:ℝ)*N-7*p)/2 ≤ 0 := by
    have h : (44:ℝ)*N ≤ 7*p := by exact_mod_cast hp
    linarith
  have hf : (⌊((44:ℝ)*N-7*p)/2⌋ : ℤ) ≤ 0 := by
    simpa using Int.floor_mono hr
  unfold secondaryTentExponent
  rw [max_eq_left ((min_le_right _ _).trans hf)]
  rfl

theorem secondaryTentExponent_support {N p : ℕ}
    (hp : secondaryTentExponent N p ≠ 0) :
    52*N < 9*p ∧ 7*p < 44*N := by
  constructor
  · by_contra h
    exact hp (secondaryTentExponent_zero_left (by omega))
  · by_contra h
    exact hp (secondaryTentExponent_zero_right (by omega))

def secondaryTentPrimeWindow (N : ℕ) : Finset ℕ :=
  (Finset.Ioc 0 (7*N)).filter (fun p => p.Prime ∧ 52*N < 9*p ∧ 7*p < 44*N)

/-- The encompassing product is exactly the product in the strict audited window. -/
theorem secondaryTentContent_eq_window {N : ℕ} (hN : 0 < N) :
    secondaryTentContent N =
      ∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p := by
  unfold secondaryTentContent
  symm
  apply Finset.prod_subset
  · intro p hp
    simp only [secondaryTentPrimeWindow, secondaryTentPrimes,
      Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    exact ⟨⟨by omega, hp.1.2⟩, hp.2.1⟩
  · intro p hp hn
    by_cases he : secondaryTentExponent N p = 0
    · simp [he]
    have hs := secondaryTentExponent_support he
    apply False.elim
    apply hn
    simp only [secondaryTentPrimeWindow, Finset.mem_filter, Finset.mem_Ioc]
    simp only [secondaryTentPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    exact ⟨⟨by omega, hp.1.2⟩, hp.2, hs⟩

theorem secondaryTentPrimeWindow_eventual_growth {c : ℝ} (hc : c < 16/63) :
    ∀ᶠ N : ℕ in atTop, c*(N:ℝ)^2 ≤
      Real.log (∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p : ℕ) := by
  filter_upwards [secondaryTentContent_eventual_growth hc,
    eventually_gt_atTop (0:ℕ)] with N hbound hN
  rw [← secondaryTentContent_eq_window hN]
  exact hbound

theorem secondaryTentPrimeWindow_eventual_507_2000 :
    ∀ᶠ N : ℕ in atTop, (507/2000:ℝ)*(N:ℝ)^2 ≤
      Real.log (∏ p ∈ secondaryTentPrimeWindow N, p ^ secondaryTentExponent N p : ℕ) :=
  secondaryTentPrimeWindow_eventual_growth (by norm_num)

theorem secondaryTentPrimeWindow_above_twoN {N p : ℕ}
    (hp : p ∈ secondaryTentPrimeWindow N) : 2*N < p := by
  simp only [secondaryTentPrimeWindow, Finset.mem_filter, Finset.mem_Ioc] at hp
  omega

/-- Any fixed nonzero exceptional integer is avoided once N is at least that integer. -/
theorem secondaryTentPrimeWindow_avoids_fixed {B N p : ℕ}
    (hB : 0 < B) (hN : B ≤ N) (hp : p ∈ secondaryTentPrimeWindow N) : ¬ p ∣ B := by
  intro hd
  have hpN := secondaryTentPrimeWindow_above_twoN hp
  have hpB := Nat.le_of_dvd hB hd
  omega

theorem secondaryTentExponent_eq_int_div (N p : ℕ) :
    secondaryTentExponent N p =
      (max 0 (min (((9:ℤ)*p-52*N)/2) (((44:ℤ)*N-7*p)/2))).toNat := by
  have ha : (⌊((9:ℝ)*p-52*N)/2⌋ : ℤ) = ((9:ℤ)*p-52*N)/2 := by
    have hh := Int.floor_div_natCast ((((9:ℤ)*p-52*N:ℤ):ℝ)) 2
    norm_num only [Int.floor_intCast] at hh
    convert hh using 1 <;> push_cast <;> ring
  have hb : (⌊((44:ℝ)*N-7*p)/2⌋ : ℤ) = ((44:ℤ)*N-7*p)/2 := by
    have hh := Int.floor_div_natCast ((((44:ℤ)*N-7*p:ℤ):ℝ)) 2
    norm_num only [Int.floor_intCast] at hh
    convert hh using 1 <;> push_cast <;> ring
  unfold secondaryTentExponent
  rw [ha, hb]

theorem secondaryTentExponent_positive_side {N p delta : ℕ}
    (hp : p = 6*N+delta) :
    secondaryTentExponent N p = N-(7*delta+1)/2 := by
  rw [secondaryTentExponent_eq_int_div]
  omega

theorem secondaryTentExponent_negative_side {N p d : ℕ}
    (hp : p+d = 6*N) :
    secondaryTentExponent N p = N-(9*d+1)/2 := by
  rw [secondaryTentExponent_eq_int_div]
  omega

end
end CatalanMeasure.Parametric
