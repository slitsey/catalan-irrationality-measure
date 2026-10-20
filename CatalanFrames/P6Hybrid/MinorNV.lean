module
public import CatalanFrames.P6Hybrid.MinorReduce
public import CatalanFrames.P6Hybrid.ValOne
public import CatalanCore.Basic.ValOneDen
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Rect CatalanFrames.P6
open CatalanFrames.LambdaHybrid.NV
namespace CatalanFrames.P6Hybrid
variable {ℓ t : ℕ} [Fact ℓ.Prime]

lemma after_low (r m : ℕ) (hKr : 2 * t + 1 ≤ r) :
    ∀ n, n < 2 * t + 1 → n ∈ (after r m).C := by
  intro n hn
  change n ∈ Finset.range r
  exact mem_range.mpr (by omega)

lemma after_lt (r m : ℕ) (htop : r + 2 * m ≤ 3 * t) :
    ∀ n, n ∈ (after r m).C ∨ n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → n < 3 * t + 1 := by
  intro n hn
  rcases hn with hc | hxy
  · have h := mem_range.mp hc
    omega
  · have h := (memXY r m n).mp hxy
    omega

lemma after_hi (r m : ℕ) (hKr : 2 * t + 1 ≤ r) :
    ∀ n, n ∈ (after r m).X' ∨ n ∈ (after r m).Y' → 2 * t + 1 ≤ n := by
  intro n hn
  have h := (memXY r m n).mp hn
  omega

def absentNodes (r m t : ℕ) (i : Fin (3 * t + 1 - (r + 2 * m))) : ℕ := r + 2 * m + i

lemma absentNodes_injective (r m t : ℕ) : Function.Injective (absentNodes r m t) := by
  intro i j h
  apply Fin.ext
  dsimp [absentNodes] at h
  omega

lemma absentNodes_range (r m : ℕ) (hKr : 2 * t + 1 ≤ r) (htop : r + 2 * m ≤ 3 * t) :
    ∀ n, (∃ i, absentNodes r m t i = n) ↔
      n ∈ absS (2 * t + 1) (3 * t + 1) (after r m).C (after r m).X' (after r m).Y' := by
  intro n
  have hxy := memXY r m n
  simp only [absS, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨i, rfl⟩
    have hi := i.2
    dsimp [absentNodes]
    refine ⟨⟨by omega, by omega⟩, ?_, ?_, ?_⟩
    · change ¬ _ ∈ Finset.range r
      simp only [mem_range]
      omega
    · intro hx
      have h := hxy.mp (Or.inl hx)
      dsimp [absentNodes] at h
      omega
    · intro hy
      have h := hxy.mp (Or.inr hy)
      dsimp [absentNodes] at h
      omega
  · rintro ⟨⟨hK, hT⟩, hc, hx, hy⟩
    have hnr : r ≤ n := by
      have hh : ¬ n < r := fun h => hc (mem_range.mpr h)
      omega
    have hnb : r + 2 * m ≤ n := by
      by_contra h
      rcases hxy.mpr ⟨hnr, by omega⟩ with h | h <;> contradiction
    exact ⟨⟨n - (r + 2 * m), by omega⟩, by dsimp [absentNodes]; omega⟩

noncomputable def minorGram (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) (r m : ℕ) :
    Matrix (Fin (2 * t + 1)) (Fin (2 * t + 1)) (ZMod ℓ) :=
  Gcols ℓ (2 * t + 1) (absentNodes r m t) *
    (Gcols ℓ (2 * t + 1) (absentNodes r m t)).transpose +
    ((p6Data3 hl ht).τ₀ / (p6Data3 hl ht).κ) • Ttop ℓ (2 * t + 1) (3 * t + 1)

/-- Once a reduced low principal minor is nonzero, the corresponding family member is nonzero. -/
theorem p6_minor_integral_of_bordered (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
    (r m : ℕ) (hKr : 2 * t + 1 ≤ r) (htop : r + 2 * m ≤ 3 * t)
    {x : ℚ} (hx : x ∈ S ℓ)
    (hNV : ∃ d : Finset (Fin (2 * t + 1)), d.card ≤ 3 ∧
      ((borderedN ((p6Data3 hl ht).h + red ℓ x / (p6Data3 hl ht).κ)
        (minorGram hl ht r m) (WX ℓ (2 * t + 1) (after r m))
        (WY ℓ (2 * t + 1) (after r m))).submatrix
          (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2 * t + 1)) id)
          (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2 * t + 1)) id)).det ≠ 0) :
    ∃ s : Finset (Fin r), r - s.card ≤ 3 ∧ (commonMinorPoly p6Frame r m s).eval x ≠ 0 := by
  obtain ⟨d, hd, hdet⟩ := hNV
  apply exists_commonMinor_of_after_low p6Frame r m (2 * t + 1) 3 hKr d hd x
  intro hzero
  apply hdet
  exact reduction_G3_low (p6Data3 hl ht) (after r m) (after_low r m hKr)
    (after_lt r m htop) (after_hi r m hKr) (absentNodes r m t)
    (absentNodes_injective r m t) (absentNodes_range r m hKr htop)
    Subtype.val Subtype.val_injective hx hzero
/-- The undeleted member handles every denominator of valuation one. -/
theorem p6_minor_valOne (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
    (r m : ℕ) (hm : 1 ≤ m) (hKr : 2 * t + 1 ≤ r) (htop : r + 2 * m ≤ 3 * t)
    {x : ℚ} (hdiv : ℓ ∣ x.den) (hsq : ¬ ℓ ^ 2 ∣ x.den) :
    ∃ s : Finset (Fin r), r - s.card ≤ 3 ∧ (commonMinorPoly p6Frame r m s).eval x ≠ 0 := by
  obtain ⟨u, hu, hg⟩ := good_mul_of_den_dvd_not_sq x hdiv hsq
  apply exists_commonMinor_of_after p6Frame r m 3 x
  apply p6_full_valOne_ne hl ht (after r m) (after_low r m hKr)
    (after_lt r m htop) (after_hi r m hKr)
  · exact isUnit_iff_ne_zero.mp (hDelta_after (ℓ := ℓ) (2 * t + 1) m r
      (by omega) (by omega) hKr (by omega))
  · exact hg
  · exact hu

/-- Integral nonvanishing is the only new gate for the square-regular family. -/
theorem p6_minor_square_of_integral (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
    (r m : ℕ) (hm : 1 ≤ m) (hKr : 2 * t + 1 ≤ r) (htop : r + 2 * m ≤ 3 * t)
    (hIntegral : ∀ x : ℚ, x ∈ S ℓ → ∃ s : Finset (Fin r), r - s.card ≤ 3 ∧
      (commonMinorPoly p6Frame r m s).eval x ≠ 0)
    {x : ℚ} (hsq : ¬ ℓ ^ 2 ∣ x.den) :
    ∃ s : Finset (Fin r), r - s.card ≤ 3 ∧ (commonMinorPoly p6Frame r m s).eval x ≠ 0 := by
  by_cases hdiv : ℓ ∣ x.den
  · exact p6_minor_valOne hl ht r m hm hKr htop hdiv hsq
  · exact hIntegral x hdiv
end CatalanFrames.P6Hybrid
#print axioms CatalanFrames.P6Hybrid.p6_minor_integral_of_bordered

#print axioms CatalanFrames.P6Hybrid.p6_minor_square_of_integral
