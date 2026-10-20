module
public import CatalanFrames.P6Hybrid.MinorCorank.Rescue
public import CatalanFrames.P6Hybrid.MinorCorank.PhysicalRescue
public import CatalanFrames.P6Hybrid.WindowSquare
public import CatalanFrames.P6Hybrid.MinorSelect
@[expose] public section
open Finset Matrix Polynomial Module CatalanCore CatalanCore.Rect CatalanFrames.P6
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanFrames.LambdaHybrid.NV CatalanFrames.P6.NV
namespace CatalanFrames.P6Hybrid
variable {ell t : ℕ} [Fact ell.Prime]

/-- Every integral rational argument has a nonzero member after at most three low deletions. -/
theorem p6_minorNV_integral (hl : ell = 6*t+1) (ht : 1≤t)
    (r m : ℕ) (hm : 1≤m) (hKr : 2*t+1≤r) (htop : r+2*m≤3*t)
    {x : ℚ} (hx : x ∈ S ell) :
    ∃ s : Finset (Fin r), r-s.card≤3 ∧ (commonMinorPoly p6Frame r m s).eval x ≠ 0 := by
  let g := ell-r-2*m
  have hg : r+2*m+g=ell := by dsimp [g]; omega
  have H : BandGeometry ell (2*t+1) m (3*t+1) g :=
    ⟨Fact.out, by omega, by omega, by dsimp [g]; omega, by omega⟩
  have hn : 3≤2*t+1-m := by omega
  have hng : 2*t+1-m≤g := by dsimp [g]; omega
  have hGram := reflected_gram_ne (K := 2*t+1) hg
    (isUnit_iff_ne_zero.mp (hDelta_after (ℓ := ell) (2*t+1) m r
      (by omega) (by omega) hKr (by omega)))
  obtain ⟨d, hd, hdet⟩ := model_low_rescue H hn hng (two_ne hl ht)
    (cc ell t-36*red ell x) hGram
  apply p6_minor_integral_of_bordered hl ht r m hKr htop hx
  refine ⟨d, hd, ?_⟩
  exact physical_low_rescue hl ht r m hKr htop (red ell x) d hdet

/-- Square-regular nonvanishing for the bounded common-deletion family. -/
theorem p6_minorNV_square (hl : ell = 6*t+1) (ht : 1≤t)
    (r m : ℕ) (hm : 1≤m) (hKr : 2*t+1≤r) (htop : r+2*m≤3*t)
    {x : ℚ} (hx : ¬ell^2 ∣ x.den) :
    ∃ s : Finset (Fin r), r-s.card≤3 ∧ (commonMinorPoly p6Frame r m s).eval x ≠ 0 :=
  p6_minor_square_of_integral hl ht r m hm hKr htop
    (fun _ h => p6_minorNV_integral hl ht r m hm hKr htop h) hx

/-- The pinned arithmetic interface consumed by the measure theorem. -/
theorem p6_minor_hasNVPin :
    HasNVPinC (commonMinorFam p6Frame P6Adm9 3) P6Cls1 P6BadSquare (51/20) (59/20) := by
  apply hasNVPinC_commonMinor_of_regular p6Frame 3
    (fun _ h => h.mod6)
  intro ell hp hc t r m hl ht ha hm hKr htop p q hq hcop hbad
  haveI : Fact ell.Prime := ⟨hp⟩
  exact p6_minorNV_square hl ht r m hm hKr htop
    (not_pow_dvd_rat_den ell 2 p q hbad)
end CatalanFrames.P6Hybrid
#print axioms CatalanFrames.P6Hybrid.p6_minorNV_square
#print axioms CatalanFrames.P6Hybrid.p6_minor_hasNVPin
