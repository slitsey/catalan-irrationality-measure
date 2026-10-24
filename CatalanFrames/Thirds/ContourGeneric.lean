module

public import CatalanFrames.Thirds.Frame
public import CatalanCore.Decay.Integ
public import CatalanCore.Decay.RayBound

@[expose] public section

/-! # Contour and decay hypotheses for the thirds frames, generic in `s`, `xs`, `δ0`, `n0off`, slope

`DecayOKs' sl` for `thirdsFrame s N xs δ0 n0off`, from explicit gap witnesses
(`CatalanCore.Decay.gap_aux`) for the two poles `μ = s` and `μ = 1`, the atom-range
inequalities and `1 ≤ 4 · sl · δ0`.  The certificate (`CertCoreGs sl ..`) never sees `xs` or
`n0off`: they enter only through this hypothesis structure.
-/

open CatalanCore

namespace CatalanFrames.Thirds

variable (s N xs δ0 : ℚ) (n0off : ℕ) (hs0 : 0 < s) (hs1 : s < 1) (hN : 0 < N)

theorem thirds_contourOK (hxs : 0 < xs) (hd0 : 0 < δ0) (k1 k2 : ℤ)
    (h1 : δ0 ≤ s - xs + k1) (h1' : s - xs + k1 - 1 ≤ -δ0)
    (h2 : δ0 ≤ 1 - xs + k2) (h2' : 1 - xs + k2 - 1 ≤ -δ0) :
    (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).ContourOK where
  xs_pos := hxs
  gap := by
    refine ⟨hd0, fun i n => ?_⟩
    fin_cases i
    · exact Decay.gap_aux s xs δ0 k1 h1 h1' n
    · exact Decay.gap_aux 1 xs δ0 k2 h2 h2' n

theorem thirds_decayOKs' (hxs : 0 < xs) (hd0 : 0 < δ0) (k1 k2 : ℤ)
    (h1 : δ0 ≤ s - xs + k1) (h1' : s - xs + k1 - 1 ≤ -δ0)
    (h2 : δ0 ≤ 1 - xs + k2) (h2' : 1 - xs + k2 - 1 ≤ -δ0)
    (sl : ℝ) (hsl : 1 ≤ sl) (hcot : 1 ≤ 4 * sl * (δ0 : ℝ))
    (hat1 : ((⌊xs - s⌋ : ℤ) : ℚ) + s ≤ n0off) (hat2 : ((⌊xs - 1⌋ : ℤ) : ℚ) + 1 ≤ n0off)
    (hN1 : 1 ≤ N) :
    (thirdsFrame s N xs δ0 n0off hs0 hs1 hN).DecayOKs' sl where
  contour := thirds_contourOK s N xs δ0 n0off hs0 hs1 hN hxs hd0 k1 k2 h1 h1' h2 h2'
  slope := ⟨by linarith, hsl, hcot⟩
  atomRange := by
    intro i
    fin_cases i
    · exact hat1
    · exact hat2
  norm_ge := hN1

end CatalanFrames.Thirds
