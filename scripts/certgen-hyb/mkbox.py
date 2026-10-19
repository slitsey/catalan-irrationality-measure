# Generate CatalanCore/Cert/SigmaHyb/UBox.lean: Utau upper bound over a box, copied from the legacy box_sound_g proof (hA,hB,hC).
src = open('CatalanLambda/Cert/RayBox.lean', encoding='utf-8').read().split('\n')
# lines are 1-indexed in grep; body from 'have hxhiR' (line 178) to before '-- (D)' (line 327)
i0 = next(i for i, l in enumerate(src) if l.startswith('  have hxhiR'))
i1 = next(i for i, l in enumerate(src) if l.startswith('  -- (D)'))
body = '\n'.join(src[i0:i1])
hdr = '''module

public import CatalanLambda.Cert.RayBox

@[expose] public section

/-!
# Upper bound of `Utau x y` over a box (`xhi < 0`, `0 ≤ ylo`), no `π` term

Extracted from the legacy `box_sound_g` proof (pieces (A), (B), (C)); `UbUp = 1 + Aup + Bup + Cup`.
-/

open Real

namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def UbUp (xlo xhi ylo yhi : ℤ) : ℚ :=
  let L1 := L1Q xlo yhi
  let Aup : ℚ := (1 / 2) * qmax ((-(xhi : ℚ) / 2 ^ 40) * L1) ((-(xlo : ℚ) / 2 ^ 40) * L1)
  let l := lQ xhi ylo
  let Bup : ℚ := -(1 / 2) * qmin ((((2 : ℚ) ^ 40 - xhi) / 2 ^ 40) * l)
    ((((2 : ℚ) ^ 40 - xlo) / 2 ^ 40) * l)
  let th := thetaQ (vloQ xlo ylo yhi)
  let Cup : ℚ := -qmin ((ylo : ℚ) / 2 ^ 40 * th) ((yhi : ℚ) / 2 ^ 40 * th)
  1 + Aup + Bup + Cup

theorem utau_box_le (xlo xhi ylo yhi : ℤ)
    (hxhi : xhi < 0) (hxlohi : xlo ≤ xhi) (hylo : 0 ≤ ylo)
    (x y : ℝ)
    (hx1 : (xlo : ℝ) / 2 ^ 40 ≤ x) (hx2 : x ≤ (xhi : ℝ) / 2 ^ 40)
    (hy1 : (ylo : ℝ) / 2 ^ 40 ≤ y) (hy2 : y ≤ (yhi : ℝ) / 2 ^ 40) :
    CatalanLambda.Cert.Utau x y ≤ ((UbUp xlo xhi ylo yhi : ℚ) : ℝ) := by
'''
tail = '''  unfold CatalanLambda.Cert.Utau
  simp only [UbUp]
  have hA' := hA
  have hC' := hC
  push_cast at hA' hC' ⊢
  have hBc : -(1 / 2 : ℝ) * min (((2 ^ 40 - (xhi : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ))
        (((2 ^ 40 - (xlo : ℝ)) / 2 ^ 40) * (lQ xhi ylo : ℝ)) ≥
      -((1 - x) * (Real.log ((1 - x) ^ 2 + y ^ 2) / 2)) := hB
  linarith [hA', hBc, hC']

end CatalanCore.Cert.SigmaHyb
'''
open('CatalanCore/Cert/SigmaHyb/UBox.lean', 'w', encoding='utf-8', newline='\n').write(hdr + body + '\n' + tail)
