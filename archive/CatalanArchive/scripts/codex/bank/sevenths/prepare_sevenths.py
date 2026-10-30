from pathlib import Path
import sys

SRC = Path(r'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform/CatalanCore/Uniform/Bank/Fifths')
OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else SRC.parent / 'Sevenths'
OUT.mkdir(exist_ok=True)
for name in ('Geom', 'NV', 'Final'):
    s = (SRC / (name + '.lean')).read_text(encoding='utf-8')
    for a, b in [('Fifths', 'Sevenths'), ('fifths', 'sevenths'), ('F5', 'F7'),
                 ('Lam5', 'Lam7'), ('D5', 'D7'), ('c5', 'c7'),
                 ('two_ninths', 'one_sixth'), ('2 / 9', '1 / 6'),
                 ('11 / 9', '7 / 6'), ('10 / 9', '13 / 12'),
                 ('59983 / 2500', '70993 / 20'), ('-1 / 25', '-1 / 49'), ('-1/25', '-1/49'), ('-25', '-49')]:
        s = s.replace(a, b)
    if name == 'Final':
        start = s.index('/-!')
        end = s.index('namespace ', start)
        s = s[:start] + '/-! Conditional sevenths assembly on the new alternating family.\nThe content and decay suppliers remain explicit obligations. -/\n\n' + s[end:]
        s = s.replace('18614248183031951531578379 / 5321679222691225544230080 + (2 / 81)',
                      '8926987763346083870538925313134246938568387 / 2458710375447819602863559629392237970329600 + (1 / 72)')
        s = s.replace('4826561916291581150063627 / 1265625000000000000000000',
                      '2185487560184413390033 / 600000000000000000000')
        s = s.replace('2239239458955067 / 312500000000000', '7425954607455103 / 1000000000000000')
        s = s.replace('59983/2500', '70993/20')
    elif name == 'Geom':
        start = s.index('/-- The block geometry')
        end = s.index('noncomputable def', start)
        s = s[:start] + '/-- Alternating common-deletion geometry with border slope `1/12`. -/\n' + s[end:]
    (OUT / (name + '.lean')).write_text(s, encoding='utf-8')

s = (SRC / 'Frame.lean').read_text(encoding='utf-8')
s = s.replace('Fifths', 'Sevenths').replace('fifths', 'sevenths').replace('25', '49')
start = s.index('/-!')
end = s.index('namespace ', start)
s = s[:start] + '/-! The six seventh frames with the exact contour offsets from the hypotheses receipt. -/\n\n' + s[end:]
start = s.index('def sevenths1')
end = s.index('/-- The requested target', start)
s = s[:start] + '''def seventhNumerator (a : Fin 6) : ℕ := a.val + 1

def seventhsFrameAt (a : Fin 6) : Frame :=
  let s : ℚ := (seventhNumerator a : ℚ) / 7
  let xs : ℚ := if a.val < 3 then (1 + s) / 2 else s / 2
  let δ : ℚ := if a.val < 3 then (1 - s) / 2 else s / 2
  seventhsFrame s xs δ (if a.val < 3 then 1 else 0)
    (by dsimp [s, seventhNumerator]; positivity)
    (by
      have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt
      dsimp [s, seventhNumerator]
      push_cast
      linarith)

''' + s[end:]
s = s.replace('/ 5', '/ 7')
start = s.index('theorem sevenths1_const')
s = s[:start] + '''theorem seventhsFrameAt_const (a : Fin 6) :
    (seventhsFrameAt a).const = ((-1 / 49 : ℚ) : ℝ) * seventhsTarget (seventhNumerator a) := by
  have h0 : (0 : ℚ) < (seventhNumerator a : ℚ) / 7 := by
    dsimp [seventhNumerator]
    positivity
  have h1 : (seventhNumerator a : ℚ) / 7 < 1 := by
    have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt
    dsimp [seventhNumerator]
    push_cast
    linarith
  unfold seventhsFrameAt
  simpa [seventhsTarget, hurwitzTail2] using
    seventhsFrame_const ((seventhNumerator a : ℚ) / 7)
      (if a.val < 3 then (1 + (seventhNumerator a : ℚ) / 7) / 2 else ((seventhNumerator a : ℚ) / 7) / 2)
      (if a.val < 3 then (1 - (seventhNumerator a : ℚ) / 7) / 2 else ((seventhNumerator a : ℚ) / 7) / 2)
      (if a.val < 3 then 1 else 0) h0 h1

end CatalanCore.Uniform.Bank.Sevenths
'''
s = s.replace('end CatalanCore.Uniform.Bank.Sevenths', '\ntheorem sevenths_shift_pos (a : Fin 6) : (0 : ℚ) < (seventhNumerator a : ℚ) / 7 := by\n  dsimp [seventhNumerator]\n  positivity\n\ntheorem sevenths_shift_lt_one (a : Fin 6) : (seventhNumerator a : ℚ) / 7 < 1 := by\n  have ha : (a.val : ℚ) < 6 := by exact_mod_cast a.isLt\n  dsimp [seventhNumerator]\n  push_cast\n  linarith\n\ntheorem seventhsFrameAt_w_ne (a : Fin 6) (i : Fin (seventhsFrameAt a).d) :\n    (seventhsFrameAt a).w i ≠ 0 := by\n  rcases i with ⟨k, hk⟩\n  have hk2 : k < 2 := hk\n  interval_cases k\n  · exact (by decide : (-1 : ℤ) ≠ 0)\n  · exact (by decide : (1 : ℤ) ≠ 0)\n\n' + 'end CatalanCore.Uniform.Bank.Sevenths')
(OUT / 'Frame.lean').write_text(s, encoding='utf-8')
(OUT / 'Members.lean').write_text('''import CatalanCore.Uniform.Bank.Sevenths.Final
import CatalanCore.Uniform.Bank.Sevenths.Frame
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Uniform

/-- All six targets, conditional on the matched content and decay suppliers. -/
theorem sevenths_measure (a : Fin 6)
    (hS : HasScaledContent
      ((F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2)).restrictAdm
        (fun i => i.1 % 2 = 0)) F7.scale Lam7)
    (hD : HasScaledDecay
      (F7.family (seventhsFrameAt a) (F7.selectionDepth (seventhsFrameAt a) 2))
      F7.scale (D7 : ℝ) (c7 : ℝ)) :
    Measure.MeasureLBAt (seventhsTarget (seventhNumerator a)) ((70993 / 20 : ℚ) : ℝ) :=
  sevenths_measure_of_const (seventhsFrameAt a) (by show 1 ≤ 2; norm_num)
    (seventhsFrameAt_w_ne a) _ le_rfl (seventhsFrameAt_const a) hS hD

end CatalanCore.Uniform.Bank.Sevenths
''', encoding='utf-8')
(OUT / 'Audit.lean').write_text('''import CatalanCore.Uniform.Bank.Sevenths.Members
#print axioms CatalanCore.Uniform.Bank.Sevenths.Lam7_lt_D7
#print axioms CatalanCore.Uniform.Bank.Sevenths.sevenths_X_le
#print axioms CatalanCore.Uniform.Bank.Sevenths.F7_nv0
#print axioms CatalanCore.Uniform.Bank.Sevenths.F7_rowPieces
#print axioms CatalanCore.Uniform.Bank.Sevenths.F7_colPieces
#print axioms CatalanCore.Uniform.Bank.Sevenths.F7_totalMass
#print axioms CatalanCore.Uniform.Bank.Sevenths.sevenths_measureLB
#print axioms CatalanCore.Uniform.Bank.Sevenths.seventhsFrameAt_const
#print axioms CatalanCore.Uniform.Bank.Sevenths.sevenths_measure
''', encoding='utf-8')
