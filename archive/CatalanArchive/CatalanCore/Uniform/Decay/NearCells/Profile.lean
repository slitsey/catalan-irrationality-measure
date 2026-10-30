import CatalanCore.Uniform.Decay.NearCells.PilotData
set_option Elab.async false
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 20

namespace CatalanCore.Uniform.Decay.NearCells.Pilot
open CatalanCore.Uniform.Decay.SignedPilot CatalanCore.Uniform.Decay.Tools

def zcP : CQ := edge0Center (1/160) (11/1600)
def hP : ℚ := ((11/1600) - (1/160)) / 2
def p5 : WP := sevWP.getD 5 ⟨0, [], ⟨0,0⟩, ⟨0,0⟩, 0, 0⟩

-- one transcendental evaluation
theorem t_log : (evalInput (1, 3141592653589793238, 1000000000000000000, 1)).isSome = true := by decide +kernel
theorem t_atan : (evalInput (2, 3141592653589793238, 1000000000000000000, 0)).isSome = true := by decide +kernel
theorem t_logHalf : (logHalf ⟨123456789/1000000, 987654321/1000000⟩).isSome = true := by decide +kernel
theorem t_argEnc : (argEnc ⟨123456789/1000000, 987654321/1000000⟩).isSome = true := by decide +kernel
-- one piece
theorem t_piece : (pieceEval nPilot p5 zcP edge0Dir hP).isSome = true := by decide +kernel
-- the pieces without the transcendental part: just the CQ coefficient arithmetic
def z0P : CQ := z0of p5.A p5.B zcP
def eP' : CQ := eof p5.A p5.B edge0Dir
theorem t_coef : ((List.range nPilot).map (pieceCoef nPilot p5 z0P eP' ⟨1/3, 1/7⟩ ⟨1/5, 1/11⟩ (1/13))).length = 8 := by decide +kernel



def forced (o : Option (List ℚ × ℚ)) : Bool :=
  match o with
  | some (c, E) => decide (c.foldl (· + ·) 0 < 1000000000) && decide (E < 1)
  | none => false

theorem t_piece_forced5 : forced (pieceEval nPilot p5 zcP edge0Dir hP) = true := by decide +kernel
def p9 : WP := sevWP.getD 9 ⟨0, [], ⟨0,0⟩, ⟨0,0⟩, 0, 0⟩
theorem t_piece_forced9 : forced (pieceEval nPilot p9 zcP edge0Dir hP) = true := by decide +kernel
def p27 : WP := sevWP.getD 27 ⟨0, [], ⟨0,0⟩, ⟨0,0⟩, 0, 0⟩
theorem t_piece_forced27 : forced (pieceEval nPilot p27 zcP edge0Dir hP) = true := by decide +kernel
-- the pieces coefficients with trivial constants (isolates the CQ arithmetic from the enclosure values)
theorem t_coef_forced : decide (((List.range nPilot).map (pieceCoef nPilot p5 z0P eP' ⟨1/3, 1/7⟩ ⟨1/5, 1/11⟩ (1/13))).foldl (· + ·) 0 < 1000000000) = true := by decide +kernel
theorem t_log_forced : (match logHalf (CQ.sub p5.B p5.A) with | some (l, e) => decide (l < 100 ∧ e < 1) | none => false) = true := by decide +kernel


/-! List-based variant to test sharing. -/
def jetL (Pl : List CQ) (q : CQ) (m : ℕ) : CQ :=
  CQ.sumTo (fun j => CQ.smul (if j = m then 0 else -(1 / (((m - j : ℕ)) : ℚ)))
    (CQ.mul (Pl.getD j CQ.zero) (CQ.pow q (m - j)))) (m + 1)

def pieceCoefL (n : ℕ) (P : WP) (z0 e L0 L1 : CQ) (lv : ℚ) : List ℚ :=
  let a := coeffs P.a
  let d := P.a.length - 1
  let PBl := (List.range n).map (PBc a d z0 e)
  let PAl := (List.range n).map (fun m => CQ.sub (CQ.ofQ (if m = 0 then massQ a d else 0)) (PBl.getD m CQ.zero))
  let q0 := q0of z0 e
  let q1 := q1of z0 e
  (List.range n).map fun m =>
    (CQ.add (CQ.add (CQ.add (CQ.add (CQ.mul (PAl.getD m CQ.zero) L1) (CQ.mul (PBl.getD m CQ.zero) L0))
      (Rc a d z0 e m)) (jetL PAl q1 m)) (jetL PBl q0 m)).re
      + (if m = 0 then massQ a d * lv else 0)

theorem t_coefL_forced : decide ((pieceCoefL nPilot p5 z0P eP' ⟨1/3, 1/7⟩ ⟨1/5, 1/11⟩ (1/13)).foldl (· + ·) 0 < 1000000000) = true := by decide +kernel


def sumRe (l : List CQ) : ℚ := (l.map CQ.re).foldl (· + ·) 0
def aP := coeffs p5.a
def dP := p5.a.length - 1
theorem t_z0 : decide (z0P.re < 1000000000) = true := by decide +kernel
theorem t_PB : decide (sumRe ((List.range 8).map (PBc aP dP z0P eP')) < 1000000000) = true := by decide +kernel
theorem t_R : decide (sumRe ((List.range 8).map (Rc aP dP z0P eP')) < 1000000000) = true := by decide +kernel
theorem t_wq : decide (massQ aP dP < 1000000000) = true := by decide +kernel
theorem t_jet : decide (sumRe ((List.range 8).map (jetc (PAc aP dP z0P eP') (q1of z0P eP'))) < 1000000000) = true := by decide +kernel

end CatalanCore.Uniform.Decay.NearCells.Pilot
