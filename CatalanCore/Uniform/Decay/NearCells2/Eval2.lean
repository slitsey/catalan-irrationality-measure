import CatalanCore.Uniform.Decay.NearCells2.Defs
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools

/-- Like `pieceEval`, but the two jet remainders are returned as terms instead of norm bounds. -/
def pieceEval2 (n : ℕ) (P : WP) (zc dd : CQ) (h : ℚ) : Option (List ℚ × ℚ × List Tm) :=
  if decide (P.a.length - 1 + 2 ≤ n) && decide ((CQ.sub P.B P.A).nsq ≠ 0) &&
      sideOk3 (z0of P.A P.B zc) (eof P.A P.B dd) h &&
      decide ((z0of P.A P.B zc).nsq ≠ 0) &&
      decide ((CQ.sub CQ.one (z0of P.A P.B zc)).nsq ≠ 0) &&
      decide (sqrtUp ((q0of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (sqrtUp ((q1of (z0of P.A P.B zc) (eof P.A P.B dd)).nsq * h ^ 2) < 1) &&
      decide (0 ≤ h) then
    match logHalf (CQ.sub P.B P.A), logHalf (CQ.neg (z0of P.A P.B zc)),
        argEnc (CQ.neg (z0of P.A P.B zc)), logHalf (CQ.sub CQ.one (z0of P.A P.B zc)),
        argEnc (CQ.sub CQ.one (z0of P.A P.B zc)) with
    | some (lv, εv), some (l0, e0l), some (a0, e0a), some (l1, e1l), some (a1, e1a) =>
      some ((List.range n).map (pieceCoef n P (z0of P.A P.B zc) (eof P.A P.B dd) ⟨l0, a0⟩ ⟨l1, a1⟩ lv),
        lsum (fun m =>
            (nrmQ (PAc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd) m) * (e1l + e1a)
             + nrmQ (PBc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd) m) * (e0l + e0a))
              * h ^ m) n
        + |massQ (coeffs P.a) (P.a.length - 1)| * εv,
        [⟨q1of (z0of P.A P.B zc) (eof P.A P.B dd),
            (List.range n).map (PAc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd))⟩,
         ⟨q0of (z0of P.A P.B zc) (eof P.A P.B dd),
            (List.range n).map (PBc (coeffs P.a) (P.a.length - 1) (z0of P.A P.B zc) (eof P.A P.B dd))⟩])
    | _, _, _, _, _ => none
  else none

/-- Aggregate (weights `-w`): model, enclosure error, and the (unmerged) remainder terms. -/
def aggEval2 (n : ℕ) (zc dd : CQ) (h : ℚ) : List WP → Option (List ℚ × ℚ × List Tm)
  | [] => some ([], 0, [])
  | P :: ps =>
    match pieceEval2 n P zc dd h, aggEval2 n zc dd h ps with
    | some (c, E, T), some (C, F, T') =>
      some (addL (scaleL (-P.w) c) C, |P.w| * E + F,
        T.map (fun t => (⟨t.q, scaleC (-P.w) t.P⟩ : Tm)) ++ T')
    | _, _ => none

/-- The merged aggregate: model `C` and total error `F` (as `aggEval`, but with merged remainders). -/
def aggEvalM (n : ℕ) (zc dd : CQ) (h : ℚ) (ps : List WP) : Option (List ℚ × ℚ) :=
  match aggEval2 n zc dd h ps with
  | some (C, F, T) =>
    if tmOk h (mergeAll T) then some (C, F + tmErr n h (mergeAll T)) else none
  | none => none

end CatalanCore.Uniform.Decay.NearCells
