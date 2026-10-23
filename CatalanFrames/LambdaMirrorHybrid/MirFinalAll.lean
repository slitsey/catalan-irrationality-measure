module

public import CatalanFrames.LambdaMirrorHybrid.MirT
public import CatalanFrames.HybCommon.TopSum
public import CatalanFrames.HybCommon.NegRect
public import CatalanFrames.LambdaMirrorHybrid.Assembly
public import CatalanCore.Cert.SigmaHyb.FinalH
public import CatalanCore.Cert.Sigma300.Glue
public import CatalanCore.Decay.Rect.DecayTop
public import CatalanFrames.LambdaMirrorHybrid.MirContent

@[expose] public section

/-!
# The mirror hybrid measure theorem `mir_hyb_measure_final` (`G + 5π²/48`)

Content: `mir_logDhybT_le` (tropical + extended weights) with the five generic deficit sums
(`HybCommon.Sums*`) gives `both_eps_G`; bordering (`mem2Content_of_both_G`) gives `Mem2Content`.
Decay: the same hybrid certificate `certHyb` as λ, applied with `mirror_decayOK` (frame-generic
`decay_of_certG_rect` / `decay_top_of_certG_rect`).
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.LambdaMirror CatalanFrames.HybCommon

namespace CatalanFrames.LambdaMirrorHybrid

/-- **Mirror hybrid decay, member 1** (`D = 3.9028`, `c = 7.6444`): the λ certificate at `mirFrame`. -/
theorem mir_hybrid_decay :
    HasDecay (hybridFamUp mirFrame (1 / 8 : ℚ)) (((39028 / 10000 : ℚ)) : ℝ)
      (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.decay_of_certG_rect (Fr := mirFrame) CatalanCore.Cert.Sigma300.mirror_decayOK
    CatalanCore.Cert.SigmaHyb.certHyb (α := 1 / 8) (by norm_num)
    CatalanCore.Cert.SigmaHyb.hg_hyb (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k) (Rc := 1)
    (by norm_num) CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le

/-- **Mirror hybrid decay, member 2.** -/
theorem mir_mem2_decay :
    Mem2Decay mirFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.mem2Decay_of_certG_rect (Fr := mirFrame)
    CatalanCore.Cert.Sigma300.mirror_decayOK CatalanCore.Cert.SigmaHyb.certHyb
    CatalanCore.Cert.SigmaHyb.hg_hyb (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k)
    (Rc := 1) (by norm_num) CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le (by simp [CatalanCore.Cert.SigmaHyb.certHyb]; norm_num)

#print axioms mir_hybrid_decay
#print axioms mir_mem2_decay

/-- The border cost is negligible for the mirror instance. -/
/-- **The mirror hybrid measure theorem**: `μ(G + 5π²/48) ≤ 38.35`. -/
theorem mir_hyb_measure_final :
    Measure.MeasureLBAt ((∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2)
      + 5 * Real.pi ^ 2 / 48) (((3835 / 100 : ℚ)) : ℝ) :=
  mir_hyb_measure_G (Λ := 370343 / 100000) (D := 39028 / 10000) (C := 76444 / 10000)
    (E := 3835 / 100)
    (mir_hasContent (by norm_num) (by push_cast; norm_num)) mir_hybrid_decay mir_mem2_decay
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- final theorem
#print axioms mir_hyb_measure_final

end CatalanFrames.LambdaMirrorHybrid
