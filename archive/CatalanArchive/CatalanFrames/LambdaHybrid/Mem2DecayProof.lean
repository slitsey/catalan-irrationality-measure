module

public import CatalanFrames.Lambda.Const
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Decay.Rect.DecayTop
public import CatalanArchive.CatalanCore.Cert.SigmaHyb.FinalH

@[expose] public section

/-!
# λ hybrid: decay of the second member, proved (MEM2D)

`Mem2Decay lamFrame (39028/10000) (76444/10000)`: `mem2Decay_of_certG_rect` (`decay_top_of_certG_rect`) applied to the same
certificate `certHyb` as member 1.  With `Mem2Content` still open, this leaves exactly one
hypothesis in the λ hybrid measure theorem.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

theorem lam_mem2_decay :
    Mem2Decay lamFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ) :=
  CatalanCore.mem2Decay_of_certG_rect (Fr := lamFrame)
    CatalanCore.Cert.Sigma300.lam_decayOK CatalanCore.Cert.SigmaHyb.certHyb
    CatalanCore.Cert.SigmaHyb.hg_hyb (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k)
    (Rc := 1) (by norm_num) CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le (by simp [CatalanCore.Cert.SigmaHyb.certHyb]; norm_num)

#print axioms lam_mem2_decay

end CatalanFrames.LambdaHybrid
