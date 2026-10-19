module

public import CatalanFrames.Lambda.Const
public import CatalanCore.Rect.PairBridge
public import CatalanCore.Decay.Rect.DecayTop
public import CatalanCore.Cert.SigmaHyb.FinalH

@[expose] public section

/-!
# λ hybrid: decay of the second member, proved (MEM2D)

`Mem2Decay lamFrame (39028/10000) (76444/10000)`: `decay_top_of_certG_rect` applied to the same
certificate `certHyb` as member 1.  With `Mem2Content` still open, this leaves exactly one
hypothesis in the λ hybrid measure theorem.
-/

open Filter CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid CatalanFrames.Lambda

namespace CatalanFrames.LambdaHybrid

theorem lam_mem2_decay :
    Mem2Decay lamFrame (((39028 / 10000 : ℚ)) : ℝ) (((76444 / 10000 : ℚ)) : ℝ) := by
  intro δ hδ
  obtain ⟨N, hN⟩ := CatalanCore.decay_top_of_certG_rect (Fr := lamFrame)
    CatalanCore.Cert.Sigma300.lam_decayOK CatalanCore.Cert.SigmaHyb.certHyb (α := 1 / 8)
    (by norm_num) CatalanCore.Cert.SigmaHyb.hg_hyb
    (fun k => CatalanCore.Cert.SigmaHyb.wtH_nonneg k) (Rc := 1) (by norm_num)
    CatalanCore.Cert.SigmaHyb.cH_norm CatalanCore.Cert.SigmaHyb.Inu_le
    CatalanCore.Cert.SigmaHyb.D_le (by simp [CatalanCore.Cert.SigmaHyb.certHyb]; norm_num) δ hδ
  refine ⟨N, fun r h8 hr t ht => ?_⟩
  have hm : ((r / 8 : ℕ) : ℝ) = (((1 / 8 : ℚ)) : ℝ) * r := by
    obtain ⟨k, rfl⟩ := h8
    rw [Nat.mul_div_cancel_left _ (by norm_num)]
    push_cast; ring
  exact hN r (r / 8) hr hm t ht

#print axioms lam_mem2_decay

end CatalanFrames.LambdaHybrid
