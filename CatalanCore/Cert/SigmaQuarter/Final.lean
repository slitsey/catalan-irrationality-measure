module
public import CatalanCore.Cert.SigmaQuarter.FinalCore
public import CatalanCore.Cert.SigmaQuarter.Finite
public import CatalanCore.Cert.SigmaQuarter.Energy
public import CatalanCore.Cert.SigmaQuarter.Jfun
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter

/-- Frozen1200-atom certificate at the quarter border. -/
noncomputable def certQ :
    CertCoreG pts.length (1/2048 : ℝ) (1/1000 : ℝ) cQ mQ :=
  assemble controls I_ok

theorem certQ_ccert : certQ.ccert = 4013201/500000 := rfl

theorem D_le : (2323303/500000 : ℚ) ≤ certQ.Dof 3 (1/4) (184428/100000) :=
  assemble_D_le controls I_ok

theorem hg_Q (s : ℂ) : certQ.g s = (1+(((1/4 : ℚ)) : ℝ)) *
    CatalanLambda.Decay.Usig (1/2048 : ℝ) cQ mQ s -
      CatalanCore.Decay.Unu (((1/4 : ℚ)) : ℝ) s +
        (1-(1/1000 : ℝ))*Real.pi*|s.im| := by
  have he : (((1/4 : ℚ)) : ℝ) = (1/4 : ℝ) := by norm_num
  rw [he]
  rfl
end CatalanCore.Cert.SigmaQuarter
#print axioms CatalanCore.Cert.SigmaQuarter.certQ
