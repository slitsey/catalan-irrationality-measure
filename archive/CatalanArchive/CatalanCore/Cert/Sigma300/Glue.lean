module

public import CatalanCore.Decay.Main
public import CatalanLambda.Cert.Final
public import CatalanFrames.Lambda.Contour
public import CatalanFrames.Lambda.Decay
public import CatalanFrames.LambdaMirror.Contour
public import CatalanFrames.P6.Contour

@[expose] public section

/-!
# Sigma300 glue: the legacy certificate as a `CertCore`, and the generic decay at three frames (WP3)

* `Sigma300.certCore := CertCore.ofFacts CatalanLambda.Cert.certFacts` (the Cert/Engine files are not
  moved; only the two density-dependent fields are reshaped, `Sbase = SCERT/2`).
* `Dof 2 0 (3/2) ≥ 31111/10000` : the λ negative control (legacy `Dcert`).
* `Dof 3 0 (3/2) ≥ 30002/10000` : P6 row A (design 3.1: `m′`, `I`, `S_old` as in Lean).
* `ccert = 68726/10000`, density-free.
* `DecayOK'` for `lamFrame`, `mirFrame`, `p6Frame`, and `decay_of_cert` instantiated at each.

NEXT STEP (not built here): P6's own σ (FK row D, μ ≈ 29.94) needs new tables
(`SigmaData`-type tables, ray macros, seg/line data, glue) and a second `CertCore`; the
generic `decay_of_cert` applies to it unchanged.
-/

open CatalanCore CatalanCore.Cert

namespace CatalanCore.Cert.Sigma300

/-- The legacy σ = 300 certificate as a frame-free `CertCore` (density-free). -/
noncomputable def certCore : CertCore 300 (1 / 1024 : ℝ) (1 / 1000 : ℝ)
    CatalanLambda.Cert.cS CatalanLambda.Cert.mS :=
  CertCore.ofFacts CatalanLambda.Cert.certFacts

theorem ccert_eq : certCore.ccert = 68726 / 10000 := rfl

/-- Density 2 (λ, mirror): the legacy `Dcert = 31111/10000`. -/
theorem Dof_two : (31111 / 10000 : ℚ) ≤ certCore.Dof 2 0 (3 / 2) := by
  unfold certCore CertCore.Dof CertCore.ofFacts
  simp only [CatalanLambda.Cert.certFacts]
  unfold CatalanLambda.Cert.SCERT CatalanLambda.Cert.IBOUND CatalanLambda.Cert.MPRAY
    CatalanLambda.Cert.SVAL
  norm_num

/-- Density 3 (P6 row A): `D = 30002/10000`. -/
theorem Dof_three : (30002 / 10000 : ℚ) ≤ certCore.Dof 3 0 (3 / 2) := by
  unfold certCore CertCore.Dof CertCore.ofFacts
  simp only [CatalanLambda.Cert.certFacts]
  unfold CatalanLambda.Cert.SCERT CatalanLambda.Cert.IBOUND CatalanLambda.Cert.MPRAY
    CatalanLambda.Cert.SVAL
  norm_num

end CatalanCore.Cert.Sigma300

/-! ### The frame hypotheses at the three frames -/

namespace CatalanCore.Cert.Sigma300

open CatalanFrames

theorem lam_decayOK : Frame.DecayOK' Lambda.lamFrame where
  contour := Lambda.lam_contourOK
  delta := by norm_num [Lambda.lamFrame]
  atomRange := by
    intro i
    fin_cases i <;> simp [Lambda.lamFrame] <;> norm_num
  norm_ge := by norm_num [Lambda.lamFrame]

theorem mirror_decayOK : Frame.DecayOK' LambdaMirror.mirFrame where
  contour := LambdaMirror.mirror_contourOK
  delta := by norm_num [LambdaMirror.mirFrame]
  atomRange := by
    intro i
    fin_cases i <;> simp [LambdaMirror.mirFrame] <;> norm_num
  norm_ge := by norm_num [LambdaMirror.mirFrame]

theorem p6_decayOK : Frame.DecayOK' P6.p6Frame where
  contour := P6.p6_contourOK
  delta := by norm_num [P6.p6Frame]
  atomRange := by
    intro i
    fin_cases i <;> simp [P6.p6Frame] <;> norm_num
  norm_ge := by norm_num [P6.p6Frame]

/-- **Negative control.**  The generic `decay_of_cert` at `lamFrame` (density 2) with the σ = 300
certificate reproduces the legacy decay statement (`CatalanFrames.Lambda.Final.hD_cert`). -/
theorem lam_decay : HasDecay (PolyFamily.ofFrame Lambda.lamFrame) (((31111 / 10000 : ℚ)) : ℝ)
    (((68726 / 10000 : ℚ)) : ℝ) := by
  have := decay_of_cert lam_decayOK certCore Dof_two
  rwa [ccert_eq] at this

/-- The same statement for the mirror (density 2). -/
theorem mirror_decay : HasDecay (PolyFamily.ofFrame LambdaMirror.mirFrame) (((31111 / 10000 : ℚ)) : ℝ)
    (((68726 / 10000 : ℚ)) : ℝ) := by
  have := decay_of_cert mirror_decayOK certCore Dof_two
  rwa [ccert_eq] at this

/-- **P6 row A**: density 3, the σ = 300 certificate: `D = 3.0002`, `c = 6.8726`. -/
theorem p6_decay_rowA : HasDecay (PolyFamily.ofFrame P6.p6Frame) (((30002 / 10000 : ℚ)) : ℝ)
    (((68726 / 10000 : ℚ)) : ℝ) := by
  have := decay_of_cert p6_decayOK certCore Dof_three
  rwa [ccert_eq] at this

end CatalanCore.Cert.Sigma300

namespace CatalanCore.Cert.Sigma300

open CatalanFrames

/-- The λ specialisation of the head (left open by WP2a): `atomHead = ∑_{m<N0} atomSum`. -/
theorem lam_atomHead (N0 a b : ℕ) :
    Lambda.lamFrame.atomHead N0 a b = ∑ m ∈ Finset.range N0, Lambda.lamFrame.atomSum a b m := by
  have e0 : ((Lambda.lamFrame.μ (0 : Fin 2) : ℚ) : ℝ) = 3 / 4 := by
    show (((3 / 4 : ℚ)) : ℝ) = 3 / 4; norm_num
  have e1 : ((Lambda.lamFrame.μ (1 : Fin 2) : ℚ) : ℝ) = 1 := by
    show (((1 : ℚ)) : ℝ) = 1; norm_num
  have hx : ((Lambda.lamFrame.xs : ℚ) : ℝ) = 3 / 8 := by
    show (((3 / 8 : ℚ)) : ℝ) = 3 / 8; norm_num
  refine Frame.atomHead_eq_sum Lambda.lamFrame N0 a b ?_ ?_
  · intro m hm i
    have hm' : (m : ℝ) + 1 ≤ N0 := by exact_mod_cast hm
    rw [hx, not_lt]
    fin_cases i
    · show (m : ℝ) + ((Lambda.lamFrame.μ (0 : Fin 2) : ℚ) : ℝ) ≤ (N0 : ℝ) + 3 / 8
      rw [e0]; linarith
    · show (m : ℝ) + ((Lambda.lamFrame.μ (1 : Fin 2) : ℚ) : ℝ) ≤ (N0 : ℝ) + 3 / 8
      rw [e1]; linarith
  · intro m hm i
    have hm' : (N0 : ℝ) ≤ m := by exact_mod_cast hm
    rw [hx]
    fin_cases i
    · show (N0 : ℝ) + 3 / 8 < (m : ℝ) + ((Lambda.lamFrame.μ (0 : Fin 2) : ℚ) : ℝ)
      rw [e0]; linarith
    · show (N0 : ℝ) + 3 / 8 < (m : ℝ) + ((Lambda.lamFrame.μ (1 : Fin 2) : ℚ) : ℝ)
      rw [e1]; linarith

end CatalanCore.Cert.Sigma300
