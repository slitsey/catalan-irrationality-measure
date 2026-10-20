module
public import CatalanCore.Arith.Hybrid.ChainTransport
public import CatalanCore.Arith.Hybrid.LemmaE.ModelPartners
public import CatalanCore.Rect.Full
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
variable {Z : Type} [Fintype Z] [DecidableEq Z]
noncomputable def full (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :
    Matrix (Fin r ⊕ Z) (Fin r ⊕ Z) ℚ[X] :=
  (Rect.FullN Fr (fun i : Fin r => i.val) xs ys (X : ℚ[X])).map (rescaleHom p 2)
noncomputable def Q (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  LemmaE.Atil p (fun _ : Fin r => 1) (full Fr p r xs ys).toBlocks₁₁
noncomputable def Q0 (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  LemmaE.blockProject (fun i : Fin r => i.val % p) (Q Fr p r xs ys)
noncomputable def h (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  (Q0 Fr p r xs ys).det
noncomputable def B2 (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  C ((p : ℚ)^2) • (full Fr p r xs ys).toBlocks₁₂
noncomputable def C2 (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  C ((p : ℚ)^2) • (full Fr p r xs ys).toBlocks₂₁
noncomputable def Sr (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  LemmaE.modelRow (fun i : Fin r => i.val % p) (fun z => xs z % p)
    (Q0 Fr p r xs ys) (C2 Fr p r xs ys)
noncomputable def Sc (Fr : Frame) (p r : ℕ) (xs ys : Z → ℕ) :=
  LemmaE.modelCol (fun i : Fin r => i.val % p) (fun z => ys z % p)
    (Q0 Fr p r xs ys) (B2 Fr p r xs ys)
end CatalanCore.Arith.Hybrid.ChainModel
