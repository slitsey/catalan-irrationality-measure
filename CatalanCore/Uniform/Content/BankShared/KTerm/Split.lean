import CatalanCore.Uniform.Content.BankShared.KTerm.Bank
set_option Elab.async false

/-! # k-shift bank data split across modules (lane K)

The template check `ktmplOK D j T` reads only the parameter fields of the bank (all but `Λ` and `tmpls`).  So the
templates of a bank can be checked in separate modules against a header bank `H` (templates `[]`, any `Λ`), and the
checks transport to `{H with Λ := Λ, tmpls := l}` (`ktmplOK_withTmpls`), as for `Check.Split`. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check

theorem kpieceAll_append (D : KBankData) (j : ℕ) (l₁ l₂ : List (QPiece × Cert)) :
    kpieceAll D j (l₁ ++ l₂) = (kpieceAll D j l₁ && kpieceAll D j l₂) := by
  unfold kpieceAll
  exact List.all_append

/-- **Transport**: a template check against the header bank `H` holds for `{H with Λ := Λ, tmpls := l}`. -/
theorem ktmplOK_withTmpls (H : KBankData) (Λ : ℚ) (l : List (ℕ × KTmpl)) (j : ℕ) (T : KTmpl)
    (h : ktmplOK H j T = true) : ktmplOK { H with Λ := Λ, tmpls := l } j T = true := h

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kpieceAll_append
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.ktmplOK_withTmpls
