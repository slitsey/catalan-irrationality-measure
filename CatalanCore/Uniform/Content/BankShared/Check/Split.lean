import CatalanCore.Uniform.Content.BankShared.Check.Bank
set_option Elab.async false

/-! # Bank data split across modules (lane C1L)

The template check `tmplOK D j T` reads only the parameter fields of the bank (`q, α, depth, cF, Pbad, t0, τ,
extra`).  So the templates of a large bank can be checked in separate modules against a header bank `H`
(templates `[]`, any `Λ`), and the checks transport to the full bank `{H with Λ := Λ, tmpls := l}`
(`tmplOK_withTmpls`).  This keeps each data module small; nothing about the check changes. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- `tmplOK` depends only on the parameter fields. -/
theorem tmplOK_congr {D D' : BankData} (hq : D'.q = D.q) (hα : D'.α = D.α) (hd : D'.depth = D.depth)
    (hc : D'.cF = D.cF) (hP : D'.Pbad = D.Pbad) (ht : D'.t0 = D.t0) (hτ : D'.τ = D.τ)
    (hx : D'.extra = D.extra) (j : ℕ) (T : QTmpl) : tmplOK D' j T = tmplOK D j T := by
  obtain ⟨q, M, α, mem, dep, cF, Pb, α0, τ, Λ, α0b, t0, ex, tm⟩ := D
  obtain ⟨q', M', α', mem', dep', cF', Pb', α0', τ', Λ', α0b', t0', ex', tm'⟩ := D'
  simp only at hq hα hd hc hP ht hτ hx
  subst hq hα hd hc hP ht hτ hx
  rfl

/-- **Transport**: a template check against the header bank `H` holds for `{H with Λ := Λ, tmpls := l}`. -/
theorem tmplOK_withTmpls (H : BankData) (Λ : ℚ) (l : List (ℕ × QTmpl)) (j : ℕ) (T : QTmpl)
    (h : tmplOK H j T = true) : tmplOK { H with Λ := Λ, tmpls := l } j T = true := by
  exact (tmplOK_congr (D := H) (D' := { H with Λ := Λ, tmpls := l }) rfl rfl rfl rfl rfl rfl rfl rfl j T).trans h

end CatalanCore.Uniform.Content.BankShared.Check
