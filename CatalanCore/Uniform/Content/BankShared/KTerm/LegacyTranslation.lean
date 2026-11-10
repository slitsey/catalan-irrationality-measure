module

public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodTranslation
public import CatalanCore.Uniform.Content.BankShared.Check.Prefix
public import CatalanCore.Uniform.Content.UFSimple.WrapTranslation
public import CatalanCore.Uniform.Content.UFSimple.WrapPrefixCheck

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000

/-! Generic transport adapters for one checked representative per branch orbit.
Catalogue validity is deliberately a separate input to the accepted PC engine. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.UFSimple

noncomputable def Transl.ofFamily (b a Kc Ω : ℕ) (F : ℕ → KBranch) (ν : ℕ)
    (hdebit : ∀ n,(F (ν+a*n)).debit=(F ν).debit)
    (hprice : ∀ n r p m kv,(F (ν+a*n)).τ.evalN (r+n*b*p) p (m+n*a*p) kv =
      (F ν).τ.evalN r p m kv+n*Kc*p)
    (hcond : ∀ n r p m kv,r+n*b*p≤Ω*p →
      (∀ cd∈(F ν).conds,cd.Holds r p m kv) →
      ∀ cd∈(F (ν+a*n)).conds,cd.Holds (r+n*b*p) p (m+n*a*p) kv) :
    Transl b a Kc Ω [F ν] := by
  classical
  exact
    { ρ := fun n br => if br=F ν then F (ν+a*n) else br
      debit := by
        intro n br
        split_ifs with h
        · simpa only [h] using hdebit n
        · rfl
      price := by
        intro n br hb r p m kv
        have h : br=F ν := by simpa only [List.mem_singleton] using hb
        subst br
        simp only [if_pos rfl]
        exact hprice n r p m kv
      cond := by
        intro n br hb r p m kv hΩ h cd hcd
        have he : br=F ν := by simpa only [List.mem_singleton] using hb
        subst br
        simp only [if_pos rfl] at hcd ⊢
        exact hcond n r p m kv hΩ h cd hcd }

theorem pre_duplicate_eval (ν j0 j1 r p m k : ℕ) :
    (kbrPre ν j0 [j1,j1]).τ.evalN r p m (fun _ => k) =
      (brPre ν j0 j1).τ.evalN r p m k := by
  simp only [kbrPre,kPreLo,kPreHi,kNn,kMn,kMx,kPoleLos,kPoleHis,KExpr.evalN,
    brPre,Cat.tPre,Cat.preLo,Cat.preHi,Cat.eNn,Expr.evalN]
  split_ifs <;> simp only [KExpr.evalN,Expr.evalN] <;> omega

theorem legacy_pre_cov (a b t ν j0 j1 r p m k : ℕ) :
    (brPre (ν+a*t) j0 j1).τ.evalN (r+t*b*p) p (m+t*a*p) k =
      (brPre ν j0 j1).τ.evalN r p m k+t*(2*b+2*a)*p := by
  rw [←pre_duplicate_eval (ν+a*t) j0 j1 (r+t*b*p) p (m+t*a*p) k,
    pre_cov,pre_duplicate_eval]

noncomputable def legacyPreTranslation (b a Ω idx ν j0 j1 : ℕ) :
    Transl b a (2*b+2*a) Ω [(brPre ν j0 j1).liftK idx] :=
  Transl.ofFamily b a (2*b+2*a) Ω (fun n => (brPre n j0 j1).liftK idx) ν
    (by intro n;rfl)
    (by
      intro n r p m kv
      change ((brPre (ν+a*n) j0 j1).τ.liftK idx).evalN _ _ _ _=_
      rw [evalN_liftK]
      change _=((brPre ν j0 j1).τ.liftK idx).evalN _ _ _ _+_
      rw [evalN_liftK]
      exact legacy_pre_cov a b n ν j0 j1 r p m (kv idx))
    (by intro n r p m kv _ _ cd hcd;simp [Branch.liftK,brPre] at hcd)

noncomputable def wrapPrefixTranslation (b a Ω idx ν : ℕ) (hν : 1≤ν) :
    Transl b a (2*b+2*a) Ω [(WrapPrefixCheck.brPrefix ν).liftK idx] :=
  Transl.ofFamily b a (2*b+2*a) Ω (fun n => (WrapPrefixCheck.brPrefix n).liftK idx) ν
    (by intro n;rfl)
    (by
      intro n r p m kv
      change ((WrapExpr.tWrap (ν+a*n)).liftK idx).evalN _ _ _ _=_
      rw [evalN_liftK]
      change _=((WrapExpr.tWrap ν).liftK idx).evalN _ _ _ _+_
      rw [evalN_liftK]
      exact WrapExpr.wrap_cov a b n ν r p m (kv idx) hν)
    (by
      intro n r p m kv _ h cd hcd
      have hl := h ((WrapPrefixCheck.prefixLo ν).liftK idx) (by
        simp [Branch.liftK,WrapPrefixCheck.brPrefix])
      have hh := h ((WrapPrefixCheck.prefixHi ν).liftK idx) (by
        simp [Branch.liftK,WrapPrefixCheck.brPrefix])
      rw [holds_liftK,WrapPrefixCheck.prefixLo_iff] at hl
      rw [holds_liftK,WrapPrefixCheck.prefixHi_iff] at hh
      simp only [Branch.liftK,WrapPrefixCheck.brPrefix,List.map_cons,List.map_nil,
        List.mem_cons,List.not_mem_nil,or_false] at hcd
      rcases hcd with rfl | rfl
      · rw [holds_liftK,WrapPrefixCheck.prefixLo_iff]
        have he : (ν+a*n)*p=ν*p+n*a*p := by ring
        omega
      · rw [holds_liftK,WrapPrefixCheck.prefixHi_iff]
        have he : (ν+a*n+1)*p=(ν+1)*p+n*a*p := by ring
        omega)

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.Transl.ofFamily
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.legacy_pre_cov
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.legacyPreTranslation
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.wrapPrefixTranslation
