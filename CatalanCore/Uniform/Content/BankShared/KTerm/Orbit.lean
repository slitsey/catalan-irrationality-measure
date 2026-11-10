module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic

@[expose] public section
set_option Elab.async false

/-! Checked orbit seeds reuse the accepted periodic engine. The numeric
threshold is separate from a possibly noncomputable family threshold. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared.Check Polynomial

structure OrbitSeed where
  base : QPiece × Cert
  b : ℕ
  a : ℕ
  Kc : ℕ
  Ω : ℕ
  N : ℕ
  times : List ℕ

noncomputable def identityTranslation (Ω : ℕ) (kb : List KBranch) : Transl 0 0 0 Ω kb where
  ρ _ br := br
  debit _ _ := rfl
  price := by intro n br _ r p m kv;simp
  cond := by intro n br _ r p m kv _ h cd hcd;simpa using h cd hcd

def OrbitSeed.pieces (cF : ℕ) (S : OrbitSeed) : List (QPiece × Cert) :=
  S.times.map (fun n => (trPiece S.b S.Kc cF S.base.2.R n S.base.1,dummyCert))

def seedOK (D : KBankData) (kb : List KBranch) (j L : ℕ) (S : OrbitSeed) : Bool :=
  cellOKb D kb j S.N S.b S.Ω S.base && S.times.all (fun n => decide (n≤S.N)) &&
    decide (S.base.2.R*S.base.1.t≤(L:ℚ))

theorem seed_facts {D : KBankData} (hpar : KParams D) {c : ℚ} {hc : 0<c}
    {const : ℝ} {depth : ℕ} {Q : NodeFamily.Index (altGeom c hc).geometry → ℚ[X]}
    (hdepth : depth≤D.depth) {L N0 j : ℕ} (hL : L≤N0) (S : OrbitSeed)
    (hab : D.α*S.b=S.a) {kb : List KBranch} (tr : Transl S.b S.a S.Kc S.Ω kb)
    (hvalid : ∀ n,KCatValidFam c hc const depth Q D.shifts D.Q D.Pbad N0 (kb.map (tr.ρ n)))
    (hok : seedOK D kb j L S=true) :
    ∀ z∈S.pieces D.cF,PieceBasic z.1 ∧ PieceCov D c hc const depth Q N0 j z.1 := by
  have hpar' := hpar
  obtain ⟨hq,-,-,-,-,-,hα,-,-,-⟩ := hpar'
  simp only [seedOK,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hok
  obtain ⟨⟨hok,htimes⟩,hlim⟩ := hok
  obtain ⟨⟨hbasic,hR,hΩ⟩,hbase⟩ := cellOKb_facts (by omega : 1≤D.Q) hα hok
  intro z hz
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hz
  have hnN : n≤S.N := htimes n hn
  have hnQ : (n:ℚ)≤(S.N:ℚ) := by exact_mod_cast hnN
  have hLQ : (L:ℚ)≤(N0:ℚ) := by exact_mod_cast hL
  refine ⟨trPiece_basic hbasic S.b S.Kc D.cF S.base.2.R n,?_⟩
  exact exp_cov_per_large hpar hdepth hab tr hvalid hbasic hbase
    (by linarith) n (by
      have hb : (0:ℚ)≤(S.b:ℚ) := Nat.cast_nonneg _
      have h := mul_le_mul_of_nonneg_right hnQ hb
      linarith)

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.identityTranslation
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.seed_facts
