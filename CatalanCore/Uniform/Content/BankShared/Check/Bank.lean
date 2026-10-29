import CatalanCore.Uniform.Content.BankShared.Check.Catalogue
import CatalanCore.Uniform.Content.Member.Template
set_option Elab.async false

/-! # Bank data and the one Boolean check (lane C1L; C1/PAPER.md §5, (D1)-(D6))

`BankData`: the parameters `q, α, M`, the members `a`, the depth, the frame constants `c_Fr`, `P_bad`, the prefix
lemma's `(t0, α0b)`, `α0, τ, Λ_fin`, the bank's extra branches (catalogue `tableT ++ extra`), and per root class `j`
a template `(t1, pieces with certificates)`.

`check D` (all comparisons of rationals):
* (D1) every member `a` and unit class `c < M` has `j(a, c) = a c⁻¹ mod q` with a template;
* (D2) every template is a chain from `t1` (contiguity; (K0) is part of `pieceOK`);
* (D3) `α0 ≥ α0b`, `0 < t1 ≤ t0`;
* (D4) `κ_j tend_j ≥ 1 + 2α`, `tend_j ≥ q(1+2α)`, `2 tend_j ≥ P_bad`, `tend_j ≤ τ`;
* (D5) every piece passes `pieceOK` (K0)-(K4) at `κ = j/q`;
* (D6) for every member: `Σ_{c unit mod M} mass T_{j(a,c)} = φ(M) Λ_fin`;
plus the frame checks `2 ≤ q ≤ P_bad`, `q ∣ M`, `0 < a < q`, `gcd(a, q) = 1`.

The real templates: `mkTemplate`, `tmplOf D a c`; `mass_tmplOf`, `tend_tmplOf`, `contentConstant_tmplOf`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member

/-- A class template with rational data. -/
structure QTmpl where
  t1 : ℚ
  pieces : List (QPiece × Cert)

/-- The data of a two-term bank. -/
structure BankData where
  q : ℕ
  M : ℕ
  α : ℚ
  members : List ℕ
  depth : ℕ
  cF : ℕ
  Pbad : ℕ
  α0 : ℚ
  τ : ℚ
  Λ : ℚ
  α0b : ℚ
  t0 : ℚ
  extra : List Branch
  tmpls : List (ℕ × QTmpl)

namespace BankData

/-- The catalogue: table T, then the bank's branches. -/
def cat (D : BankData) : List Branch := tableT ++ D.extra

end BankData

/-- The template of the root class `j`. -/
def findT (j : ℕ) : List (ℕ × QTmpl) → Option QTmpl
  | [] => none
  | x :: l => if x.1 = j then some x.2 else findT j l

theorem findT_mem (j : ℕ) : ∀ (l : List (ℕ × QTmpl)) {T : QTmpl}, findT j l = some T → (j, T) ∈ l
  | [], _, h => by simp [findT] at h
  | x :: l, T, h => by
    unfold findT at h
    split_ifs at h with hx
    · simp only [Option.some.injEq] at h; subst h; rw [← hx]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (findT_mem j l h)

/-- The root class `j(a, c)`: the least `x < q` with `x c ≡ a (mod q)`. -/
def jOf (q a c : ℕ) : Option ℕ := (List.range q).find? (fun x => (x * c) % q == a % q)

theorem jOf_spec {q a c j : ℕ} (h : jOf q a c = some j) : j < q ∧ (j * c) % q = a % q := by
  unfold jOf at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  simp only [beq_iff_eq] at h1
  exact ⟨List.mem_range.1 h2, h1⟩

/-- Contiguity of the pieces. -/
def chainOK : ℚ → List (QPiece × Cert) → Bool
  | _, [] => true
  | s0, x :: l => decide (x.1.s = s0) && chainOK x.1.t l

/-- The right end. -/
def tendQ : ℚ → List (QPiece × Cert) → ℚ
  | s0, [] => s0
  | _, x :: l => tendQ x.1.t l

/-- The integral of a piece. -/
def QPiece.mass (P : QPiece) : ℚ := P.a * (P.t - P.s) + P.b * (P.t * P.t - P.s * P.s) / 2

/-- The mass `α0 t1 + Σ ∫ P` of a template. -/
def QTmpl.mass (α0 : ℚ) (T : QTmpl) : ℚ := α0 * T.t1 + (T.pieces.map (fun x => x.1.mass)).sum

/-- (D5) on a list of pieces of the root class `j`. -/
def pieceAll (D : BankData) (j : ℕ) (l : List (QPiece × Cert)) : Bool :=
  l.all (fun x => pieceOK D.cat D.q D.α ((j : ℚ) / D.q) D.depth D.cF D.Pbad x.1 x.2)

theorem pieceAll_append (D : BankData) (j : ℕ) (l₁ l₂ : List (QPiece × Cert)) :
    pieceAll D j (l₁ ++ l₂) = (pieceAll D j l₁ && pieceAll D j l₂) := by
  simp [pieceAll, List.all_append]

/-- (D2)-(D4) for the root class `j`. -/
def tmplHead (D : BankData) (j : ℕ) (T : QTmpl) : Bool :=
  decide (0 < T.t1) && decide (T.t1 ≤ D.t0) && chainOK T.t1 T.pieces &&
    decide (1 + 2 * D.α ≤ (j : ℚ) / D.q * tendQ T.t1 T.pieces) &&
    decide ((D.q : ℚ) * (1 + 2 * D.α) ≤ tendQ T.t1 T.pieces) &&
    decide ((D.Pbad : ℚ) ≤ 2 * tendQ T.t1 T.pieces) &&
    decide (tendQ T.t1 T.pieces ≤ D.τ)

/-- (D2)-(D5) for the root class `j`. -/
def tmplOK (D : BankData) (j : ℕ) (T : QTmpl) : Bool := tmplHead D j T && pieceAll D j T.pieces

/-- `Σ_{c < n, gcd(M, c) = 1} f c`. -/
def unitSum (M : ℕ) (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => unitSum M f n + (if Nat.gcd M n = 1 then f n else 0)

/-- `#{c < n : gcd(M, c) = 1}`. -/
def unitCount (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => unitCount M n + (if Nat.gcd M n = 1 then 1 else 0)

/-- `P c` for every `c < n` with `gcd(M, c) = 1`. -/
def unitAll (M : ℕ) (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => unitAll M P n && (!decide (Nat.gcd M n = 1) || P n)

/-- The mass of the template of the class `c` for the member `a` (`0` when missing). -/
def classMass (D : BankData) (a c : ℕ) : ℚ :=
  match jOf D.q a c with
  | some j => match findT j D.tmpls with
    | some T => T.mass D.α0
    | none => 0
  | none => 0

/-- (D1) and (D6) for the member `a`. -/
def classOK (D : BankData) (a : ℕ) : Bool :=
  decide (0 < a) && decide (a < D.q) && decide (Nat.gcd a D.q = 1) &&
    unitAll D.M (fun c => match jOf D.q a c with
      | some j => (findT j D.tmpls).isSome
      | none => false) D.M &&
    decide (unitSum D.M (classMass D a) D.M = D.Λ * unitCount D.M D.M)

/-- The frame checks and (D3) for `α0`. -/
def checkParams (D : BankData) : Bool :=
  decide (2 ≤ D.q) && decide (D.q ≤ D.Pbad) && decide (0 < D.M) && decide (D.M % D.q = 0) &&
    decide (0 ≤ D.α) && decide (D.α0b ≤ D.α0) && decide (0 ≤ D.α0)

/-- **The bank check.** -/
def check (D : BankData) : Bool :=
  checkParams D && D.tmpls.all (fun x => tmplOK D x.1 x.2) && D.members.all (classOK D)

/-! ### The real templates -/

/-- The real piece. -/
noncomputable def QPiece.toPiece (P : QPiece) : Piece := ⟨P.s, P.t, P.a, P.b, P.C⟩

/-- The real piece list. -/
noncomputable def QTmpl.real (T : QTmpl) : List Piece := T.pieces.map (fun x => x.1.toPiece)

theorem chain_real {D : BankData} {κ : ℚ} :
    ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true →
      (∀ x ∈ l, pieceOK D.cat D.q D.α κ D.depth D.cF D.Pbad x.1 x.2 = true) →
      Chain (s0 : ℝ) (l.map (fun x => x.1.toPiece))
  | [], _, _, _ => trivial
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hx := hp x List.mem_cons_self
    unfold pieceOK at hx
    rcases hb : nth D.cat x.2.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hst⟩, ha0⟩, ha1⟩, hC0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [QPiece.toPiece, h.1]
    · show (0 : ℝ) < (x.1.s : ℝ); exact_mod_cast hs0
    · show (x.1.s : ℝ) ≤ x.1.t; exact_mod_cast hst.le
    · show (0 : ℝ) ≤ (x.1.C : ℝ); exact_mod_cast hC0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.s; exact_mod_cast ha0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.t; exact_mod_cast ha1
    · exact chain_real l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))

theorem lastEnd_real : ∀ (l : List (QPiece × Cert)) (s0 : ℚ),
    lastEnd (s0 : ℝ) (l.map (fun x => x.1.toPiece)) = (tendQ s0 l : ℝ)
  | [], _ => rfl
  | x :: l, _ => by simp only [List.map_cons, lastEnd, tendQ]; exact lastEnd_real l x.1.t

theorem listInt_real : ∀ (l : List (QPiece × Cert)),
    listInt (l.map (fun x => x.1.toPiece)) = ((l.map (fun x => x.1.mass)).sum : ℝ)
  | [] => by simp [listInt]
  | x :: l => by
    simp only [List.map_cons, listInt, List.sum_cons]
    rw [listInt_real l]
    simp only [Piece.int, QPiece.toPiece, QPiece.mass]
    push_cast; ring

open Classical in
/-- The real template of a rational template (a default template when the data are not a chain). -/
noncomputable def mkTemplate (α0 : ℚ) (T : QTmpl) : Template :=
  if h : 0 ≤ α0 ∧ 0 < T.t1 ∧ Chain (T.t1 : ℝ) T.real then
    ⟨α0, T.t1, T.real, by exact_mod_cast h.1, by exact_mod_cast h.2.1, h.2.2⟩
  else ⟨0, 1, [], le_refl _, one_pos, trivial⟩

/-- The template of the class `c` for the member `a`. -/
noncomputable def tmplOf (D : BankData) (a : ℕ) {M : ℕ} (c : ZMod M) : Template :=
  match jOf D.q a c.val with
  | some j => match findT j D.tmpls with
    | some T => mkTemplate D.α0 T
    | none => ⟨0, 1, [], le_refl _, one_pos, trivial⟩
  | none => ⟨0, 1, [], le_refl _, one_pos, trivial⟩

section Facts

variable {D : BankData} (hD : check D = true)
include hD

theorem check_params : 2 ≤ D.q ∧ D.q ≤ D.Pbad ∧ 0 < D.M ∧ D.M % D.q = 0 ∧ 0 ≤ D.α ∧ D.α0b ≤ D.α0 ∧
    0 ≤ D.α0 := by
  simp only [check, checkParams, Bool.and_eq_true, decide_eq_true_eq] at hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, -⟩, -⟩ := hD
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem check_tmpl {j : ℕ} {T : QTmpl} (h : findT j D.tmpls = some T) : tmplOK D j T = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hD
  exact hD.1.2 (j, T) (findT_mem j D.tmpls h)

theorem check_member {a : ℕ} (ha : a ∈ D.members) : classOK D a = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at hD
  exact hD.2 a ha

/-- The facts of one root-class template. -/
theorem tmpl_facts {j : ℕ} {T : QTmpl} (h : findT j D.tmpls = some T) :
    0 < T.t1 ∧ T.t1 ≤ D.t0 ∧ chainOK T.t1 T.pieces = true ∧
    (∀ x ∈ T.pieces, pieceOK D.cat D.q D.α ((j : ℚ) / D.q) D.depth D.cF D.Pbad x.1 x.2 = true) ∧
    1 + 2 * D.α ≤ (j : ℚ) / D.q * tendQ T.t1 T.pieces ∧ (D.q : ℚ) * (1 + 2 * D.α) ≤ tendQ T.t1 T.pieces ∧
    (D.Pbad : ℚ) ≤ 2 * tendQ T.t1 T.pieces ∧ tendQ T.t1 T.pieces ≤ D.τ := by
  have := check_tmpl hD h
  simp only [tmplOK, tmplHead, pieceAll, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h5⟩, h6⟩, h7⟩, h8⟩, h4⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem mkTemplate_eq {j : ℕ} {T : QTmpl} (h : findT j D.tmpls = some T) :
    mkTemplate D.α0 T = ⟨D.α0, T.t1, T.real, by exact_mod_cast (check_params hD).2.2.2.2.2.2,
      by exact_mod_cast (tmpl_facts hD h).1,
      chain_real T.pieces T.t1 (tmpl_facts hD h).2.2.1 (tmpl_facts hD h).2.2.2.1⟩ := by
  unfold mkTemplate
  rw [dif_pos ⟨(check_params hD).2.2.2.2.2.2, (tmpl_facts hD h).1,
    chain_real T.pieces T.t1 (tmpl_facts hD h).2.2.1 (tmpl_facts hD h).2.2.2.1⟩]

theorem mass_mkTemplate {j : ℕ} {T : QTmpl} (h : findT j D.tmpls = some T) :
    (mkTemplate D.α0 T).mass = (T.mass D.α0 : ℝ) := by
  rw [mkTemplate_eq hD h]
  simp only [Template.mass, QTmpl.real, QTmpl.mass]
  rw [listInt_real]; push_cast; rw [List.map_map]; rfl

theorem tend_mkTemplate {j : ℕ} {T : QTmpl} (h : findT j D.tmpls = some T) :
    (mkTemplate D.α0 T).tend = (tendQ T.t1 T.pieces : ℝ) := by
  rw [mkTemplate_eq hD h]
  simp only [Template.tend, QTmpl.real]
  exact lastEnd_real T.pieces T.t1

end Facts

end CatalanCore.Uniform.Content.BankShared.Check
