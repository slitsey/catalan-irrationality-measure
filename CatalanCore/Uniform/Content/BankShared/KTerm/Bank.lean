import CatalanCore.Uniform.Content.BankShared.KTerm.Expr
import CatalanCore.Uniform.Content.BankShared.Check.Bank
set_option Elab.async false

/-! # Bank data and the check for a k-shift bank (lane K)

`KBankData`: the master modulus `Q` and member `a` (master root `Q k = j p + (Q - a)`), the class modulus `M`, the
shifts `(q_i, o_i, s_i)`, the k-shift catalogue `kcat`, and per master root class `j` a template with a **tail
branch** `tb`.  The catalogue of the class `j` is `cat D j = kcat` compiled with
`k_i = t_i k - (b_i(j) p + c_i)` (`Inst.KShift`); there is no built-in table T.

`kcheck D` (all comparisons of rationals or naturals):
* frame: `2 ≤ Q ≤ P_bad`, `Q ∣ M`, `0 < a < Q`, `gcd(a, Q) = 1`, `0 ≤ α`, `α0b ≤ α0`, `0 ≤ α0`; every shift has
  `q ∣ Q`, `0 < o < q`, `s (Q - a) ≡ o (mod q)` with `o ≤ s (Q - a)`;
* per template `j`: `0 < t1 ≤ t0`, chain, `tend ≤ τ`, every shift has `s j ≢ 0 (mod q)` (its root class is
  nonzero), every piece passes `Check.pieceOK` on `cat D j` at `κ = j/Q`, and the tail test: the branch `tb` of
  `cat D j` has price `0`, debit `0`, every condition has `ℓ₁ ≥ 0`, `ℓ(tend) > 0` and
  `(1 - η⁻)/ℓ(tend) ≤ R_t`, and `Q(2+2α)/tend² ≤ R_t`, `P_bad/tend ≤ R_t`;
* (D1), (D6): every unit class `c < M` has its template, and `Σ_c mass = φ(M) Λ_fin`. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.BankShared.Check

/-- A class template with a tail branch. -/
structure KTmpl where
  t1 : ℚ
  pieces : List (QPiece × Cert)
  tb : ℕ

/-- The data of a k-shift bank. -/
structure KBankData where
  Q : ℕ
  M : ℕ
  α : ℚ
  a : ℕ
  shifts : List Shift
  depth : ℕ
  cF : ℕ
  Pbad : ℕ
  α0 : ℚ
  τ : ℚ
  Λ : ℚ
  α0b : ℚ
  t0 : ℚ
  Rt : ℚ
  kcat : List KBranch
  tmpls : List (ℕ × KTmpl)

namespace KBankData

variable (D : KBankData)

/-- The master offset `Q - a`. -/
def oM : ℕ := D.Q - D.a
def tS (i : ℕ) : ℕ := (shAt D.shifts i).t D.Q
def bS (j i : ℕ) : ℕ := (shAt D.shifts i).b j
def cS (i : ℕ) : ℕ := (shAt D.shifts i).c D.oM

/-- The one-lattice catalogue of the master root class `j`. -/
def cat (j : ℕ) : List Branch := D.kcat.map (KBranch.compile D.tS (D.bS j) D.cS)

end KBankData

/-- The template of the root class `j`. -/
def findK (j : ℕ) : List (ℕ × KTmpl) → Option KTmpl
  | [] => none
  | x :: l => if x.1 = j then some x.2 else findK j l

theorem findK_mem (j : ℕ) : ∀ (l : List (ℕ × KTmpl)) {T : KTmpl}, findK j l = some T → (j, T) ∈ l
  | [], _, h => by simp [findK] at h
  | x :: l, T, h => by
    unfold findK at h
    split_ifs at h with hx
    · simp only [Option.some.injEq] at h; subst h; rw [← hx]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (findK_mem j l h)

/-- The price is the constant `0`. -/
def isZero : Expr → Bool
  | .cst 0 => true
  | _ => false

theorem evalN_of_isZero {e : Expr} (h : isZero e = true) (r p m k : ℕ) : e.evalN r p m k = 0 := by
  unfold isZero at h
  split at h
  · rfl
  · exact absurd h (by decide)

/-- The rational template of a k-template. -/
def KTmpl.toQ (T : KTmpl) : QTmpl := ⟨T.t1, T.pieces⟩

/-- A shift is admissible against the master offset `oM`. -/
def shiftOK (Q oM : ℕ) (x : Shift) : Bool :=
  decide (0 < x.q) && decide (Q % x.q = 0) && decide (0 < x.o) && decide (x.o < x.q) &&
    decide (x.o ≤ x.s * oM) && decide ((x.s * oM - x.o) % x.q = 0)

/-- The tail test of the class `j` at `te = tend`. -/
def tailOK (D : KBankData) (j : ℕ) (te : ℚ) (tb : ℕ) : Bool :=
  match nth (D.cat j) tb with
  | none => false
  | some br =>
    isZero br.τ && decide (br.debit = 0) &&
    br.conds.all (fun c => decide (0 ≤ c.ell1 ((j : ℚ) / D.Q)) &&
      decide (0 < c.lv D.α ((j : ℚ) / D.Q) te) &&
      decide ((1 - c.etaLo D.Q) / c.lv D.α ((j : ℚ) / D.Q) te ≤ D.Rt)) &&
    decide (0 < te) && decide ((D.Q : ℚ) * (2 + 2 * D.α) / (te * te) ≤ D.Rt) &&
    decide ((D.Pbad : ℚ) / te ≤ D.Rt)

/-- (D2)-(D4) for the root class `j`. -/
def ktmplHead (D : KBankData) (j : ℕ) (T : KTmpl) : Bool :=
  decide (0 < T.t1) && decide (T.t1 ≤ D.t0) && chainOK T.t1 T.pieces &&
    D.shifts.all (fun x => decide (x.s * j % x.q ≠ 0)) &&
    tailOK D j (tendQ T.t1 T.pieces) T.tb && decide (tendQ T.t1 T.pieces ≤ D.τ)

/-- (D5) for the root class `j`. -/
def kpieceAll (D : KBankData) (j : ℕ) (l : List (QPiece × Cert)) : Bool :=
  l.all (fun x => pieceOK (D.cat j) D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad x.1 x.2)

def ktmplOK (D : KBankData) (j : ℕ) (T : KTmpl) : Bool := ktmplHead D j T && kpieceAll D j T.pieces

/-- The mass of the template of the class `c` (`0` when missing). -/
def kclassMass (D : KBankData) (c : ℕ) : ℚ :=
  match jOf D.Q D.a c with
  | some j => match findK j D.tmpls with
    | some T => T.toQ.mass D.α0
    | none => 0
  | none => 0

/-- (D1) and (D6). -/
def kclassOK (D : KBankData) : Bool :=
  unitAll D.M (fun c => match jOf D.Q D.a c with
      | some j => (findK j D.tmpls).isSome
      | none => false) D.M &&
    decide (unitSum D.M (kclassMass D) D.M = D.Λ * unitCount D.M D.M)

/-- The frame checks. -/
def kcheckParams (D : KBankData) : Bool :=
  decide (2 ≤ D.Q) && decide (D.Q ≤ D.Pbad) && decide (0 < D.M) && decide (D.M % D.Q = 0) &&
    decide (0 < D.a) && decide (D.a < D.Q) && decide (Nat.gcd D.a D.Q = 1) &&
    decide (0 ≤ D.α) && decide (D.α0b ≤ D.α0) && decide (0 ≤ D.α0) &&
    D.shifts.all (shiftOK D.Q D.oM)

/-- **The k-shift bank check.** -/
def kcheck (D : KBankData) : Bool :=
  kcheckParams D && D.tmpls.all (fun x => ktmplOK D x.1 x.2) && kclassOK D

/-! ### Real templates -/

theorem chain_real_cat {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ} :
    ∀ (l : List (QPiece × Cert)) (s0 : ℚ), chainOK s0 l = true →
      (∀ x ∈ l, pieceOK cat q α κ depth cF Pbad x.1 x.2 = true) →
      Chain (s0 : ℝ) (l.map (fun x => x.1.toPiece))
  | [], _, _, _ => trivial
  | x :: l, s0, h, hp => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    have hx := hp x List.mem_cons_self
    unfold pieceOK at hx
    rcases hb : nth cat x.2.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hst⟩, ha0⟩, ha1⟩, hC0⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hx
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [QPiece.toPiece, h.1]
    · show (0 : ℝ) < (x.1.s : ℝ); exact_mod_cast hs0
    · show (x.1.s : ℝ) ≤ x.1.t; exact_mod_cast hst.le
    · show (0 : ℝ) ≤ (x.1.C : ℝ); exact_mod_cast hC0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.s; exact_mod_cast ha0
    · show (0 : ℝ) ≤ (x.1.a : ℝ) + x.1.b * x.1.t; exact_mod_cast ha1
    · exact chain_real_cat l x.1.t h.2 (fun y hy => hp y (List.mem_cons_of_mem _ hy))

theorem mkTemplate_eq_of {α0 : ℚ} {T : QTmpl} (h0 : 0 ≤ α0) (h1 : 0 < T.t1) (hch : Chain (T.t1 : ℝ) T.real) :
    mkTemplate α0 T = ⟨α0, T.t1, T.real, by exact_mod_cast h0, by exact_mod_cast h1, hch⟩ := by
  unfold mkTemplate
  rw [dif_pos ⟨h0, h1, hch⟩]

theorem mass_mkTemplate_of {α0 : ℚ} {T : QTmpl} (h0 : 0 ≤ α0) (h1 : 0 < T.t1) (hch : Chain (T.t1 : ℝ) T.real) :
    (mkTemplate α0 T).mass = (T.mass α0 : ℝ) := by
  rw [mkTemplate_eq_of h0 h1 hch]
  simp only [Template.mass, QTmpl.real, QTmpl.mass]
  rw [listInt_real]; push_cast; rw [List.map_map]; rfl

theorem tend_mkTemplate_of {α0 : ℚ} {T : QTmpl} (h0 : 0 ≤ α0) (h1 : 0 < T.t1) (hch : Chain (T.t1 : ℝ) T.real) :
    (mkTemplate α0 T).tend = (tendQ T.t1 T.pieces : ℝ) := by
  rw [mkTemplate_eq_of h0 h1 hch]
  simp only [Template.tend, QTmpl.real]
  exact lastEnd_real T.pieces T.t1

/-- The template of the class `c`. -/
noncomputable def ktmplOf (D : KBankData) {M : ℕ} (c : ZMod M) : Template :=
  match jOf D.Q D.a c.val with
  | some j => match findK j D.tmpls with
    | some T => mkTemplate D.α0 T.toQ
    | none => ⟨0, 1, [], le_refl _, one_pos, trivial⟩
  | none => ⟨0, 1, [], le_refl _, one_pos, trivial⟩

section Facts

variable {D : KBankData} (hD : kcheck D = true)
include hD

theorem kcheck_params : 2 ≤ D.Q ∧ D.Q ≤ D.Pbad ∧ 0 < D.M ∧ D.M % D.Q = 0 ∧ 0 < D.a ∧ D.a < D.Q ∧
    0 ≤ D.α ∧ D.α0b ≤ D.α0 ∧ 0 ≤ D.α0 ∧ (∀ x ∈ D.shifts, shiftOK D.Q D.oM x = true) := by
  simp only [kcheck, kcheckParams, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hD
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, -⟩, -⟩ := hD
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem kcheck_class : kclassOK D = true := by
  simp only [kcheck, Bool.and_eq_true] at hD
  exact hD.2

theorem kcheck_tmpl {j : ℕ} {T : KTmpl} (h : findK j D.tmpls = some T) : ktmplOK D j T = true := by
  simp only [kcheck, Bool.and_eq_true, List.all_eq_true] at hD
  exact hD.1.2 (j, T) (findK_mem j D.tmpls h)

/-- The facts of one root-class template. -/
theorem ktmpl_facts {j : ℕ} {T : KTmpl} (h : findK j D.tmpls = some T) :
    0 < T.t1 ∧ T.t1 ≤ D.t0 ∧ chainOK T.t1 T.pieces = true ∧
    (∀ x ∈ D.shifts, x.s * j % x.q ≠ 0) ∧
    tailOK D j (tendQ T.t1 T.pieces) T.tb = true ∧ tendQ T.t1 T.pieces ≤ D.τ ∧
    (∀ x ∈ T.pieces, pieceOK (D.cat j) D.Q D.α ((j : ℚ) / D.Q) D.depth D.cF D.Pbad x.1 x.2 = true) := by
  have := kcheck_tmpl hD h
  simp only [ktmplOK, ktmplHead, kpieceAll, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem ktmpl_chain {j : ℕ} {T : KTmpl} (h : findK j D.tmpls = some T) : Chain (T.t1 : ℝ) T.toQ.real := by
  obtain ⟨-, -, hch, -, -, -, hp⟩ := ktmpl_facts hD h
  exact chain_real_cat T.pieces T.t1 hch hp

theorem kmass {j : ℕ} {T : KTmpl} (h : findK j D.tmpls = some T) :
    (mkTemplate D.α0 T.toQ).mass = (T.toQ.mass D.α0 : ℝ) :=
  mass_mkTemplate_of (T := T.toQ) (kcheck_params hD).2.2.2.2.2.2.2.2.1 (ktmpl_facts hD h).1 (ktmpl_chain hD h)

theorem ktend {j : ℕ} {T : KTmpl} (h : findK j D.tmpls = some T) :
    (mkTemplate D.α0 T.toQ).tend = (tendQ T.t1 T.pieces : ℝ) :=
  tend_mkTemplate_of (T := T.toQ) (kcheck_params hD).2.2.2.2.2.2.2.2.1 (ktmpl_facts hD h).1 (ktmpl_chain hD h)

end Facts

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.ktmpl_facts
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.kmass
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.ktend
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.evalN_of_isZero
