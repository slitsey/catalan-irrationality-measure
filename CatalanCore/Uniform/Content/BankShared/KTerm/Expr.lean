module

public import CatalanCore.Uniform.Content.BankShared.Check.Cover
public import CatalanCore.Uniform.Content.BankShared.Inst.KShift

@[expose] public section
set_option Elab.async false

/-! # Layer prices with several pole indices, compiled to the one-lattice class (lane K)

`KExpr`: the expression class `𝔈` of C1 (`Check.Expr`) with one variable `vk i` per pole shift; `KCond`: a
validity condition with one coefficient per shift (`ck : List ℤ`); `KBranch`: price, conditions, debit.

**Compilation.**  Given, per shift `i`, naturals `t i, b i, c i` with `k_i = t_i k - (b_i p + c_i)` (the master
lattice of `Inst.KShift`), `KExpr.compile` replaces `vk i` by the one-lattice expression
`t_i vk ∸ (b_i vp + c_i)` and `KCond.compile` substitutes the affine form exactly (no truncation):

* `evalN_compile`: the compiled price at `(r, p, m, k)` is the k-shift price at `(r, p, m, kv)`,
  `kv i = t_i k - (b_i p + c_i)`;
* `holds_compile`: the compiled condition holds iff the k-shift condition holds at `kv` (when `b_i p + c_i ≤ t_i k`).

The homogenised profile and the error constant of a compiled branch are those of `Check.Expr` (κ = j/Q of the
master class), so `Check.pieceOK` and Theorem B (`Check.piece_sound`) apply verbatim. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check

/-- Expressions of the class `𝔈` in `r, p, m` and the pole indices `k_0, k_1, …`. -/
inductive KExpr where
  | vr
  | vp
  | vm
  | vk (i : ℕ)
  | cst (c : ℕ)
  | add (a b : KExpr)
  | smul (c : ℕ) (a : KExpr)
  | tsub (a b : KExpr)
  | mn (a b : KExpr)
  | mx (a b : KExpr)
  | dist (a : KExpr)
  | ap
  | sp

namespace KExpr

/-- The integer value at `(r, p, m, k)`, `k i` the pole index of shift `i`. -/
def evalN (r p m : ℕ) (k : ℕ → ℕ) : KExpr → ℕ
  | vr => r
  | vp => p
  | vm => m
  | vk i => k i
  | cst c => c
  | add a b => evalN r p m k a + evalN r p m k b
  | smul c a => c * evalN r p m k a
  | tsub a b => evalN r p m k a - evalN r p m k b
  | mn a b => min (evalN r p m k a) (evalN r p m k b)
  | mx a b => max (evalN r p m k a) (evalN r p m k b)
  | dist a => min (evalN r p m k a % p) (p - evalN r p m k a % p)
  | ap => p * (r / p)
  | sp => r % p

/-- Replace every `vk i` by the one-lattice expression `σ i`. -/
def compile (σ : ℕ → Expr) : KExpr → Expr
  | vr => .vr
  | vp => .vp
  | vm => .vm
  | vk i => σ i
  | cst c => .cst c
  | add a b => .add (compile σ a) (compile σ b)
  | smul c a => .smul c (compile σ a)
  | tsub a b => .tsub (compile σ a) (compile σ b)
  | mn a b => .mn (compile σ a) (compile σ b)
  | mx a b => .mx (compile σ a) (compile σ b)
  | dist a => .dist (compile σ a)
  | ap => .ap
  | sp => .sp

theorem evalN_compile (σ : ℕ → Expr) (r p m k : ℕ) (e : KExpr) :
    (e.compile σ).evalN r p m k = e.evalN r p m (fun i => (σ i).evalN r p m k) := by
  induction e with
  | vr => rfl
  | vp => rfl
  | vm => rfl
  | vk i => rfl
  | cst c => rfl
  | add a b iha ihb => simp only [compile, evalN, Expr.evalN, iha, ihb]
  | smul c a iha => simp only [compile, evalN, Expr.evalN, iha]
  | tsub a b iha ihb => simp only [compile, evalN, Expr.evalN, iha, ihb]
  | mn a b iha ihb => simp only [compile, evalN, Expr.evalN, iha, ihb]
  | mx a b iha ihb => simp only [compile, evalN, Expr.evalN, iha, ihb]
  | dist a iha => simp only [compile, evalN, Expr.evalN, iha]
  | ap => rfl
  | sp => rfl

end KExpr

/-- The one-lattice expression `t vk ∸ (b vp + c)` of a transported pole index. -/
def subE (t b c : ℕ) : Expr := .tsub (.smul t .vk) (.add (.smul b .vp) (.cst c))

theorem evalN_subE (t b c r p m k : ℕ) : (subE t b c).evalN r p m k = t * k - (b * p + c) := rfl

/-! ### Conditions -/

/-- `Σ_i l_i f(i)`. -/
def dot : List ℤ → (ℕ → ℤ) → ℤ
  | [], _ => 0
  | a :: l, f => a * f 0 + dot l (fun i => f (i + 1))

theorem dot_affine : ∀ (l : List ℤ) (f g h : ℕ → ℤ) (x y : ℤ),
    dot l (fun i => f i * x - (g i * y + h i)) = dot l f * x - (dot l g * y + dot l h)
  | [], _, _, _, _, _ => by simp [dot]
  | a :: l, f, g, h, x, y => by
    have ih : dot l (fun i => f (i + 1) * x - (g (i + 1) * y + h (i + 1))) =
        dot l (fun i => f (i + 1)) * x - (dot l (fun i => g (i + 1)) * y + dot l (fun i => h (i + 1))) :=
      dot_affine l (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => h (i + 1)) x y
    simp only [dot]
    rw [ih]
    ring

/-- A validity condition `L ≥ 0` (`strict = false`) or `L > 0`, `L = cr r + cp p + cm m + Σ ck_i k_i + c1`. -/
structure KCond where
  cr : ℤ
  cp : ℤ
  cm : ℤ
  ck : List ℤ
  c1 : ℤ
  strict : Bool

namespace KCond

def L (c : KCond) (r p m : ℕ) (k : ℕ → ℕ) : ℤ :=
  c.cr * r + c.cp * p + c.cm * m + dot c.ck (fun i => (k i : ℤ)) + c.c1

def Holds (c : KCond) (r p m : ℕ) (k : ℕ → ℕ) : Prop :=
  if c.strict then 0 < c.L r p m k else 0 ≤ c.L r p m k

/-- The one-lattice condition after `k_i = t_i k - (b_i p + c_i)`. -/
def compile (t b cc : ℕ → ℕ) (c : KCond) : Cond :=
  ⟨c.cr, c.cp - dot c.ck (fun i => (b i : ℤ)), c.cm, dot c.ck (fun i => (t i : ℤ)),
    c.c1 - dot c.ck (fun i => (cc i : ℤ)), c.strict⟩

theorem L_compile (t b cc : ℕ → ℕ) (c : KCond) (r p m k : ℕ) (h : ∀ i, b i * p + cc i ≤ t i * k) :
    (c.compile t b cc).L r p m k = c.L r p m (fun i => t i * k - (b i * p + cc i)) := by
  have e : (fun i => (((t i * k - (b i * p + cc i) : ℕ)) : ℤ)) =
      (fun i => (t i : ℤ) * k - ((b i : ℤ) * p + cc i)) := by
    funext i
    first
      | (push_cast [Nat.cast_sub (h i)]; done)
      | (push_cast [Nat.cast_sub (h i)]; ring)
  unfold Cond.L L compile
  simp only
  rw [e, dot_affine c.ck (fun i => (t i : ℤ)) (fun i => (b i : ℤ)) (fun i => (cc i : ℤ)) (k : ℤ) (p : ℤ)]
  ring

theorem holds_compile (t b cc : ℕ → ℕ) (c : KCond) (r p m k : ℕ) (h : ∀ i, b i * p + cc i ≤ t i * k) :
    (c.compile t b cc).Holds r p m k ↔ c.Holds r p m (fun i => t i * k - (b i * p + cc i)) := by
  unfold Cond.Holds Holds
  rw [L_compile t b cc c r p m k h]
  exact Iff.rfl

end KCond

/-- A k-shift branch: price, validity conditions, debit per deleted node. -/
structure KBranch where
  τ : KExpr
  conds : List KCond
  debit : ℕ

/-- The one-lattice branch. -/
def KBranch.compile (t b cc : ℕ → ℕ) (br : KBranch) : Branch :=
  ⟨br.τ.compile (fun i => subE (t i) (b i) (cc i)), br.conds.map (KCond.compile t b cc), br.debit⟩

theorem KBranch.evalN_compile (t b cc : ℕ → ℕ) (br : KBranch) (r p m k : ℕ) :
    (br.compile t b cc).τ.evalN r p m k = br.τ.evalN r p m (fun i => t i * k - (b i * p + cc i)) :=
  KExpr.evalN_compile _ r p m k br.τ


/-! ### P124: embedding a one-index catalogue in any selected shift -/

def _root_.CatalanCore.Uniform.Content.BankShared.Check.Expr.liftK
    (idx : ℕ) : Expr → KExpr
  | .vr => .vr
  | .vp => .vp
  | .vm => .vm
  | .vk => .vk idx
  | .cst c => .cst c
  | .add a b => .add (a.liftK idx) (b.liftK idx)
  | .smul c a => .smul c (a.liftK idx)
  | .tsub a b => .tsub (a.liftK idx) (b.liftK idx)
  | .mn a b => .mn (a.liftK idx) (b.liftK idx)
  | .mx a b => .mx (a.liftK idx) (b.liftK idx)
  | .dist a => .dist (a.liftK idx)
  | .ap => .ap
  | .sp => .sp

theorem evalN_liftK (e : Expr) (idx r p m : ℕ) (kv : ℕ → ℕ) :
    (e.liftK idx).evalN r p m kv = e.evalN r p m (kv idx) := by
  induction e <;> simp_all [Expr.liftK, KExpr.evalN, Expr.evalN]

def _root_.CatalanCore.Uniform.Content.BankShared.Check.Cond.liftK
    (idx : ℕ) (cd : Cond) : KCond :=
  ⟨cd.cr, cd.cp, cd.cm, List.replicate idx 0 ++ [cd.ck], cd.c1, cd.strict⟩

theorem dot_single (idx : ℕ) (a : ℤ) (f : ℕ → ℤ) :
    dot (List.replicate idx 0 ++ [a]) f = a * f idx := by
  induction idx generalizing f with
  | zero => simp [dot]
  | succ idx ih =>
      simpa [List.replicate_succ, dot] using ih (fun j => f (j + 1))

theorem holds_liftK (cd : Cond) (idx r p m : ℕ) (kv : ℕ → ℕ) :
    (cd.liftK idx).Holds r p m kv ↔ cd.Holds r p m (kv idx) := by
  simp [Cond.liftK, KCond.Holds, Cond.Holds, KCond.L, Cond.L, dot_single]

def _root_.CatalanCore.Uniform.Content.BankShared.Check.Branch.liftK
    (idx : ℕ) (br : Branch) : KBranch :=
  ⟨br.τ.liftK idx, br.conds.map (Cond.liftK idx), br.debit⟩

theorem compile_liftK_err (e : Expr) (idx : ℕ) (t b cc : ℕ → ℕ)
    (ht : t idx = 1) (hb : b idx = 0) (hc : cc idx = 0) (ε : ℚ) :
    ((e.liftK idx).compile (fun i => subE (t i) (b i) (cc i))).err ε = e.err ε := by
  induction e <;>
    simp_all [Expr.liftK, KExpr.compile, subE, Expr.err]

theorem compile_liftK_evalR (e : Expr) (idx : ℕ) (t b cc : ℕ → ℕ)
    (ht : t idx = 1) (hb : b idx = 0) (hc : cc idx = 0)
    (keep : Bool) (R P M K : ℝ) (hK : 0 ≤ K) :
    ((e.liftK idx).compile (fun i => subE (t i) (b i) (cc i))).evalR keep R P M K =
      e.evalR keep R P M K := by
  induction e <;>
    simp_all [Expr.liftK, KExpr.compile, subE, Expr.evalR, max_eq_left hK]

theorem compile_liftK_prof (e : Expr) (idx : ℕ) (t b cc : ℕ → ℕ)
    (ht : t idx = 1) (hb : b idx = 0) (hc : cc idx = 0)
    (α κ : ℚ) (θ : ℝ) (hκθ : 0 ≤ (κ : ℝ) * θ) :
    prof α κ θ ((e.liftK idx).compile (fun i => subE (t i) (b i) (cc i))) =
      prof α κ θ e :=
  compile_liftK_evalR e idx t b cc ht hb hc false 1 θ α ((κ : ℝ) * θ) hκθ

theorem compile_liftK_cond (cd : Cond) (idx : ℕ) (t b cc : ℕ → ℕ)
    (ht : t idx = 1) (hb : b idx = 0) (hc : cc idx = 0) :
    (cd.liftK idx).compile t b cc = cd := by
  cases cd
  simp [Cond.liftK, KCond.compile, dot_single, ht, hb, hc]


end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KExpr.evalN_compile
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KCond.L_compile
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KCond.holds_compile
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.KBranch.evalN_compile

#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.evalN_liftK
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.compile_liftK_prof
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.compile_liftK_err
