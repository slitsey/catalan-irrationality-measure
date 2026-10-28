module

public import CatalanCore.Uniform.Content.Hybrid.Blocks

@[expose] public section

/-!
# Fibre certificates and the block kernel they define (lane H15)

A residue fibre `x ∈ 𝔽_p` of the rows (columns) of a Loewner matrix contains at most one node per
digit `n / p`.  A `FibreCert` is the `p`-independent rational data of one fibre, indexed by digits:
the pole palette `lf`, `ee`, the exact local unit changes of basis `Lq, Lq', Pq, Pq'` and the
killed digits.  `Realizes` says that a fibre of the actual matrix has exactly this palette.
`blockKernel_of_certs` builds the H1 `BlockKernel` (global `L, P`, kill set) from one certificate
per fibre.
-/

open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.RankProducer

/-- Rational local certificate of one residue fibre, indexed by digits. -/
structure FibreCert where
  R : Finset ℕ
  C : Finset ℕ
  lf : ℕ → ℚ
  ee : ℕ → ℚ
  Lq : ℕ → ℕ → ℚ
  Lq' : ℕ → ℕ → ℚ
  Pq : ℕ → ℕ → ℚ
  Pq' : ℕ → ℕ → ℚ
  kr : Finset ℕ
  kc : Finset ℕ

namespace FibreCert

/-- The local leading block, by digits. -/
def Kc (c : FibreCert) (d e : ℕ) : ℚ :=
  if d = e then -c.ee d else (c.lf e - c.lf d) / ((e : ℚ) - d)

/-- `L K P` on digits. -/
def LKP (c : FibreCert) (d e : ℕ) : ℚ :=
  ∑ f ∈ c.R, ∑ g ∈ c.C, c.Lq d f * c.Kc f g * c.Pq g e

/-- The exact (rational) conditions on a certificate. -/
structure Ok (c : FibreCert) : Prop where
  hLL : ∀ d ∈ c.R, ∀ e ∈ c.R, ∑ f ∈ c.R, c.Lq d f * c.Lq' f e = if d = e then 1 else 0
  hPP : ∀ d ∈ c.C, ∀ e ∈ c.C, ∑ f ∈ c.C, c.Pq d f * c.Pq' f e = if d = e then 1 else 0
  kr_sub : c.kr ⊆ c.R
  kc_sub : c.kc ⊆ c.C
  hrow : ∀ d ∈ c.kr, ∀ e ∈ c.C, c.LKP d e = 0
  hcol : ∀ d ∈ c.R, ∀ e ∈ c.kc, c.LKP d e = 0

/-- `p`-integrality of all the data used. -/
structure Integral (p : ℕ) [Fact p.Prime] (c : FibreCert) : Prop where
  lq : ∀ d ∈ c.R, ∀ e ∈ c.R, c.Lq d e ∈ S p ∧ c.Lq' d e ∈ S p
  pq : ∀ d ∈ c.C, ∀ e ∈ c.C, c.Pq d e ∈ S p ∧ c.Pq' d e ∈ S p

end FibreCert

section Lift

variable {p : ℕ} [Fact p.Prime]

lemma liftQ_mul {x y : ℚ} (hx : x ∈ S p) (hy : y ∈ S p) :
    liftQ p (x * y) = liftQ p x * liftQ p y := by
  apply Subtype.ext
  rw [liftQ_val ((S p).mul_mem hx hy)]
  show x * y = (liftQ p x : ℚ) * (liftQ p y : ℚ)
  rw [liftQ_val hx, liftQ_val hy]

lemma liftQ_add {x y : ℚ} (hx : x ∈ S p) (hy : y ∈ S p) :
    liftQ p (x + y) = liftQ p x + liftQ p y := by
  apply Subtype.ext
  rw [liftQ_val ((S p).add_mem hx hy)]
  show x + y = (liftQ p x : ℚ) + (liftQ p y : ℚ)
  rw [liftQ_val hx, liftQ_val hy]

lemma liftQ_zero : liftQ p 0 = 0 := by
  apply Subtype.ext
  rw [liftQ_val (S p).zero_mem]; rfl

lemma liftQ_one : liftQ p 1 = 1 := by
  apply Subtype.ext
  rw [liftQ_val (S p).one_mem]; rfl

lemma liftQ_sum {α : Type*} (s : Finset α) (f : α → ℚ) (h : ∀ a ∈ s, f a ∈ S p) :
    liftQ p (∑ a ∈ s, f a) = ∑ a ∈ s, liftQ p (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [liftQ_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      liftQ_add (h a (Finset.mem_insert_self _ _))
        ((S p).sum_mem fun b hb => h b (Finset.mem_insert_of_mem hb)),
      ih fun b hb => h b (Finset.mem_insert_of_mem hb)]

/-- A sum over the elements of a fibre, whose digits are injective and fill `R`, is the sum over `R`. -/
lemma sum_digits {α : Type*} [Fintype α] (dg : α → ℕ) (R : Finset ℕ)
    (hinj : Function.Injective dg) (hR : ∀ d, d ∈ R ↔ ∃ l, dg l = d)
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) : ∑ l, g (dg l) = ∑ d ∈ R, g d := by
  classical
  rw [← Finset.sum_image (f := g) (s := (Finset.univ : Finset α)) (g := dg)
    (fun x _ y _ h => hinj h)]
  congr 1
  ext d
  simp [hR]

end Lift


section Realize

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {B : ℕ} {f e : ℕ → ℚ}

/-- Row fibre of a node map. -/
abbrev TrOf (a : ι → ℕ) (p : ℕ) (x : ZMod p) := {i : ι // (a i : ZMod p) = x}

/-- Rows identified with `Σ x, Tr x`. -/
def erOf (a : ι → ℕ) (p : ℕ) : ι ≃ Σ x : ZMod p, TrOf a p x :=
  (Equiv.sigmaFiberEquiv (fun i => (a i : ZMod p))).symm

lemma erOf_fst (a : ι → ℕ) (i : ι) : (erOf a p i).1 = (a i : ZMod p) := rfl

lemma erOf_symm (a : ι → ℕ) (x : ZMod p) (t : TrOf a p x) : (erOf a p).symm ⟨x, t⟩ = t.1 := rfl

/-- The fibre `x` of the actual matrix has the palette of `c`. -/
structure Realizes (PS : PoleSplit p B f e) (a b : ι → ℕ) (x : ZMod p) (c : FibreCert) : Prop where
  r_mem : ∀ i, (a i : ZMod p) = x → a i / p ∈ c.R
  r_cov : ∀ d ∈ c.R, ∃ i, (a i : ZMod p) = x ∧ a i / p = d
  c_mem : ∀ j, (b j : ZMod p) = x → b j / p ∈ c.C
  c_cov : ∀ d ∈ c.C, ∃ j, (b j : ZMod p) = x ∧ b j / p = d
  lf_r : ∀ i, (a i : ZMod p) = x → PS.Lf (a i) = c.lf (a i / p)
  lf_c : ∀ j, (b j : ZMod p) = x → PS.Lf (b j) = c.lf (b j / p)
  ee_r : ∀ i, (a i : ZMod p) = x → PS.E (a i) = c.ee (a i / p)

lemma node_eq_of_digit {n m : ℕ} (h : (n : ZMod p) = (m : ZMod p)) (hd : n / p = m / p) : n = m := by
  have hm := natCast_eq_of_mod h
  have h1 := Nat.div_add_mod n p
  have h2 := Nat.div_add_mod m p
  rw [hd, hm] at h1
  omega

lemma Kq_eq_Kc {PS : PoleSplit p B f e} {a b : ι → ℕ} {x : ZMod p} {c : FibreCert}
    (hR : Realizes PS a b x c) {i j : ι} (hi : (a i : ZMod p) = x) (hj : (b j : ZMod p) = x) :
    PS.Kq a b i j = c.Kc (a i / p) (b j / p) := by
  have hij : (a i : ZMod p) = (b j : ZMod p) := hi.trans hj.symm
  unfold PoleSplit.Kq FibreCert.Kc
  by_cases h1 : a i = b j
  · have hd : a i / p = b j / p := by rw [h1]
    rw [if_pos h1, if_pos hd, hR.ee_r i hi, hd]
  · have hd : ¬ a i / p = b j / p := fun hd => h1 (node_eq_of_digit hij hd)
    rw [if_neg h1, if_pos hij, if_neg hd, hR.lf_r i hi, hR.lf_c j hj]
    rw [digitDiff, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]

end Realize

end CatalanCore.Uniform.Content.RankProducer
