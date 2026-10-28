module

public import CatalanCore.Uniform.Content.UFFamily.Entries

@[expose] public section

/-!
# UF families: `Realizes` for every joint type (lane H10)

A **joint type** (`JType`) is the list of block-digit/floor pairs `(⌊c/p⌋, ⌊(q c - o)/p⌋)` of the core
nodes of one residue fiber, plus the same pair for the border node (zone).  `mkFib` turns a joint
type into the integer bordered-fiber data (`IntFib`) by `Dn`-scaling the rational entries of `Entries`,
with `Closed.Cval` as the prefix residues; no value is a literal.

`nodeFib_realizes` : the evaluated fiber `nodeFib (evP p u₀) Fr c Q t` of the lift IS realised by
`mkFib J … Dn` (`FibD.Realizes`), for every `p` with `N < p²`, `q < p`, as soon as the nodes of the
fiber are listed by `J` and `Dn` clears all denominators (`IntOK`, a kernel-decidable check).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily

/-- A joint type: the pairs `(⌊c/p⌋, ⌊(q c - o)/p⌋)` of the fiber's core nodes and of the border node. -/
structure JType where
  nodes : List (ℕ × ℕ)
  zone : ℕ × ℕ

namespace JType

def node (J : JType) (i : ℕ) : ℕ × ℕ := J.nodes.getD i (0, 0)

end JType

section Data

variable (q o r : ℕ) (nrm : ℚ) (u0 : ℤ) (J : JType)

/-- Prefix residue `V` of a node, as a rational. -/
def Lq (n : ℕ × ℕ) : ℚ := Cval 1 q o r n.1 n.2

/-- Prefix residue `W` of a node, as a rational. -/
def Eq' (n : ℕ × ℕ) : ℚ := Cval 2 q o r n.1 n.2

/-- Entry `(i, j)` of the fiber block at `X = u₀`. -/
def entM (i j : ℕ) : ℚ :=
  if i = j then (u0 : ℚ) + (-nrm⁻¹) * Eq' q o r (J.node i)
  else nrm⁻¹ * (Lq q o r (J.node j) - Lq q o r (J.node i)) *
    (((J.node j).1 : ℚ) - ((J.node i).1 : ℚ))⁻¹

/-- Border vector. -/
def entS (i : ℕ) : ℚ :=
  nrm⁻¹ * (Lq q o r (J.node i) - Lq q o r J.zone) * (((J.node i).1 : ℚ) - (J.zone.1 : ℚ))⁻¹

/-- Prefix vector. -/
def entU (i : ℕ) : ℚ := Lq q o r (J.node i)

/-- Border prefix. -/
def entZ : ℚ := Lq q o r J.zone

/-- The integer data of a joint type, scaled by `Dn`. -/
def mkFib (Dn : ℤ) : IntFib J.nodes.length where
  M := (List.range J.nodes.length).map fun i => (List.range J.nodes.length).map fun j =>
    ((Dn : ℚ) * entM q o r nrm u0 J i j).num
  s := (List.range J.nodes.length).map fun i => ((Dn : ℚ) * entS q o r nrm J i).num
  u := (List.range J.nodes.length).map fun i => ((Dn : ℚ) * entU q o r J i).num
  z := ((Dn : ℚ) * entZ q o r J).num

/-- `Dn` clears every denominator. -/
def IntOK (Dn : ℤ) : Prop :=
  (∀ i < J.nodes.length, ∀ j < J.nodes.length, ((Dn : ℚ) * entM q o r nrm u0 J i j).den = 1) ∧
  (∀ i < J.nodes.length, ((Dn : ℚ) * entS q o r nrm J i).den = 1) ∧
  (∀ i < J.nodes.length, ((Dn : ℚ) * entU q o r J i).den = 1) ∧
  ((Dn : ℚ) * entZ q o r J).den = 1

instance (Dn : ℤ) : Decidable (IntOK q o r nrm u0 J Dn) := by unfold IntOK; infer_instance

variable {q o r nrm u0 J}

theorem mkFib_Mf (Dn : ℤ) {i j : ℕ} (hi : i < J.nodes.length) (hj : j < J.nodes.length) :
    (mkFib q o r nrm u0 J Dn).Mf i j = ((Dn : ℚ) * entM q o r nrm u0 J i j).num := by
  simp [IntFib.Mf, mkFib, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi, hj]

theorem mkFib_sf (Dn : ℤ) {i : ℕ} (hi : i < J.nodes.length) :
    (mkFib q o r nrm u0 J Dn).sf i = ((Dn : ℚ) * entS q o r nrm J i).num := by
  simp [IntFib.sf, mkFib, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

theorem mkFib_uf (Dn : ℤ) {i : ℕ} (hi : i < J.nodes.length) :
    (mkFib q o r nrm u0 J Dn).uf i = ((Dn : ℚ) * entU q o r J i).num := by
  simp [IntFib.uf, mkFib, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, hi]

end Data

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {q o : ℕ}

theorem scaled_cast {x : ℚ} {y : ZMod p} (hx : Good p x y) (Dn : ℤ) (hden : ((Dn : ℚ) * x).den = 1) :
    (Dn : ZMod p) * y = (((Dn : ℚ) * x).num : ZMod p) := by
  have g := (Good.intCast (ℓ := p) Dn).mul hx
  have h1 : (((Dn : ℚ) * x).num : ℚ) = (Dn : ℚ) * x := Rat.coe_int_num_of_den_eq_one hden
  have g2 : Good p ((((Dn : ℚ) * x).num : ℤ) : ℚ) ((((Dn : ℚ) * x).num : ℤ) : ZMod p) :=
    Good.intCast _
  have g3 := g2.congr' h1
  exact g.2.symm.trans g3.2

theorem digit_ne {a b : ℕ} (hab : a ≠ b) (hmod : (a : ZMod p) = (b : ZMod p))
    (ha : a < p * p) (hb : b < p * p) :
    ((b / p : ℕ) : ZMod p) - ((a / p : ℕ) : ZMod p) ≠ 0 := by
  have hp := (Fact.out : p.Prime)
  intro h
  rw [sub_eq_zero] at h
  have h1 : b / p % p = a / p % p := (ZMod.natCast_eq_natCast_iff' _ _ p).1 h
  have h2 : a % p = b % p := (ZMod.natCast_eq_natCast_iff' _ _ p).1 hmod
  have hap : a / p < p := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
  have hbp : b / p < p := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hb)
  rw [Nat.mod_eq_of_lt hap, Nat.mod_eq_of_lt hbp] at h1
  apply hab
  rw [← Nat.div_add_mod a p, ← Nat.div_add_mod b p, h1, h2]

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **`Realizes`, generically.** -/
theorem nodeFib_realizes (T : TwoTermData Fr q o) (hqp : q < p) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0)
    (c : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (t : ℕ) (ht : t < N) (u0 : ℤ) (J : JType) (Dn : ℤ)
    (g : Fin J.nodes.length → ι) (hg : Function.Injective g)
    (hcol : ∀ i, ((c (g i) : ℕ) : ZMod p) = ((t : ℕ) : ZMod p))
    (hsurj : ∀ a, ((c a : ℕ) : ZMod p) = ((t : ℕ) : ZMod p) → ∃ i, g i = a)
    (hcinj : Function.Injective c) (hne : ∀ i, c (g i) ≠ t)
    (hnode : ∀ i : Fin J.nodes.length, J.node i = (c (g i) / p, (q * c (g i) - o) / p))
    (hzone : J.zone = (t / p, (q * t - o) / p))
    (hint : IntOK q o (p % q) Fr.norm u0 J Dn) :
    (nodeFib (evP p (u0 : ZMod p)) Fr c
      (sLift c xs ys (hint_of_poleData (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp hc hx
        hy)).toBlocks₁₁ t).Realizes Dn (mkFib q o (p % q) Fr.norm u0 J Dn) := by
  set D := twoTermPoleData T hNp.le hsq hnorm hnorm0 with hD
  have hVc : ∀ a, a < N → Good p (Lq q o (p % q) (a / p, (q * a - o) / p)) (D.V a) :=
    fun a ha => good_V T hqp hNp.le hsq hnorm hnorm0 ha
  have hWc : ∀ a, a < N → Good p (Eq' q o (p % q) (a / p, (q * a - o) / p)) (D.W a) :=
    fun a ha => good_W T hqp hNp.le hsq hnorm hnorm0 ha
  have gn := (good_red hnorm).inv hnorm0
  have hN2 : ∀ a, a < N → a < p * p := fun a ha => lt_trans ha hNp
  -- the labelling
  have hf : Function.Bijective (fun i : Fin J.nodes.length =>
      (⟨g i, hcol i⟩ : {i : ι // ((c i : ℕ) : ZMod p) = ((t : ℕ) : ZMod p)})) := by
    constructor
    · intro i j h
      exact hg (congrArg Subtype.val h)
    · intro a
      obtain ⟨i, hi⟩ := hsurj a.1 a.2
      exact ⟨i, Subtype.ext hi⟩
  set e := (Equiv.ofBijective _ hf).symm with he
  have hge : ∀ i, g (e i) = i.1 := fun i => by
    have := (Equiv.ofBijective _ hf).apply_symm_apply i
    exact congrArg Subtype.val this
  -- entries
  have hM : ∀ a b : Fin J.nodes.length, (Dn : ZMod p) * evP p (u0 : ZMod p)
      ((sLift c xs ys (hint_of_poleData D hNp hc hx hy)).toBlocks₁₁ (g a) (g b)) =
        ((mkFib q o (p % q) Fr.norm u0 J Dn).Mf a b : ZMod p) := by
    intro a b
    rw [mkFib_Mf Dn a.2 b.2]
    by_cases hab : a = b
    · subst hab
      have hd := good_Mn_diag D (hc (g a))
      rw [evP_core_diag D hNp c xs ys hc hx hy (u0 : ZMod p) hd]
      have gE := hWc _ (hc (g a))
      rw [← hnode a] at gE
      have gx : Good p (entM q o (p % q) Fr.norm u0 J a a) ((u0 : ZMod p) +
          -(red p Fr.norm)⁻¹ * D.W (c (g a))) := by
        unfold entM
        rw [if_pos rfl]
        exact (Good.intCast u0).add (gn.neg.mul gE)
      exact scaled_cast gx Dn (hint.1 a a.2 a a.2)
    · have hab' : (a : ℕ) ≠ (b : ℕ) := fun h => hab (Fin.ext h)
      have hcab : c (g a) ≠ c (g b) := fun h => hab (hg (hcinj h))
      have hmod : ((c (g a) : ℕ) : ZMod p) = ((c (g b) : ℕ) : ZMod p) := (hcol a).trans (hcol b).symm
      have ho := good_Mn_off D hNp hcab hmod (hc _) (hc _)
      rw [evP_core_off D hNp c xs ys hc hx hy (u0 : ZMod p) (fun h => hab (hg h)) ho]
      have hA := hVc _ (hc (g a))
      have hB := hVc _ (hc (g b))
      rw [← hnode a] at hA
      rw [← hnode b] at hB
      have dA : Good p (((J.node a).1 : ℕ) : ℚ) (((c (g a) / p : ℕ) : ZMod p)) := by
        rw [hnode a]; exact Good.natCast _
      have dB : Good p (((J.node b).1 : ℕ) : ℚ) (((c (g b) / p : ℕ) : ZMod p)) := by
        rw [hnode b]; exact Good.natCast _
      have hne0 := digit_ne hcab hmod (hN2 _ (hc _)) (hN2 _ (hc _))
      have gx : Good p (entM q o (p % q) Fr.norm u0 J a b) ((red p Fr.norm)⁻¹ *
          (D.V (c (g b)) - D.V (c (g a))) *
            (((c (g b) / p : ℕ) : ZMod p) - ((c (g a) / p : ℕ) : ZMod p))⁻¹) := by
        unfold entM
        rw [if_neg hab']
        exact (gn.mul (hB.sub hA)).mul ((dB.sub dA).inv hne0)
      exact scaled_cast gx Dn (hint.1 a a.2 b b.2)
  have hS : ∀ a : Fin J.nodes.length, (Dn : ZMod p) * evP p (u0 : ZMod p)
      (loewRow p Fr c t (g a)) = ((mkFib q o (p % q) Fr.norm u0 J Dn).sf a : ZMod p) := by
    intro a
    rw [mkFib_sf Dn a.2]
    have hct : t ≠ c (g a) := fun h => hne a h.symm
    have hmod : ((t : ℕ) : ZMod p) = ((c (g a) : ℕ) : ZMod p) := (hcol a).symm
    have ho := good_Mn_off D hNp hct hmod ht (hc _)
    rw [evP_loewRow c t (u0 : ZMod p) (g a) ho]
    have hA := hVc _ (hc (g a))
    have hZ := hVc _ ht
    rw [← hnode a] at hA
    rw [← hzone] at hZ
    have dA : Good p (((J.node a).1 : ℕ) : ℚ) (((c (g a) / p : ℕ) : ZMod p)) := by
      rw [hnode a]; exact Good.natCast _
    have dZ : Good p ((J.zone.1 : ℕ) : ℚ) (((t / p : ℕ) : ZMod p)) := by
      rw [hzone]; exact Good.natCast _
    have hne0 := digit_ne hct hmod (hN2 _ ht) (hN2 _ (hc _))
    have gx : Good p (entS q o (p % q) Fr.norm J a) ((red p Fr.norm)⁻¹ *
        (D.V (c (g a)) - D.V t) *
          (((c (g a) / p : ℕ) : ZMod p) - ((t / p : ℕ) : ZMod p))⁻¹) := by
      unfold entS
      exact (gn.mul (hA.sub hZ)).mul ((dA.sub dZ).inv hne0)
    exact scaled_cast gx Dn (hint.2.1 a a.2)
  have hU : ∀ a : Fin J.nodes.length, (Dn : ZMod p) * evP p (u0 : ZMod p)
      (PF1 p Fr (c (g a))) = ((mkFib q o (p % q) Fr.norm u0 J Dn).uf a : ZMod p) := by
    intro a
    rw [mkFib_uf Dn a.2, evP_PF1 (u0 : ZMod p) _ (good_PF1 D (hc _))]
    have hA := hVc _ (hc (g a))
    rw [← hnode a] at hA
    exact scaled_cast hA Dn (hint.2.2.1 a a.2)
  have hZ : (Dn : ZMod p) * evP p (u0 : ZMod p) (PF1 p Fr t) =
      ((mkFib q o (p % q) Fr.norm u0 J Dn).z : ZMod p) := by
    rw [evP_PF1 (u0 : ZMod p) _ (good_PF1 D ht)]
    have hZ := hVc _ ht
    rw [← hzone] at hZ
    exact scaled_cast hZ Dn hint.2.2.2
  refine ⟨e, fun i j => ?_, fun i => ?_, fun i => ?_, hZ⟩
  · have := hM (e i) (e j)
    rw [hge i, hge j] at this
    exact this
  · have := hS (e i)
    rw [hge i] at this
    exact this
  · have := hU (e i)
    rw [hge i] at this
    exact this

end CatalanCore.Uniform.Content.UFFamily
