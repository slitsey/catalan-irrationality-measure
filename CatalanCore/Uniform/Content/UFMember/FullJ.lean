module

public import CatalanCore.Uniform.Content.UFMember.JBlock
public import CatalanCore.Uniform.Content.UFMember.Layer
public import CatalanCore.Uniform.Content.Smith.Derived

@[expose] public section

/-!
# UF member package: the Smith layer from the `J`-block of the Schur complement

Everything is now reduced to ONE frame statement per `(r, p)`, the `J`-block form of (S7):

  (`JBlockCauchy`) for the rows `Jr` and columns `Jc` of one joint type, the divided border Schur
  complement satisfies `W_{zy} = p · Hc_{zy}` (`z ∈ Jr`, `y ∈ Jc`) and `Hc mod p` factors through
  the retained poles: `Hc_{zy} ≡ Σ_{c ∈ Ret} A_{z c} B_{c y}` (the weighted Cauchy form
  `m_z m'_y Σ_c v(c)/((c-z)(c-y))` is one such factorisation).

From it (`smithWit_of_jblock`) the full matrix has a scaled-gauge three-level witness of price

  `2(|C| + m) - (m + σ + (σ - |Ret|))`,  `σ = |Jr| + |Jc| - m`,

and `smithJLayer` is the corresponding debit-1 layer for the deletion members.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform
  CatalanCore.Uniform.Content.Member

namespace CatalanCore.Uniform.Content.UFMember

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The `J`-block form of (S7) at one prime (the remaining frame obligation). -/
structure JBlockCauchy (W : Matrix κ κ (LocRing p)[X]) where
  Jr : Finset κ
  Jc : Finset κ
  Hc : Matrix κ κ (LocRing p)[X]
  hJ : ∀ z ∈ Jr, ∀ y ∈ Jc, W z y = Polynomial.C ((p : ℕ) : LocRing p) * Hc z y
  Ret : Finset (ZMod p)
  A : κ → ZMod p → RatFunc (ZMod p)
  B : ZMod p → κ → RatFunc (ZMod p)
  hcauchy : ∀ z ∈ Jr, ∀ y ∈ Jc, phiP p (Hc z y) = ∑ c ∈ Ret, A z c * B c y

/-- The `J`-block data give two-level data of `W` with `a = σ`, `b = |Ret|`. -/
theorem JBlockCauchy.twoLevel {W : Matrix κ κ (LocRing p)[X]} (J : JBlockCauchy W) :
    Nonempty (TwoLevelData (phiP p) (Polynomial.C ((p : ℕ) : LocRing p)) W
      (J.Jr.card + J.Jc.card - Fintype.card κ) J.Ret.card) := by
  refine exists_twoLevelData_of_jblock (phiP p) (phiP_eq_zero_iff p) (UFMember.phiP_lift p) W
    J.Jr J.Jc J.Hc J.hJ J.Ret.card ?_
  refine Smith.rank_le_card_of_sum J.Ret _ (fun z c => J.A z.1 c) (fun c y => J.B c y.1)
    fun z y => ?_
  simp only [Matrix.submatrix_apply, Matrix.map_apply]
  exact J.hcauchy z.1 z.2 y.1 y.2

/-- **The Smith witness of the full matrix from the `J`-block of (S7).** -/
noncomputable def smithWit_of_jblock (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (J : JBlockCauchy (schurW c xs ys (hint_of_poleData D hN hc hx hy))) :
    ThreeLevelWit p ((FullN Fr c xs ys (X : ℚ[X])).map (scaleU p)) J.Ret.card :=
  fullSmithWit D hN c xs ys hc hx hy hdist (Classical.choice J.twoLevel)

theorem smithWit_of_jblock_price (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (J : JBlockCauchy (schurW c xs ys (hint_of_poleData D hN hc hx hy))) :
    (smithWit_of_jblock D hN c xs ys hc hx hy hdist J).price =
      2 * Fintype.card (ι ⊕ κ) - (Fintype.card κ +
        ((J.Jr.card + J.Jc.card - Fintype.card κ) +
          ((J.Jr.card + J.Jc.card - Fintype.card κ) - J.Ret.card))) :=
  fullSmithWit_price D hN c xs ys hc hx hy hdist _

/-- **Smith data at `(r, p)` in frame terms**: pole data, node bounds, distinct border
residues and the `J`-block of (S7). -/
structure SmithJDatum (G : BlockGeom) (Fr : Frame) (r p : ℕ) [Fact p.Prime] where
  N : ℕ
  D : PoleData Fr p N
  hN : N < p * p
  hc : ∀ a : (G.geometry r).C, (a : ℕ) < N
  hx : ∀ i, (G.geometry r).xs i < N
  hy : ∀ j, (G.geometry r).ys j < N
  hdist : ∀ i j, (((G.geometry r).xs i : ℕ) : ZMod p) ≠ (((G.geometry r).ys j : ℕ) : ZMod p)
  J : JBlockCauchy (schurW (fun a : (G.geometry r).C => (a : ℕ)) (G.geometry r).xs
    (G.geometry r).ys (hint_of_poleData D hN hc hx hy))

/-- The Smith price of a datum: `2(|C| + m) - (m + σ + (σ - |Ret|))`. -/
def SmithJDatum.price {G : BlockGeom} {Fr : Frame} {r p : ℕ} [Fact p.Prime]
    (S : SmithJDatum G Fr r p) : ℕ :=
  2 * Fintype.card ((G.geometry r).C ⊕ Fin (G.geometry r).k) - (Fintype.card (Fin (G.geometry r).k) +
    ((S.J.Jr.card + S.J.Jc.card - Fintype.card (Fin (G.geometry r).k)) +
      ((S.J.Jr.card + S.J.Jc.card - Fintype.card (Fin (G.geometry r).k)) - S.J.Ret.card)))

/-- **The Smith layer (debit 1) from frame data and the `J`-block of (S7).** -/
noncomputable def smithJLayer {G : BlockGeom} {Fr : Frame} {depth : ℕ}
    (valid : ℕ → ℕ → Prop) (base : ℕ → ℕ → ℕ)
    (S : ∀ r p : ℕ, [Fact p.Prime] → valid r p → SmithJDatum G Fr r p)
    (hbase : ∀ r p : ℕ, ∀ [Fact p.Prime], ∀ h : valid r p, (S r p h).price ≤ base r p) :
    DebitLayer G Fr depth :=
  smithLayer valid base
    (fun r p _ h => ⟨(S r p h).J.Ret.card,
      smithWit_of_jblock (S r p h).D (S r p h).hN _ _ _ (S r p h).hc (S r p h).hx (S r p h).hy
        (S r p h).hdist (S r p h).J⟩)
    (fun r p _ h => by
      rw [smithWit_of_jblock_price]
      exact hbase r p h)

end CatalanCore.Uniform.Content.UFMember
