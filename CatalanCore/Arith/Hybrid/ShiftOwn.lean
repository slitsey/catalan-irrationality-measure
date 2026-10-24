module
public import CatalanCore.Arith.Hybrid.ShiftZRed
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # Own-chain transport modulo `p²`

For two zone nodes `x ≤ x'` of one cut-free interval the chains correspond (`chainTransport`), the
exact pole data agree, and the actual chain matrices and rows agree modulo `p²`
(`poleScaledEntry_second_order`).  Hence the first-order partners `Sr_x`, `Sr_x'` agree modulo `p²`
on corresponding chain nodes (`Sr_transport2`), by cancelling the chain matrix, which has a unit
determinant. -/

section Level2
variable {p : ℕ} [Fact p.Prime]

lemma gn_C_le_of_good_zero {y : ℚ} (h : Good p y 0) : gn p (C y) ≤ (p : ℝ)⁻¹ := by
  have hy : y ∈ LocRing p := h.mem
  have h0 : redQ p ⟨y, hy⟩ = 0 := by
    rw [redQ_apply]; exact h.eq
  obtain ⟨b, hb⟩ := (redQ_eq_zero_iff p _).1 h0
  have hy2 : y = (p : ℚ) * (b : ℚ) := by
    have := congrArg Subtype.val hb
    simpa using this
  rw [hy2, map_mul, gn_mul, gn_C, gn_C, padicNorm.padicNorm_p_of_prime]
  have hb1 : padicNorm p (b : ℚ) ≤ 1 := (mem_locRing_iff_padicNorm (p := p)).1 b.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  push_cast
  calc ((p : ℝ)⁻¹) * (padicNorm p (b : ℚ) : ℝ) ≤ ((p : ℝ)⁻¹) * 1 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) (by positivity)
    _ = (p : ℝ)⁻¹ := mul_one _

/-- `p²`-level cancellation of a unit-determinant matrix. -/
lemma row_gn_of_mul {I : Type} [Fintype I] [DecidableEq I] (M : Matrix I I ℚ[X])
    (hM : ∀ i j, LemmaE.Int1 p (M i j)) (hd : gn p M.det = 1) (v : I → ℚ[X]) (ε : ℝ)
    (hε : 0 ≤ ε) (h : ∀ i, gn p ((v ᵥ* M) i) ≤ ε) (i : I) : gn p (v i) ≤ ε := by
  have H : M.det • v = (v ᵥ* M) ᵥ* M.adjugate := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hi := congrFun H i
  have hb : gn p (((v ᵥ* M) ᵥ* M.adjugate) i) ≤ ε := by
    simp only [Matrix.vecMul, dotProduct]
    apply LemmaE.gn_sum_le_const _ _ _ hε
    intro j _
    rw [gn_mul]
    calc gn p ((v ᵥ* M) j) * gn p (M.adjugate j i) ≤ ε * 1 :=
          mul_le_mul (h j) (LemmaE.adj_int1 hM j i) (gn_nonneg p _) hε
      _ = ε := mul_one _
  rw [← hi] at hb
  simpa [Pi.smul_apply, smul_eq_mul, gn_mul, hd] using hb

end Level2


section Transport2
open ChainClasses ChainModel LemmaE
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- Exact pole data along a chain transport inside a cut-free interval. -/
theorem chainTransport_pole (hL : LamData Fr o) {r x x' : ℕ} (hxx : x ≤ x')
    (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (x:ℤ) (x':ℤ))
    (i : ChainIndex p r x) :
    ((chainNode (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i)).val : ℤ) =
        ((chainNode i).val : ℤ) + ((x':ℤ) - x) ∧
      polePrefix Fr p o (chainNode i).val =
        polePrefix Fr p o (chainNode (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i)).val ∧
      poleSquarePrefix Fr p o (chainNode i).val =
        poleSquarePrefix Fr p o (chainNode (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i)).val ∧
      polePrefix Fr p o x = polePrefix Fr p o x' := by
  set e : ChainIndex p r x ≃ ChainIndex p r x' :=
    chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc with he
  have hshift : ((chainNode (e i)).val : ℤ) = ((chainNode i).val : ℤ) + ((x':ℤ) - x) :=
    chainNode_transport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i
  have hperiod : ∀ t j : ℤ, Singular (p:ℤ) (o:ℤ) (t + j * p) ↔ Singular (p:ℤ) (o:ℤ) t :=
    singular_periodic _ _
  have hnc_i : NoCut (Singular (p:ℤ) (o:ℤ)) ((chainNode i).val : ℤ) ((chainNode (e i)).val : ℤ) := by
    have H := noCut_translate (i := i.val) hperiod hnc
    have h1 : ((chainNode i).val : ℤ) = (x:ℤ) - i.val * p := chainNode_cast i
    have h2 : ((chainNode (e i)).val : ℤ) = (x':ℤ) - i.val * p := chainNode_cast (e i)
    rw [h1, h2]; exact H
  have hle : (chainNode i).val ≤ (chainNode (e i)).val := by
    have hxx' : (x:ℤ) ≤ x' := by exact_mod_cast hxx
    omega
  have h0 : NoCut (Singular (p:ℤ) (o:ℤ)) (x:ℤ) (x':ℤ) := fun t h1 h2 hs => hnc t h1 h2 (Or.inl hs)
  exact ⟨hshift, polePrefix_nocut hL hle hnc_i, poleSquarePrefix_nocut hL hle hnc_i,
    polePrefix_nocut hL hxx h0⟩

lemma gn_C_pole_diff (hL : LamData Fr o) (hp : 5≤p) {a b : ℕ} (ha : a<p*p) (hb : b<p*p)
    (hc : a%p=b%p) :
    gn p (C ((p:ℚ)^2 * Fr.Mn a b - poleScaledEntry Fr p o a b)) ≤ ((p:ℝ)⁻¹)^2 := by
  have H := gn_C_le_of_good_zero (poleScaledEntry_second_order hL hp ha hb hc)
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : (p:ℚ)^2 * Fr.Mn a b - poleScaledEntry Fr p o a b =
      (p:ℚ) * (((p:ℚ)^2 * Fr.Mn a b - poleScaledEntry Fr p o a b) / (p:ℚ)) := by
    field_simp
  rw [e, map_mul, gn_mul, gn_C, padicNorm.padicNorm_p_of_prime]
  push_cast
  calc ((p:ℝ)⁻¹) * _ ≤ ((p:ℝ)⁻¹) * (p:ℝ)⁻¹ := mul_le_mul_of_nonneg_left H (by positivity)
    _ = ((p:ℝ)⁻¹)^2 := by ring

end Transport2


section Sr2Transport
open ChainClasses ChainModel LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame}

lemma chainMatrix_apply' {z : ℕ} (i j : ChainIndex p r z) :
    chainMatrix (p := p) Fr r z i j =
      C ((p:ℚ)^2 * Fr.Mn (chainNode i).val (chainNode j).val) + X * (if i = j then (1:ℚ[X]) else 0) := by
  simp [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply]

/-- The chain matrices of corresponding chains agree modulo `p²`. -/
theorem chainMatrix_cng2 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N) {x x' : ℕ}
    (hxx : x ≤ x') (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (x:ℤ) (x':ℤ))
    (i j : ChainIndex p r x) :
    gn p (chainMatrix (p := p) Fr r x i j -
      chainMatrix (p := p) Fr r x' (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i)
        (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc j)) ≤ ((p:ℝ)⁻¹)^2 := by
  set e := chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc with he
  obtain ⟨s1, v1, w1, -⟩ := chainTransport_pole hL hxx hnc i
  obtain ⟨s2, v2, w2, -⟩ := chainTransport_pole hL hxx hnc j
  have hpse : poleScaledEntry Fr p o (chainNode i).val (chainNode j).val =
      poleScaledEntry Fr p o (chainNode (e i)).val (chainNode (e j)).val := by
    apply poleScaledEntry_transport (by omega) v1 v2 w1
  have hsame1 : (chainNode i).val % p = (chainNode j).val % p := by rw [chainNode_mod, chainNode_mod]
  have hsame2 : (chainNode (e i)).val % p = (chainNode (e j)).val % p := by
    rw [chainNode_mod, chainNode_mod]
  have hlt : ∀ q : Fin r, q.val < p * p := fun q => by have := q.isLt; omega
  have d1 := gn_C_pole_diff hL hp (hlt (chainNode i)) (hlt (chainNode j)) hsame1
  have d2 := gn_C_pole_diff hL hp (hlt (chainNode (e i))) (hlt (chainNode (e j))) hsame2
  have hij : (if i = j then (1:ℚ[X]) else 0) = (if e i = e j then (1:ℚ[X]) else 0) := by
    simp [e.injective.eq_iff]
  rw [chainMatrix_apply', chainMatrix_apply', ← hij]
  have : C ((p:ℚ)^2 * Fr.Mn (chainNode i).val (chainNode j).val) + X * (if i = j then (1:ℚ[X]) else 0) -
      (C ((p:ℚ)^2 * Fr.Mn (chainNode (e i)).val (chainNode (e j)).val) + X * (if i = j then (1:ℚ[X]) else 0)) =
      C ((p:ℚ)^2 * Fr.Mn (chainNode i).val (chainNode j).val - poleScaledEntry Fr p o (chainNode i).val (chainNode j).val) -
      C ((p:ℚ)^2 * Fr.Mn (chainNode (e i)).val (chainNode (e j)).val - poleScaledEntry Fr p o (chainNode (e i)).val (chainNode (e j)).val) := by
    rw [hpse]; simp only [map_sub]; ring
  rw [this]
  rw [sub_eq_add_neg]
  exact (gn_add_le _ _).trans (max_le d1 (by rw [gn_neg]; exact d2))

end Sr2Transport


section Sr2T
open ChainClasses ChainModel LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame} {Z1 Z2 : Type} [Fintype Z1] [DecidableEq Z1]
  [Fintype Z2] [DecidableEq Z2] {xs1 ys1 : Z1 → ℕ} {xs2 ys2 : Z2 → ℕ}

/-- **The first-order row partners agree modulo `p²` on corresponding chain nodes.** -/
theorem Sr_transport2 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx1 : ∀ z, xs1 z<N) (hx2 : ∀ z, xs2 z<N)
    (hQ0 : Q0 Fr p r xs1 ys1 = Q0 Fr p r xs2 ys2)
    (z1 : Z1) (z2 : Z2) (hz1 : r ≤ xs1 z1) (hz2 : r ≤ xs2 z2) (hxx : xs1 z1 ≤ xs2 z2)
    (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs1 z1 : ℤ) (xs2 z2 : ℤ))
    (i : ChainIndex p r (xs1 z1)) :
    gn p (Sr Fr p r xs1 ys1 z1 (chainNode i) -
      Sr Fr p r xs2 ys2 z2 (chainNode (chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc i)))
      ≤ ((p:ℝ)⁻¹)^2 := by
  set e := chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc with he
  have hh : ChainModel.h Fr p r xs1 ys1 = ChainModel.h Fr p r xs2 ys2 := by
    unfold ChainModel.h; rw [hQ0]
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by positivity
  have hM : ∀ a b : ChainIndex p r (xs1 z1), LemmaE.Int1 p (chainMatrix (p := p) Fr r (xs1 z1) a b) :=
    fun a b => int1_of_gle0 (gle0_chainMatrix hL hp hN hr a b)
  refine row_gn_of_mul (chainMatrix (p := p) Fr r (xs1 z1)) hM
    (ChainClasses.chainMatrix_primitive hL hp hN hr)
    (fun j => Sr Fr p r xs1 ys1 z1 (chainNode j) -
      Sr Fr p r xs2 ys2 z2 (chainNode (e j))) _ hε ?_ i
  intro q
  have hS1 := Sr_chain_eq (ys := ys1) hL hp hN hr z1 hz1 q
  have hS2 := Sr_chain_eq (ys := ys2) hL hp hN hr z2 hz2 (e q)
  rw [← e.sum_comp] at hS2
  have hexp : ((fun j => Sr Fr p r xs1 ys1 z1 (chainNode j) -
        Sr Fr p r xs2 ys2 z2 (chainNode (e j))) ᵥ* chainMatrix (p := p) Fr r (xs1 z1)) q =
      ChainModel.h Fr p r xs1 ys1 * (C2 Fr p r xs1 ys1 z1 (chainNode q) -
        C2 Fr p r xs2 ys2 z2 (chainNode (e q))) +
      ∑ j, Sr Fr p r xs2 ys2 z2 (chainNode (e j)) *
        (chainMatrix (p := p) Fr r (xs2 z2) (e j) (e q) - chainMatrix (p := p) Fr r (xs1 z1) j q) := by
    rw [← hh] at hS2
    simp only [Matrix.vecMul, dotProduct, sub_mul, Finset.sum_sub_distrib]
    rw [hS1]
    have hB : ∑ j, Sr Fr p r xs2 ys2 z2 (chainNode (e j)) * chainMatrix (p := p) Fr r (xs1 z1) j q =
        ChainModel.h Fr p r xs1 ys1 * C2 Fr p r xs2 ys2 z2 (chainNode (e q)) -
          ∑ j, Sr Fr p r xs2 ys2 z2 (chainNode (e j)) *
            (chainMatrix (p := p) Fr r (xs2 z2) (e j) (e q) - chainMatrix (p := p) Fr r (xs1 z1) j q) := by
      rw [← hS2, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hB]
    ring
  rw [hexp]
  -- bounds
  obtain ⟨s1, v1, w1, v4⟩ := chainTransport_pole hL hxx hnc q
  replace s1 : ((chainNode (e q)).val : ℤ) = ((chainNode q).val : ℤ) + (((xs2 z2 : ℕ) : ℤ) - (xs1 z1 : ℕ)) := s1
  replace v1 : polePrefix Fr p o (chainNode q).val = polePrefix Fr p o (chainNode (e q)).val := v1
  replace w1 : poleSquarePrefix Fr p o (chainNode q).val = poleSquarePrefix Fr p o (chainNode (e q)).val := w1
  have hpse : poleScaledEntry Fr p o (xs1 z1) (chainNode q).val =
      poleScaledEntry Fr p o (xs2 z2) (chainNode (e q)).val := by
    rw [poleScaledEntry_symm (Fr := Fr) (p := p) (o := o) (xs1 z1),
      poleScaledEntry_symm (Fr := Fr) (p := p) (o := o) (xs2 z2)]
    exact poleScaledEntry_transport (by omega) v1 v4 w1
  have hlt : ∀ q : Fin r, q.val < p * p := fun q => by have := q.isLt; omega
  have d1 := gn_C_pole_diff hL hp (a := xs1 z1) (b := (chainNode q).val) (by have := hx1 z1; omega)
    (hlt _) (by rw [chainNode_mod])
  have d2 := gn_C_pole_diff hL hp (a := xs2 z2) (b := (chainNode (e q)).val) (by have := hx2 z2; omega)
    (hlt _) (by rw [chainNode_mod])
  have hC2 : gn p (C2 Fr p r xs1 ys1 z1 (chainNode q) - C2 Fr p r xs2 ys2 z2 (chainNode (e q))) ≤
      ((p:ℝ)⁻¹)^2 := by
    rw [C2_apply, C2_apply]
    have : C ((p:ℚ)^2 * Fr.Mn (xs1 z1) (chainNode q).val) - C ((p:ℚ)^2 * Fr.Mn (xs2 z2) (chainNode (e q)).val) =
        C ((p:ℚ)^2 * Fr.Mn (xs1 z1) (chainNode q).val - poleScaledEntry Fr p o (xs1 z1) (chainNode q).val) -
        C ((p:ℚ)^2 * Fr.Mn (xs2 z2) (chainNode (e q)).val - poleScaledEntry Fr p o (xs2 z2) (chainNode (e q)).val) := by
      rw [hpse]; simp only [map_sub]; ring
    rw [this, sub_eq_add_neg]
    exact (gn_add_le _ _).trans (max_le d1 (by rw [gn_neg]; exact d2))
  have hhn : gn p (ChainModel.h Fr p r xs1 ys1) ≤ 1 := by
    have := (gle_iff_gn p 0 _).1 (gle0_h (xs := xs1) (ys := ys1) hL hp hN hr)
    simpa using this
  refine (gn_add_le _ _).trans (max_le ?_ ?_)
  · rw [gn_mul]
    calc gn p (ChainModel.h Fr p r xs1 ys1) * _ ≤ 1 * ((p:ℝ)⁻¹)^2 :=
          mul_le_mul hhn hC2 (gn_nonneg p _) zero_le_one
      _ = _ := one_mul _
  · apply LemmaE.gn_sum_le_const _ _ _ hε
    intro j _
    rw [gn_mul]
    have hMj := chainMatrix_cng2 hL hp hN hr hxx hnc j q
    have hMj' : gn p (chainMatrix (p := p) Fr r (xs2 z2) (e j) (e q) -
        chainMatrix (p := p) Fr r (xs1 z1) j q) ≤ ((p:ℝ)⁻¹)^2 := by
      rw [← neg_sub, gn_neg]; exact hMj
    calc gn p (Sr Fr p r xs2 ys2 z2 (chainNode (e j))) * _ ≤ 1 * ((p:ℝ)⁻¹)^2 :=
          mul_le_mul (Sr_int1 hL hp hN hr hx2 z2 _) hMj' (gn_nonneg p _) zero_le_one
      _ = _ := one_mul _

end Sr2T


section RegDiff
open ChainClasses ChainModel LemmaE
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The regular cumulative `∑_{k ≤ a} regularDelta k`. -/
noncomputable def Rg (p o a : ℕ) : ℚ := ∑ k ∈ Icc 1 a, regularDelta p (o:ℤ) (k:ℤ)

lemma fullPrefix_split (a : ℕ) : fullPrefix Fr a = polePrefix Fr p o a + Rg p o a := by
  unfold fullPrefix polePrefix poleDelta Rg
  simp only [Finset.sum_sub_distrib]
  ring

lemma Rg_eq_regularPrefix (a : ℕ) : Rg p o a = regularPrefix p (o:ℤ) a := by
  induction a with
  | zero => simp [Rg, regularPrefix]
  | succ n ih =>
    have h1 : Rg p o (n + 1) = Rg p o n + regularDelta p (o:ℤ) ((n + 1 : ℕ) : ℤ) := by
      unfold Rg; exact Finset.sum_Icc_succ_top (by omega) _
    rw [h1, ih]
    unfold regularPrefix
    rw [Finset.sum_range_succ]
    push_cast
    rfl

lemma Rg_good (hp : 5 ≤ p) {a b : ℕ} (hab : a % p = b % p) :
    Good p (Rg p o b - Rg p o a) 0 := by
  rw [Rg_eq_regularPrefix, Rg_eq_regularPrefix]
  exact good_regularPrefix_difference (p := p) (o:ℤ) (four_ne_zmod p hp) hab

end RegDiff

section Own
open ChainClasses ChainModel LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame} {Z1 Z2 : Type} [Fintype Z1] [DecidableEq Z1]
  [Fintype Z2] [DecidableEq Z2] {xs1 ys1 : Z1 → ℕ} {xs2 ys2 : Z2 → ℕ}

/-- The own-chain part `h ω_x - (Sr ω)_x` of the one-node residual. -/
noncomputable def Wown (Fr : Frame) (p r : ℕ) [Fact p.Prime] {Z : Type} [Fintype Z] [DecidableEq Z]
    (xs ys : Z → ℕ) (a b : ℚ[X]) (z : Z) : ℚ[X] :=
  ChainModel.h Fr p r xs ys * omegaW Fr p a b (xs z) -
    ∑ m, Sr Fr p r xs ys z m * omegaW Fr p a b m.val

/-- **Own-chain transport.**  For two nodes of one cut-free interval,
`W(x₁) - W(x₂) ≡ - a · p (R(x₂) - R(x₁)) · (h - ∑ Sr_{x₂})  (mod p²)`, `R` the regular cumulative. -/
theorem Wown_transport2 (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx1 : ∀ z, xs1 z<N) (hx2 : ∀ z, xs2 z<N)
    (hQ0 : Q0 Fr p r xs1 ys1 = Q0 Fr p r xs2 ys2)
    (z1 : Z1) (z2 : Z2) (hz1 : r ≤ xs1 z1) (hz2 : r ≤ xs2 z2) (hxx : xs1 z1 ≤ xs2 z2)
    (hnc : NoCut (Cut (p:ℤ) (r:ℤ) (Singular (p:ℤ) (o:ℤ))) (xs1 z1 : ℤ) (xs2 z2 : ℤ))
    {a b : ℚ[X]} (ha : Int1 p a) (hb : Int1 p b) :
    gn p (Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
      a * C ((p:ℚ) * (Rg p o (xs2 z2) - Rg p o (xs1 z1))) *
        (ChainModel.h Fr p r xs2 ys2 - ∑ m, Sr Fr p r xs2 ys2 z2 m)) ≤ ((p:ℝ)⁻¹)^2 := by
  classical
  set e := chainTransport (sing := Singular (p:ℤ) (o:ℤ)) hxx hnc with he
  have hh : ChainModel.h Fr p r xs1 ys1 = ChainModel.h Fr p r xs2 ys2 := by
    unfold ChainModel.h; rw [hQ0]
  have hp0 : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hε : (0:ℝ) ≤ ((p:ℝ)⁻¹)^2 := by positivity
  set ω : ℕ → ℚ[X] := fun k => omegaW Fr p a b k with hω
  have hωint : ∀ k, k < N → Int1 p (ω k) := fun k hk =>
    (ha.mul (int1_pPf hL hp hN hr hk)).sub hb
  -- sums over chains
  have F1 : ∑ m, Sr Fr p r xs1 ys1 z1 m * ω m.val =
      ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs1 ys1 z1 (chainNode q) * ω (chainNode q).val := by
    rw [sum_chain (p := p) hz1 (fun m => Sr Fr p r xs1 ys1 z1 m * ω m.val)]
    intro m hm
    rw [Sr_support hL hp hN hr z1 m (fun h => hm h.symm), zero_mul]
  have F2 : ∑ m, Sr Fr p r xs2 ys2 z2 m * ω m.val =
      ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) * ω (chainNode (e q)).val := by
    rw [sum_chain (p := p) hz2 (fun m => Sr Fr p r xs2 ys2 z2 m * ω m.val)]
    · exact (e.sum_comp (fun q' => Sr Fr p r xs2 ys2 z2 (chainNode q') * ω (chainNode q').val)).symm
    · intro m hm
      rw [Sr_support hL hp hN hr z2 m (fun h => hm h.symm), zero_mul]
  have F3 : ∑ m, Sr Fr p r xs2 ys2 z2 m =
      ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) := by
    rw [sum_chain (p := p) hz2 (fun m => Sr Fr p r xs2 ys2 z2 m)]
    · exact (e.sum_comp (fun q' => Sr Fr p r xs2 ys2 z2 (chainNode q'))).symm
    · intro m hm
      exact Sr_support hL hp hN hr z2 m (fun h => hm h.symm)
  -- the pole parts of the cumulatives agree
  have h0 : NoCut (Singular (p:ℤ) (o:ℤ)) (xs1 z1 : ℤ) (xs2 z2 : ℤ) :=
    fun t h1 h2 hs => hnc t h1 h2 (Or.inl hs)
  have hpole1 : polePrefix Fr p o (xs1 z1) = polePrefix Fr p o (xs2 z2) :=
    polePrefix_nocut hL hxx h0
  set Δ : ℚ := Rg p o (xs2 z2) - Rg p o (xs1 z1) with hΔ
  obtain ⟨R, hR⟩ : ∃ R : ChainIndex p r (xs1 z1) → ℚ, ∀ q, R q = Rg p o (chainNode (e q)).val - Rg p o (chainNode q).val := ⟨_, fun _ => rfl⟩
  have F4 : ω (xs1 z1) - ω (xs2 z2) = -(a * C ((p:ℚ) * Δ)) := by
    simp only [hω, omegaW]
    rw [fullPrefix_split (Fr := Fr) (p := p) (o := o) (xs1 z1),
      fullPrefix_split (Fr := Fr) (p := p) (o := o) (xs2 z2), hpole1, hΔ]
    simp only [map_mul, map_add, map_sub]
    ring
  have F5 : ∀ q : ChainIndex p r (xs1 z1),
      ω (chainNode (e q)).val = ω (chainNode q).val +
        a * C ((p:ℚ) * R q) := by
    intro q
    obtain ⟨-, v1, -, -⟩ := chainTransport_pole hL hxx hnc q
    replace v1 : polePrefix Fr p o (chainNode q).val = polePrefix Fr p o (chainNode (e q)).val := v1
    simp only [hω, omegaW]
    rw [fullPrefix_split (Fr := Fr) (p := p) (o := o) (chainNode q).val,
      fullPrefix_split (Fr := Fr) (p := p) (o := o) (chainNode (e q)).val, v1, hR q]
    simp only [map_mul, map_add, map_sub]
    ring
  -- error terms
  have E2 : gn p (∑ q : ChainIndex p r (xs1 z1),
      (Sr Fr p r xs1 ys1 z1 (chainNode q) - Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
        ω (chainNode q).val) ≤ ((p:ℝ)⁻¹)^2 := by
    apply LemmaE.gn_sum_le_const _ _ _ hε
    intro q _
    rw [gn_mul]
    calc gn p (Sr Fr p r xs1 ys1 z1 (chainNode q) - Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
          gn p (ω (chainNode q).val) ≤ ((p:ℝ)⁻¹)^2 * 1 :=
        mul_le_mul (Sr_transport2 hL hp hN hr hx1 hx2 hQ0 z1 z2 hz1 hz2 hxx hnc q)
          (hωint _ (lt_of_lt_of_le (chainNode q).isLt hr)) (gn_nonneg p _) hε
      _ = _ := mul_one _
  have E3 : gn p (∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) *
      (C ((p:ℚ) * R q) -
        C ((p:ℚ) * Δ))) ≤ ((p:ℝ)⁻¹)^2 := by
    apply LemmaE.gn_sum_le_const _ _ _ hε
    intro q _
    have hG : Good p ((Rg p o (chainNode (e q)).val - Rg p o (xs2 z2)) -
        (Rg p o (chainNode q).val - Rg p o (xs1 z1))) 0 := by
      have g1 := Rg_good (p := p) (o := o) hp (a := xs2 z2) (b := (chainNode (e q)).val)
        (by rw [chainNode_mod])
      have g2 := Rg_good (p := p) (o := o) hp (a := xs1 z1) (b := (chainNode q).val)
        (by rw [chainNode_mod])
      simpa using g1.sub g2
    have hgn := gn_C_le_of_good_zero hG
    have e1 : C ((p:ℚ) * R q) -
        C ((p:ℚ) * Δ) = C (p:ℚ) * C ((Rg p o (chainNode (e q)).val - Rg p o (xs2 z2)) -
        (Rg p o (chainNode q).val - Rg p o (xs1 z1))) := by
      rw [hR q, hΔ, ← map_sub, ← map_mul]; congr 1; ring
    have hgp : gn p (C (p:ℚ)) = (p:ℝ)⁻¹ := by
      rw [gn_C, padicNorm.padicNorm_p_of_prime]; push_cast; rfl
    rw [e1]
    simp only [gn_mul, hgp]
    have hs := Sr_int1 (ys := ys2) hL hp hN hr hx2 z2 (chainNode (e q))
    calc gn p a * gn p (Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
          (((p:ℝ)⁻¹) * gn p (C ((Rg p o (chainNode (e q)).val - Rg p o (xs2 z2)) -
            (Rg p o (chainNode q).val - Rg p o (xs1 z1))))) ≤ 1 * 1 * ((p:ℝ)⁻¹ * (p:ℝ)⁻¹) :=
        mul_le_mul (mul_le_mul ha hs (gn_nonneg p _) zero_le_one)
          (mul_le_mul_of_nonneg_left hgn (by positivity)) (mul_nonneg (by positivity) (gn_nonneg p _)) (mul_nonneg zero_le_one zero_le_one)
      _ = _ := by ring
  -- the exact identity
  have key : Wown Fr p r xs1 ys1 a b z1 - Wown Fr p r xs2 ys2 a b z2 +
      a * C ((p:ℚ) * Δ) * (ChainModel.h Fr p r xs2 ys2 - ∑ m, Sr Fr p r xs2 ys2 z2 m) =
      -(∑ q : ChainIndex p r (xs1 z1),
        (Sr Fr p r xs1 ys1 z1 (chainNode q) - Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
          ω (chainNode q).val) +
      ∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) *
        (C ((p:ℚ) * R q) - C ((p:ℚ) * Δ)) := by
    unfold Wown
    rw [F1, F2, F3, ← hh]
    have G1 : ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) * ω (chainNode (e q)).val =
        ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) * ω (chainNode q).val +
        ∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) *
          C ((p:ℚ) * R q) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun q _ => by rw [F5 q]; ring
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_mul]
    have F4' : omegaW Fr p a b (xs1 z1) = omegaW Fr p a b (xs2 z2) - a * C ((p:ℚ) * Δ) := by
      have := F4; simp only [hω] at this; linear_combination this
    have hS5 : ∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) * C ((p:ℚ) * Δ) =
        a * C ((p:ℚ) * Δ) * ∑ q : ChainIndex p r (xs1 z1), Sr Fr p r xs2 ys2 z2 (chainNode (e q)) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    rw [F4']
    linear_combination G1 + hS5
  rw [key]
  have : -(∑ q : ChainIndex p r (xs1 z1),
        (Sr Fr p r xs1 ys1 z1 (chainNode q) - Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
          ω (chainNode q).val) +
      ∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) *
        (C ((p:ℚ) * R q) - C ((p:ℚ) * Δ)) =
      (∑ q : ChainIndex p r (xs1 z1), a * Sr Fr p r xs2 ys2 z2 (chainNode (e q)) *
        (C ((p:ℚ) * R q) - C ((p:ℚ) * Δ))) +
      -(∑ q : ChainIndex p r (xs1 z1),
        (Sr Fr p r xs1 ys1 z1 (chainNode q) - Sr Fr p r xs2 ys2 z2 (chainNode (e q))) *
          ω (chainNode q).val) := by ring
  rw [this]
  exact (gn_add_le _ _).trans (max_le E3 (by rw [gn_neg]; exact E2))

end Own

#print axioms CatalanCore.Arith.Hybrid.Wown_transport2
end CatalanCore.Arith.Hybrid
