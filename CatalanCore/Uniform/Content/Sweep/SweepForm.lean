module

public import CatalanCore.Uniform.Content.Sweep.QInv

@[expose] public section

/-!
# Sweep form: Lemma G, Lemma C and Proposition W for the plane 2 matrix (lane H, wave H2b; ledger P204)

`PLANE2-P1-ROW` §2 and §3, over any commutative `ℤ_(p)`-algebra `R` with `UnitProp p ξ` and `PRad`.  The
pivot block `Qp = p³ H[𝒫_r, 𝒫_c]` is invertible (`QInv`), `H = Hq` is the matrix on
`(Ω ⊕ I) × (Ω ⊕ J)` of the pivot rows/columns and any outside rows/columns `zn`, `yn`.

* `Qent_disp`, `isDisp_Hq`: the displacement identity `(s - t) Q(s,t) = p f2(s) - p f2(t)`
  (`f2 = p² f`), the input of `Schur.pivot_displacement`.
* `master_Q_Th` (Lemma G in matrix form): `Q Θ^b = Γ^b` on the pivot rows modulo `p²`, with
  `Θ^b(y) = ε(ω_y) Y^b_{h,o}(j)`; `pi2_gv`: the pivot-label vectors `Z·1`, `Z·(p² f)` are `Θ^b` mod `p²`.
* `pi2_Vout` (Corollary): the outside-label vectors are `ε(ω_n) (Γ^b_h(l) − β^b(n))` mod `p²`.
* `labR`, `labC`: the generator pairs of the row-type and column-type labels (`R1, ρ0`, `C0, γ1`), where
  `Schur.R0 = p ρ0`, `Schur.C1 = p γ1` (`R1_eq`, `R0_eq`, `C0_eq`, `C1_eq`); the column side is the
  transposed system `1 − π` (`Zp_transpose`, `rowNode_eq_colNode`).
* `oc_node` (Lemma C, parity): the class of a node from the parity of the node and of its period.
* `sw_dvd` (Proposition W): `p^(3 − W) ∣ Sw(r, c)` for all labels, `W = wR r c`: `3` for congruent nodes;
  otherwise `0` (one cell), `1` (one period, other half) if the pattern (kind, class) agrees, else `2`.
  No bound on `v(x_r − x_c)` is needed: the congruent weight `3` asks for nothing.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section Disp

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

/-- `p² f_n` as an element of `R`. -/
noncomputable def f2 (n : ℕ) : R := toR p ((p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).f n)

theorem toR_natCast (n : ℕ) : toR p ((n : ℕ) : ℚ) = (n : R) := by
  have hm : ((n : ℕ) : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (n : ℤ)
  rw [toR_of_mem hm]
  have : (⟨((n : ℕ) : ℚ), hm⟩ : LocRing p) = (n : LocRing p) := by apply Subtype.ext; simp
  rw [this, map_natCast]

theorem p_mem_loc : ((p : ℕ) : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)

theorem p2_mem_loc : ((p : ℚ) ^ 2) ∈ LocRing p := by
  exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (2 : ℕ))

theorem toR_p_sq : toR p ((p : ℚ) ^ 2) = (p : R) ^ 2 := by
  rw [pow_two, toR_mul p_mem_loc p_mem_loc, toR_p]; ring

theorem p2f_mem (hodd : p % 2 = 1) (hN : 2 * N < p * p) {n : ℕ} (hn : n < N) :
    (p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).f n ∈ LocRing p := by
  rw [f_eq v u (p := p) hv hu, mul_add, PF_eq_Scell v u hodd n]
  exact (LocRing p).add_mem (sig_cell_mem v u hodd hN hn)
    ((LocRing p).mul_mem p2_mem_loc (RF_mem v u n))

theorem f2_sub_sig (hodd : p % 2 = 1) (hN : 2 * N < p * p) {n : ℕ} (hn : n < N) :
    (p : R) ^ 2 ∣ f2 (p := p) v u hv hu n - sigR (p := p) v u (cell p n) := by
  unfold f2 sigR
  rw [f_eq v u (p := p) hv hu, mul_add, PF_eq_Scell v u hodd n, toR_add (sig_cell_mem v u hodd hN hn)
    ((LocRing p).mul_mem p2_mem_loc (RF_mem v u n)), toR_mul p2_mem_loc (RF_mem v u n), toR_p_sq]
  exact ⟨toR p (RF v u p n), by ring⟩

theorem Qent_disp (hodd : p % 2 = 1) (hN : 2 * N < p * p) (ξ : R) {s t : ℕ} (hs : s < N) (ht : t < N) :
    ((s : R) - (t : R)) * Qent (p := p) v u hv hu ξ s t =
      (p : R) * f2 (p := p) v u hv hu s - (p : R) * f2 (p := p) v u hv hu t := by
  by_cases hst : s = t
  · subst hst; simp
  · unfold Qent
    rw [if_neg hst, zero_add]
    have hq := q_mem v u hv hu hN hs ht
    have hmf := p2f_mem v u hv hu hodd hN hs
    have hmg := p2f_mem v u hv hu hodd hN ht
    have hst' : ((s : ℚ) - t) ∈ LocRing p := by
      have := int_mem_locRing (ℓ := p) ((s : ℤ) - t); push_cast at this; exact this
    have e1 : ((s : ℚ) - t) * ((p : ℚ) ^ 3 * Lm v u hv hu s t) =
        (p : ℚ) * ((p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).f s) -
          (p : ℚ) * ((p : ℚ) ^ 2 * (Datum.plane2 v u hv hu).f t) := by
      unfold Lm lw
      rw [if_neg hst]
      have h1 : ((t : ℚ) - s) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hst))
      field_simp
      ring
    have e2 : ((s : R) - (t : R)) * toR p ((p : ℚ) ^ 3 * Lm v u hv hu s t) =
        toR p (((s : ℚ) - t) * ((p : ℚ) ^ 3 * Lm v u hv hu s t)) := by
      rw [toR_mul hst' hq, toR_sub (by exact_mod_cast int_mem_locRing (ℓ := p) (s : ℤ))
        (by exact_mod_cast int_mem_locRing (ℓ := p) (t : ℤ)), toR_natCast, toR_natCast]
    rw [e2, e1, toR_sub ((LocRing p).mul_mem p_mem_loc hmf) ((LocRing p).mul_mem p_mem_loc hmg),
      toR_mul p_mem_loc hmf, toR_mul p_mem_loc hmg, toR_p]
    rfl


end Disp

section Master

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] (κ k' π : ℕ) (ξ : R)

/-- The class solutions of `Sweep.Classes`, as a function of `(b, h, o, j)`. -/
noncomputable def YrF : ℕ → ℕ → ℕ → ℕ → R := fun b h o j => Yr (p := p) v u κ k' ξ b h o j

/-- `ε(ω) = 1 - p δ E(ω)` of Lemma G, in `R / (p²)`. -/
noncomputable def epsS (ω : ℕ) : S2 p R :=
  Gen.eps (pi2 p R (p : R)) p κ k' π (sgS (p := p) (R := R) v u) (ddS (p := p) (R := R))
    (YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ)) ω

/-- The pivot-column vector `Θ^b(y) = ε(ω) Y^{b}_{h,o}(j)` in `R / (p²)`. -/
noncomputable def Th (b : ℕ) (y : PivIdx p κ k') : S2 p R :=
  epsS (p := p) v u κ k' π ξ y.1 *
    YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p y.1) (oc p κ π y.1)
      (colPer κ k' (oc p κ π y.1) y.2)

variable {κ k'}

theorem Cper_eq_image_col (o : ℕ) (ho : o ≤ 1) :
    Cper κ k' o = (Finset.univ : Finset (Fin κ ⊕ Fin k')).image (colPer κ k' o) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact exists_colPer κ k' o ho hj
  · rintro ⟨a, rfl⟩; exact colPer_mem κ k' o ho a

theorem Cper_eq_image_row (o : ℕ) (ho : o ≤ 1) :
    Cper κ k' (1 - o) = (Finset.univ : Finset (Fin κ ⊕ Fin k')).image (rowPer κ k' o) := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hj; exact exists_rowPer κ k' o ho hj
  · rintro ⟨a, rfl⟩; exact rowPer_mem κ k' o ho a

variable (κ k')

theorem sum_colNode {M : Type*} [AddCommMonoid M] (hp0 : 0 < p) (F : ℕ → M) :
    ∑ y : PivIdx p κ k', F (colNode p κ k' π y) = ∑ t ∈ PCs p κ k' π, F t := by
  rw [PCs_sum p κ k' π hp0 F, Fintype.sum_prod_type]
  rw [Finset.sum_range (fun ω => ∑ j ∈ Cper κ k' (oc p κ π ω), F (j * p + ω))]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Cper_eq_image_col _ (oc_le (π := π) (κ := κ) (p := p) ω), Finset.sum_image]
  · rfl
  · intro a _ b _ h; exact colPer_injective κ k' _ h

theorem oc_one_sub (hπ : π ≤ 1) (ω : ℕ) : oc p κ (1 - π) ω = 1 - oc p κ π ω := by
  unfold oc
  have h1 : (κ * p + ω) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  split_ifs <;> omega

theorem rowNode_eq_colNode (hπ : π ≤ 1) (x : PivIdx p κ k') :
    rowNode p κ k' π x = colNode p κ k' (1 - π) x := by
  unfold rowNode colNode
  rw [oc_one_sub (p := p) κ π hπ]
  have ho := oc_le (π := π) (κ := κ) (p := p) x.1
  congr 2

theorem sum_rowNode {M : Type*} [AddCommMonoid M] (hπ : π ≤ 1) (hp0 : 0 < p) (F : ℕ → M) :
    ∑ y : PivIdx p κ k', F (rowNode p κ k' π y) = ∑ t ∈ PCs p κ k' (1 - π), F t := by
  rw [← sum_colNode κ k' (1 - π) hp0 F]
  exact Finset.sum_congr rfl fun y _ => by rw [rowNode_eq_colNode κ k' π hπ]

end Master

section MasterQ

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}

theorem YrF_class (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) :
    ∀ b h o, o ≤ 1 → h ≤ 1 → ∀ l ∈ Cper κ k' (1 - o),
      ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ h l j * YrF (p := p) v u κ k' ξ b h o j =
        GamR (p := p) v u b h l :=
  fun b h o ho hh l hl => Yr_class v u κ k' hU hodd hN hH hpv hh ho b hl

theorem YrF_half (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) :
    ∀ b o, o ≤ 1 → ∀ j ∈ Cper κ k' o, (p : R) ∣ YrF (p := p) v u κ k' ξ b 1 o j - YrF (p := p) v u κ k' ξ b 0 o j :=
  fun b o ho j hj => Yr_half v u κ k' hU hodd hN hH hpv ho b hj

theorem Gam_sgS_eq (b h l : ℕ) :
    Gen.Gam (sgS (p := p) (R := R) v u) b h l = pi2 p R (GamR (p := p) v u b (min h 1) l) := by
  unfold Gen.Gam GamR sgS
  by_cases hb : b = 0
  · simp [hb]
  · simp [hb]

/-- **Lemma G, in matrix form**: `Q Θ^b = Γ^b` on the pivot rows, modulo `p²`. -/
theorem master_Q_Th (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N) {b : ℕ} (hb : b ≤ 1) (x : PivIdx p κ k') :
    ∑ y, pi2 p R (Qp (p := p) v u hv hu κ k' π ξ x y) * Th (p := p) v u κ k' π ξ b y =
      Gen.Gam (sgS (p := p) (R := R) v u) b (half p x.1) (rowPer κ k' (oc p κ π x.1) x.2) := by
  have hp0 : 0 < p := hp.out.pos
  have hL := lemmaG_S (p := p) (π := π) v u hv hu hodd hp5 hN hH ξ (YrF (p := p) v u κ k' ξ)
    (YrF_class v u hU hpv hodd hN hH) (YrF_half v u hU hpv hodd hN hH) (rowNode p κ k' π x)
    (rowNode_lt hH x) b hb
  have hL' : ∑ y : PivIdx p κ k', (fun t => qS (p := p) v u hv hu ξ (rowNode p κ k' π x) t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS (p := p) (R := R) v u) (ddS (p := p) (R := R))
          (YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ)) (t % p) *
          YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p t) (oc p κ π (t % p)) (t / p)))
        (colNode p κ k' π y) = _ := (sum_colNode κ k' π hp0 _).trans hL
  have hS : ∀ y : PivIdx p κ k', (fun t => qS (p := p) v u hv hu ξ (rowNode p κ k' π x) t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS (p := p) (R := R) v u) (ddS (p := p) (R := R))
          (YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ)) (t % p) *
          YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p t) (oc p κ π (t % p)) (t / p)))
        (colNode p κ k' π y) =
      pi2 p R (Qp (p := p) v u hv hu κ k' π ξ x y) * Th (p := p) v u κ k' π ξ b y := by
    intro y
    simp only [colNode_mod, colNode_div hp0]
    have : half p (colNode p κ k' π y) = half p y.1 := by
      unfold colNode; rw [half_node hp0 _ _ y.1.2]
    rw [this]
    rfl
  rw [Finset.sum_congr rfl (fun y _ => hS y)] at hL'
  rw [hL']
  have hmod : rowNode p κ k' π x % p = x.1 := rowNode_mod x
  have hdiv : rowNode p κ k' π x / p = rowPer κ k' (oc p κ π x.1) x.2 := rowNode_div hp0 x
  have hhalf : half p (rowNode p κ k' π x) = half p x.1 := by
    unfold rowNode; rw [half_node hp0 _ _ x.1.2]
  have hcl := congrArg (pi2 p R)
    (YrF_class v u hU hpv hodd hN hH b (half p x.1) (oc p κ π x.1) (oc_le x.1) (half_le_one' _)
      (rowPer κ k' (oc p κ π x.1) x.2) (rowPer_mem κ k' _ (oc_le x.1) x.2))
  rw [map_sum] at hcl
  simp only [map_mul] at hcl
  have hsum : ∑ j ∈ Cper κ k' (oc p κ π x.1), BmS (p := p) v u ξ (half p x.1) (rowPer κ k' (oc p κ π x.1) x.2) j *
      YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p x.1) (oc p κ π x.1) j =
      Gen.Gam (sgS (p := p) (R := R) v u) b (half p x.1) (rowPer κ k' (oc p κ π x.1) x.2) := by
    unfold BmS YvS
    rw [min_eq_left (half_le_one' _), Gam_sgS_eq, min_eq_left (half_le_one' _)]
    exact hcl
  simp only [hmod, hdiv, hhalf]
  rw [hsum]
  unfold Gen.eps
  ring

end MasterQ

section VecLab

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] {κ k' π : ℕ} {ξ : R}

variable (κ k' π ξ)

/-- The right-hand sides `1` and `p² f` (on the pivot rows). -/
noncomputable def Rvec (b : ℕ) (x : PivIdx p κ k') : R :=
  if b = 0 then 1 else f2 (p := p) v u hv hu (rowNode p κ k' π x)

/-- `g^b = Z W^b`: the vectors `A = Z 1` and `Z (p² f)`. -/
noncomputable def gv (b : ℕ) : PivIdx p κ k' → R :=
  (Zp (p := p) v u hv hu κ k' π ξ) *ᵥ Rvec (p := p) v u hv hu κ k' π b

/-- The value on the left hand side: `1` or `p² f_n`. -/
noncomputable def outG (b n : ℕ) : R := if b = 0 then 1 else f2 (p := p) v u hv hu n

/-- The label vector of an outside node `n`: `outG − Q(n,·) g^b`. -/
noncomputable def Vout (b n : ℕ) : R :=
  outG (p := p) v u hv hu b n - ∑ y, Qent (p := p) v u hv hu ξ n (colNode p κ k' π y) * gv (p := p) v u hv hu κ k' π ξ b y

/-- The residual pattern of an outside label: `Γ^b_h(l) − ∑_{j ∈ C_o} B^h(l, j) Y^b_{h,o}(j)`. -/
noncomputable def Gout (b h o l : ℕ) : R :=
  GamR (p := p) v u b h l - ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ h l j * YrF (p := p) v u κ k' ξ b h o j

variable {κ k' π ξ}

theorem pi2_Rvec (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N) {b : ℕ} (hb : b ≤ 1)
    (x : PivIdx p κ k') :
    pi2 p R (Rvec (p := p) v u hv hu κ k' π b x) =
      Gen.Gam (sgS (p := p) (R := R) v u) b (half p x.1) (rowPer κ k' (oc p κ π x.1) x.2) := by
  have hp0 : 0 < p := hp.out.pos
  unfold Rvec
  by_cases hb0 : b = 0
  · simp [hb0, Gen.Gam]
  · simp only [hb0, if_false]
    have hlt := rowNode_lt (π := π) hH x
    have h := f2_sub_sig (R := R) v u hv hu hodd hN hlt
    rw [← pi2_eq_iff] at h
    rw [h]
    have hc : cell p (rowNode p κ k' π x) = (rowPer κ k' (oc p κ π x.1) x.2, half p x.1) := by
      unfold rowNode; exact cell_node hp0 _ _ x.1.2
    rw [hc]
    unfold Gen.Gam sgS
    simp [hb0, half_le_one']

theorem pi2_outG (hodd : p % 2 = 1) (hN : 2 * N < p * p) {n : ℕ} (hn : n < N) (b : ℕ) :
    pi2 p R (outG (p := p) v u hv hu b n) = Gen.Gam (sgS (p := p) (R := R) v u) b (half p n) (n / p) := by
  unfold outG
  by_cases hb0 : b = 0
  · simp [hb0, Gen.Gam]
  · simp only [hb0, if_false]
    have h := f2_sub_sig (R := R) v u hv hu hodd hN hn
    rw [← pi2_eq_iff] at h
    rw [h]
    unfold Gen.Gam sgS
    simp [hb0, half_le_one']
    rfl

/-- `Z W^b` reduces to `Θ^b`. -/
theorem pi2_gv (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) {b : ℕ} (hb : b ≤ 1) (x : PivIdx p κ k') :
    pi2 p R (gv (p := p) v u hv hu κ k' π ξ b x) = Th (p := p) v u κ k' π ξ b x := by
  set ZS := (pi2 p R).mapMatrix (Zp (p := p) v u hv hu κ k' π ξ) with hZS
  set QS := (pi2 p R).mapMatrix (Qp (p := p) v u hv hu κ k' π ξ) with hQS
  have hZQ : ZS * QS = 1 := by
    rw [hZS, hQS, ← RingHom.map_mul, Zp_mul_Qp v u hv hu hU hpv hodd hp5 hN hH hRad, map_one]
  have hQT : QS *ᵥ (Th (p := p) v u κ k' π ξ b) = fun x => Gen.Gam (sgS (p := p) (R := R) v u) b (half p x.1)
      (rowPer κ k' (oc p κ π x.1) x.2) := by
    funext x'
    rw [← master_Q_Th v u hv hu hU hpv hodd hp5 hN hH hb x']
    simp [Matrix.mulVec, dotProduct, hQS]
  have hTh : Th (p := p) v u κ k' π ξ b = ZS *ᵥ (fun x => Gen.Gam (sgS (p := p) (R := R) v u) b (half p x.1)
      (rowPer κ k' (oc p κ π x.1) x.2)) := by
    rw [← hQT, Matrix.mulVec_mulVec, hZQ, Matrix.one_mulVec]
  rw [hTh]
  unfold gv
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hZS, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun x' _ => ?_
  rw [pi2_Rvec v u hv hu hodd hN hH hb x']

/-- **Outside labels** (Corollary of Lemma G): `V(n) ≡ ε(ω_n) (Γ_h(j) − β(n)) mod p²`. -/
theorem pi2_Vout (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) {b : ℕ} (hb : b ≤ 1) {n : ℕ} (hn : n < N) :
    pi2 p R (Vout (p := p) v u hv hu κ k' π ξ b n) =
      epsS (p := p) v u κ k' π ξ (n % p) *
        pi2 p R (Gout (p := p) v u κ k' ξ b (half p n) (oc p κ π (n % p)) (n / p)) := by
  have hp0 : 0 < p := hp.out.pos
  have hL := lemmaG_S (p := p) (π := π) v u hv hu hodd hp5 hN hH ξ (YrF (p := p) v u κ k' ξ)
    (YrF_class v u hU hpv hodd hN hH) (YrF_half v u hU hpv hodd hN hH) n hn b hb
  have hL' : ∑ y : PivIdx p κ k', (fun t => qS (p := p) v u hv hu ξ n t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS (p := p) (R := R) v u) (ddS (p := p) (R := R))
          (YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ)) (t % p) *
          YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p t) (oc p κ π (t % p)) (t / p)))
        (colNode p κ k' π y) = _ := (sum_colNode κ k' π hp0 _).trans hL
  have hS : ∀ y : PivIdx p κ k', (fun t => qS (p := p) v u hv hu ξ n t *
        (Gen.eps (pi2 p R (p : R)) p κ k' π (sgS (p := p) (R := R) v u) (ddS (p := p) (R := R))
          (YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ)) (t % p) *
          YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p t) (oc p κ π (t % p)) (t / p)))
        (colNode p κ k' π y) =
      pi2 p R (Qent (p := p) v u hv hu ξ n (colNode p κ k' π y) *
        gv (p := p) v u hv hu κ k' π ξ b y) := by
    intro y
    simp only [colNode_mod, colNode_div hp0]
    have : half p (colNode p κ k' π y) = half p y.1 := by
      unfold colNode; rw [half_node hp0 _ _ y.1.2]
    rw [this, map_mul, pi2_gv v u hv hu hU hpv hodd hp5 hN hH hRad hb y]
    rfl
  rw [Finset.sum_congr rfl (fun y _ => hS y), ← map_sum] at hL'
  unfold Vout
  rw [map_sub, hL', pi2_outG v u hv hu hodd hN hn]
  unfold Gout
  rw [map_sub, map_sum]
  have hh := half_le_one' (p := p) n
  have hG : pi2 p R (GamR (p := p) v u b (half p n) (n / p)) =
      Gen.Gam (sgS (p := p) (R := R) v u) b (half p n) (n / p) := by
    rw [Gam_sgS_eq, min_eq_left hh]
  rw [hG]
  simp only [map_mul]
  have hβ : ∑ j ∈ Cper κ k' (oc p κ π (n % p)), pi2 p R (Bm (p := p) v u ξ (half p n) (n / p) j) *
      pi2 p R (YrF (p := p) v u κ k' ξ b (half p n) (oc p κ π (n % p)) j) =
      ∑ j ∈ Cper κ k' (oc p κ π (n % p)), BmS (p := p) v u ξ (half p n) (n / p) j *
      YvS (p := p) (R := R) (YrF (p := p) v u κ k' ξ) b (half p n) (oc p κ π (n % p)) j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold BmS YvS
    rw [min_eq_left hh]
  rw [hβ]
  unfold epsS Gen.eps
  ring

end VecLab

section SchurIface

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] (κ k' π : ℕ) (ξ : R)
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] (zn : I → ℕ) (yn : J → ℕ)

/-- The matrix `Q = p³ H` on `(Ω ⊕ I) × (Ω ⊕ J)`: pivot rows `rowNode`, pivot columns `colNode`, outside rows
`zn` and outside columns `yn`. -/
noncomputable def Hq : Matrix (PivIdx p κ k' ⊕ I) (PivIdx p κ k' ⊕ J) R :=
  Matrix.of fun x y => Qent (p := p) v u hv hu ξ (Sum.elim (rowNode p κ k' π) zn x)
    (Sum.elim (colNode p κ k' π) yn y)

/-- The node of a row-type label. -/
def nR : I ⊕ PivIdx p κ k' → ℕ := Sum.elim zn (colNode p κ k' π)
/-- The node of a column-type label. -/
def nC : J ⊕ PivIdx p κ k' → ℕ := Sum.elim yn (rowNode p κ k' π)

variable {κ k' π ξ}

theorem Qm_Hq : Schur.Qm (Hq (p := p) v u hv hu κ k' π ξ zn yn) = Qp (p := p) v u hv hu κ k' π ξ := rfl

theorem Lm_symm (a b : ℕ) : Lm v u hv hu a b = Lm v u hv hu b a := by
  unfold Lm lw
  by_cases hab : a = b
  · subst hab; rfl
  · rw [if_neg hab, if_neg (Ne.symm hab)]
    have h1 : (b : ℚ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hab))
    have h2 : (a : ℚ) - b ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hab)
    field_simp
    ring

theorem Qent_symm (ξ : R) (a b : ℕ) :
    Qent (p := p) v u hv hu ξ a b = Qent (p := p) v u hv hu ξ b a := by
  unfold Qent
  rw [Lm_symm v u hv hu a b]
  by_cases hab : a = b
  · subst hab; rfl
  · rw [if_neg hab, if_neg (Ne.symm hab)]

theorem Qp_transpose (hπ : π ≤ 1) :
    Qp (p := p) v u hv hu κ k' (1 - π) ξ = (Qp (p := p) v u hv hu κ k' π ξ)ᵀ := by
  ext x y
  simp only [Qp, Matrix.of_apply, Matrix.transpose_apply]
  have h1 : (1 - (1 - π)) = π := by omega
  rw [rowNode_eq_colNode κ k' (1 - π) (by omega), h1, ← rowNode_eq_colNode κ k' π hπ]
  exact Qent_symm v u hv hu ξ _ _

theorem Zp_transpose (hπ : π ≤ 1) :
    Zp (p := p) v u hv hu κ k' (1 - π) ξ = (Zp (p := p) v u hv hu κ k' π ξ)ᵀ := by
  unfold Zp
  rw [Qp_transpose v u hv hu hπ, Matrix.transpose_nonsing_inv]

theorem colNode_one_sub (hπ : π ≤ 1) (x : PivIdx p κ k') :
    colNode p κ k' (1 - π) x = rowNode p κ k' π x := (rowNode_eq_colNode κ k' π hπ x).symm

theorem rowNode_one_sub (hπ : π ≤ 1) (x : PivIdx p κ k') :
    rowNode p κ k' (1 - π) x = colNode p κ k' π x := by
  rw [rowNode_eq_colNode κ k' (1 - π) (by omega), Nat.sub_sub_self hπ]

variable (κ k' π ξ)

/-- Row-type label vectors `R1` (b = 0) and `ρ0` (b = 1): outside rows and pivot columns. -/
noncomputable def labR (b : ℕ) : I ⊕ PivIdx p κ k' → R :=
  Sum.elim (fun z => Vout (p := p) v u hv hu κ k' π ξ b (zn z)) (gv (p := p) v u hv hu κ k' π ξ b)

/-- Column-type label vectors `C0` (b = 0) and `γ1` (b = 1): the transposed system `1 − π`. -/
noncomputable def labC (b : ℕ) : J ⊕ PivIdx p κ k' → R :=
  Sum.elim (fun w => Vout (p := p) v u hv hu κ k' (1 - π) ξ b (yn w))
    (gv (p := p) v u hv hu κ k' (1 - π) ξ b)

variable {κ k' π ξ}

/-- The data of the Schur transform for the plane 2 matrix. -/
noncomputable def aF : PivIdx p κ k' ⊕ I → R := fun x => ((Sum.elim (rowNode p κ k' π) zn x : ℕ) : R)
noncomputable def bF : PivIdx p κ k' ⊕ J → R := fun y => ((Sum.elim (colNode p κ k' π) yn y : ℕ) : R)
noncomputable def phiF : PivIdx p κ k' ⊕ I → R :=
  fun x => (p : R) * f2 (p := p) v u hv hu (Sum.elim (rowNode p κ k' π) zn x)
noncomputable def psiF : PivIdx p κ k' ⊕ J → R :=
  fun y => (p : R) * f2 (p := p) v u hv hu (Sum.elim (colNode p κ k' π) yn y)

theorem isDisp_Hq (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hzn : ∀ z, zn z < N) (hyn : ∀ w, yn w < N) :
    Schur.IsDisp (Hq (p := p) v u hv hu κ k' π ξ zn yn) (aF (p := p) (κ := κ) (k' := k') (π := π) zn)
      (bF (p := p) (κ := κ) (k' := k') (π := π) yn) (phiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) zn)
      (psiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) yn) := by
  intro r c
  have hr : Sum.elim (rowNode p κ k' π) zn r < N := by
    rcases r with x | z
    · exact rowNode_lt hH x
    · exact hzn z
  have hc : Sum.elim (colNode p κ k' π) yn c < N := by
    rcases c with x | w
    · exact colNode_lt hH x
    · exact hyn w
  simp only [Hq, Matrix.of_apply, aF, bF, phiF, psiF]
  exact Qent_disp v u hv hu hodd hN ξ hr hc

section Gens

variable (κ k' π ξ)

theorem Rvec_zero : Rvec (p := p) (R := R) v u hv hu κ k' π 0 = fun _ => 1 := by
  funext x; simp [Rvec]

omit [DecidableEq J] in
theorem R1_eq (hπ : π ≤ 1) :
    Schur.R1 (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ)
      = labR (p := p) v u hv hu κ k' π ξ zn 0 := by
  funext r
  rcases r with z | y
  · simp only [Schur.R1, Sum.elim_inl, labR, Vout, outG, if_true]
    unfold Schur.gA gv
    rw [Rvec_zero]
    simp [Matrix.mulVec, dotProduct, Schur.Vm, Hq, Matrix.submatrix_apply]
  · simp only [Schur.R1, Sum.elim_inr, labR]
    unfold Schur.gA gv
    rw [Rvec_zero]

omit [DecidableEq J] in
theorem R0_eq (hπ : π ≤ 1) :
    Schur.R0 (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ)
      (phiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) zn)
      = fun r => (p : R) * labR (p := p) v u hv hu κ k' π ξ zn 1 r := by
  have hg : Schur.gB (Zp (p := p) v u hv hu κ k' π ξ) (phiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) zn) =
      fun t => (p : R) * gv (p := p) v u hv hu κ k' π ξ 1 t := by
    funext t
    simp only [Schur.gB, gv, Rvec, phiF, Function.comp_apply, Sum.elim_inl, one_ne_zero, if_false,
      Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => by ring
  funext r
  rcases r with z | y
  · simp only [Schur.R0, Sum.elim_inl, labR, Vout, outG, one_ne_zero, if_false]
    rw [hg]
    simp only [phiF, Sum.elim_inr, Matrix.mulVec, dotProduct, Schur.Vm, Hq, Matrix.submatrix_apply,
      Matrix.of_apply, Sum.elim_inl, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => by ring
  · simp only [Schur.R0, Sum.elim_inr, labR]
    rw [hg]

omit [DecidableEq I] in
theorem C0_eq (hπ : π ≤ 1) :
    Schur.C0 (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ)
      = labC (p := p) v u hv hu κ k' π ξ yn 0 := by
  have hA : Schur.gA' (Zp (p := p) v u hv hu κ k' π ξ) =
      gv (p := p) v u hv hu κ k' (1 - π) ξ 0 := by
    unfold Schur.gA' gv
    rw [Rvec_zero, Zp_transpose v u hv hu hπ, Matrix.mulVec_transpose]
  funext c
  rcases c with w | x
  · simp only [Schur.C0, Sum.elim_inl, labC, Vout, outG, if_true]
    rw [hA]
    simp only [Matrix.vecMul, dotProduct, Schur.Um, Hq, Matrix.submatrix_apply, Matrix.of_apply,
      Sum.elim_inl, Sum.elim_inr]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [colNode_one_sub hπ, Qent_symm v u hv hu ξ (rowNode p κ k' π y) (yn w)]
    ring
  · simp only [Schur.C0, Sum.elim_inr, labC]
    rw [hA]

omit [DecidableEq I] in
theorem C1_eq (hπ : π ≤ 1) :
    Schur.C1 (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ)
      (psiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) yn)
      = fun c => (p : R) * labC (p := p) v u hv hu κ k' π ξ yn 1 c := by
  have hg : Schur.gB' (Zp (p := p) v u hv hu κ k' π ξ) (psiF (p := p) v u hv hu (κ := κ) (k' := k') (π := π) yn) =
      fun x => (p : R) * gv (p := p) v u hv hu κ k' (1 - π) ξ 1 x := by
    funext x
    simp only [Schur.gB', gv, Rvec, psiF, Function.comp_apply, Sum.elim_inl, one_ne_zero, if_false,
      Zp_transpose v u hv hu hπ, Matrix.vecMul, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Finset.mul_sum, rowNode_one_sub hπ]
    refine Finset.sum_congr rfl fun s _ => by ring
  funext c
  rcases c with w | x
  · simp only [Schur.C1, Sum.elim_inl, labC, Vout, outG, one_ne_zero, if_false]
    rw [hg]
    simp only [psiF, Sum.elim_inr, Matrix.vecMul, dotProduct, Schur.Um, Hq, Matrix.submatrix_apply,
      Matrix.of_apply, Sum.elim_inl, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [colNode_one_sub hπ, Qent_symm v u hv hu ξ (rowNode p κ k' π y) (yn w)]
    ring
  · simp only [Schur.C1, Sum.elim_inr, labC]
    rw [hg]

end Gens

section PropW

variable (κ k' π ξ)

/-- The pattern of a label: `Γ − β` for an outside label, `Y` for a pivot label. -/
noncomputable def patF (isOut : Bool) (b h o l : ℕ) : R :=
  if isOut then Gout (p := p) v u κ k' ξ b h o l else YrF (p := p) v u κ k' ξ b h o l

/-- The weight of a pair of labels, from the nodes `(nR, nC)`, the kinds and the classes: `3` if the nodes
are congruent, `0` in one cell and `1` in one period (other half) if the pattern agrees, else `2`. -/
def Wlab (p : ℕ) (kR kC : Bool) (oR oC n m : ℕ) : ℕ :=
  if n % p = m % p then 3
  else if kR = kC ∧ oR = oC ∧ n / p = m / p then (if half p n = half p m then 0 else 1) else 2

variable {κ k' π ξ}

theorem Wlab_le (p : ℕ) (kR kC : Bool) (oR oC n m : ℕ) : Wlab p kR kC oR oC n m ≤ 3 := by
  unfold Wlab; split_ifs <;> omega

omit [DecidableEq I] [DecidableEq J] in
theorem voutPat (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (σ : ℕ) {n : ℕ} (hn : n < N) :
    ∃ e : R, ∀ b, b ≤ 1 → (p : R) ^ 2 ∣ Vout (p := p) v u hv hu κ k' σ ξ b n -
      e * Gout (p := p) v u κ k' ξ b (half p n) (oc p κ σ (n % p)) (n / p) := by
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (epsS (p := p) v u κ k' σ ξ (n % p))
  refine ⟨e, fun b hb => ?_⟩
  rw [← pi2_eq_iff, map_mul, pi2_Vout v u hv hu hU hpv hodd hp5 hN hH hRad hb hn]
  have : pi2 p R e = epsS (p := p) v u κ k' σ ξ (n % p) := he
  rw [this]

omit [DecidableEq I] [DecidableEq J] in
theorem gvPat (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (σ : ℕ) (y : PivIdx p κ k') :
    ∃ e : R, ∀ b, b ≤ 1 → (p : R) ^ 2 ∣ gv (p := p) v u hv hu κ k' σ ξ b y -
      e * YrF (p := p) v u κ k' ξ b (half p (colNode p κ k' σ y)) (oc p κ σ (colNode p κ k' σ y % p))
        (colNode p κ k' σ y / p) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨e, he⟩ := Ideal.Quotient.mk_surjective (epsS (p := p) v u κ k' σ ξ y.1)
  refine ⟨e, fun b hb => ?_⟩
  rw [← pi2_eq_iff, map_mul, pi2_gv v u hv hu hU hpv hodd hp5 hN hH hRad hb y]
  have : pi2 p R e = epsS (p := p) v u κ k' σ ξ y.1 := he
  rw [this, colNode_mod, colNode_div hp0]
  have hh : half p (colNode p κ k' σ y) = half p y.1 := by
    unfold colNode; rw [half_node hp0 _ _ y.1.2]
  rw [hh]
  unfold Th YvS
  rw [min_eq_left (half_le_one' _)]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem omega_sq (A0 A1 B0 B1 e e' P0 P1 : R) (hA0 : (p : R) ^ 2 ∣ A0 - e * P0)
    (hA1 : (p : R) ^ 2 ∣ A1 - e * P1) (hB0 : (p : R) ^ 2 ∣ B0 - e' * P0)
    (hB1 : (p : R) ^ 2 ∣ B1 - e' * P1) : (p : R) ^ 2 ∣ A1 * B0 - A0 * B1 := by
  rw [← pi2_eq_zero_iff]
  have a0 := pi2_eq_iff.2 hA0
  have a1 := pi2_eq_iff.2 hA1
  have b0 := pi2_eq_iff.2 hB0
  have b1 := pi2_eq_iff.2 hB1
  rw [map_sub, map_mul, map_mul, a0, a1, b0, b1]
  simp only [map_mul]
  ring

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem omega_one (A0 A1 B0 B1 e e' P0 P1 Q0 Q1 : R) (hA0 : (p : R) ^ 2 ∣ A0 - e * P0)
    (hA1 : (p : R) ^ 2 ∣ A1 - e * P1) (hB0 : (p : R) ^ 2 ∣ B0 - e' * Q0)
    (hB1 : (p : R) ^ 2 ∣ B1 - e' * Q1) (h0 : (p : R) ∣ P0 - Q0) (h1 : (p : R) ∣ P1 - Q1) :
    (p : R) ∣ A1 * B0 - A0 * B1 := by
  set mk := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hmk
  have key : ∀ x y : R, (p : R) ∣ x - y → mk x = mk y := fun x y h => by
    rw [hmk, Ideal.Quotient.eq, Ideal.mem_span_singleton]; exact h
  have sq : ∀ z : R, (p : R) ^ 2 ∣ z → (p : R) ∣ z := fun z h => (dvd_pow_self (p : R) two_ne_zero).trans h
  have a0 := key _ _ (sq _ hA0)
  have a1 := key _ _ (sq _ hA1)
  have b0 := key _ _ (sq _ hB0)
  have b1 := key _ _ (sq _ hB1)
  have c0 := key _ _ h0
  have c1 := key _ _ h1
  have : mk (A1 * B0 - A0 * B1) = 0 := by
    rw [map_sub, map_mul, map_mul, a0, a1, b0, b1]
    simp only [map_mul]
    have c0' : mk Q0 = mk P0 := c0.symm
    have c1' : mk Q1 = mk P1 := c1.symm
    rw [c0', c1']
    ring
  have := Ideal.Quotient.eq_zero_iff_mem.1 this
  exact Ideal.mem_span_singleton.1 this

theorem patF_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v)
    (hH : (κ + 2 * k') * p ≤ N) (isOut : Bool) {o l : ℕ} (b : ℕ) (hl : (l + 1) * p ≤ N)
    (hlc : isOut = false → l ∈ Cper κ k' o) (ho : o ≤ 1) :
    (p : R) ∣ patF (p := p) v u κ k' ξ isOut b 1 o l - patF (p := p) v u κ k' ξ isOut b 0 o l := by
  cases isOut
  · simp only [patF, Bool.false_eq_true, if_false]
    exact YrF_half v u hU hpv hodd hN hH b o ho l (hlc rfl)
  · simp only [patF, if_true, Gout]
    have e : (GamR (p := p) v u b 1 l - ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ 1 l j * YrF (p := p) v u κ k' ξ b 1 o j) -
        (GamR (p := p) v u b 0 l - ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ 0 l j * YrF (p := p) v u κ k' ξ b 0 o j) =
        (GamR (p := p) v u b 1 l - GamR (p := p) v u b 0 l) -
          ∑ j ∈ Cper κ k' o, ((Bm (p := p) v u ξ 1 l j - Bm (p := p) v u ξ 0 l j) * YrF (p := p) v u κ k' ξ b 1 o j +
            Bm (p := p) v u ξ 0 l j * (YrF (p := p) v u κ k' ξ b 1 o j - YrF (p := p) v u κ k' ξ b 0 o j)) := by
      have : ∀ j ∈ Cper κ k' o, Bm (p := p) v u ξ 1 l j * YrF (p := p) v u κ k' ξ b 1 o j -
          Bm (p := p) v u ξ 0 l j * YrF (p := p) v u κ k' ξ b 0 o j =
          (Bm (p := p) v u ξ 1 l j - Bm (p := p) v u ξ 0 l j) * YrF (p := p) v u κ k' ξ b 1 o j +
            Bm (p := p) v u ξ 0 l j * (YrF (p := p) v u κ k' ξ b 1 o j - YrF (p := p) v u κ k' ξ b 0 o j) :=
        fun j _ => by ring
      have hs : ∑ j ∈ Cper κ k' o, ((Bm (p := p) v u ξ 1 l j - Bm (p := p) v u ξ 0 l j) * YrF (p := p) v u κ k' ξ b 1 o j +
            Bm (p := p) v u ξ 0 l j * (YrF (p := p) v u κ k' ξ b 1 o j - YrF (p := p) v u κ k' ξ b 0 o j)) =
          ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ 1 l j * YrF (p := p) v u κ k' ξ b 1 o j -
          ∑ j ∈ Cper κ k' o, Bm (p := p) v u ξ 0 l j * YrF (p := p) v u κ k' ξ b 0 o j := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j hj => (this j hj).symm)
      rw [hs]; ring
    rw [e]
    refine dvd_sub ?_ (Finset.dvd_sum fun j hj => ?_)
    · unfold GamR
      by_cases hb : b = 0
      · simp [hb]
      · simp only [hb, if_false]; exact sigR_halves v u hodd hN hl
    · have hjlt : j < κ + 2 * k' := ((mem_Cper (κ := κ) (k' := k')).1 hj).1
      have hjc : (j + 1) * p ≤ N := by nlinarith
      exact dvd_add (Dvd.dvd.mul_right (Bm_halves v u hodd hN ξ hl hjc) _)
        (Dvd.dvd.mul_left (YrF_half v u hU hpv hodd hN hH b o ho j hj) _)

theorem isUnit_natDiff {a b : ℕ} (h : a % p ≠ b % p) : IsUnit ((a : R) - (b : R)) := by
  have hz : ¬ (p : ℤ) ∣ (a : ℤ) - b := fun hd => h ((dvd_sub_iff (p := p) a b).1 hd)
  have hz0 : ((a : ℤ) - b : ℚ) ≠ 0 := by
    intro h0
    apply hz
    have : ((a : ℤ) - b : ℤ) = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  have h1 : (((a : ℤ) - b : ℤ) : LocRing p) * invZ p ((a : ℤ) - b) = 1 := by
    apply Subtype.ext
    simp only [Subring.coe_mul, coe_invZ, if_neg hz]
    push_cast
    push_cast at hz0
    field_simp
  have hu : IsUnit (((a : ℤ) - b : ℤ) : LocRing p) := IsUnit.of_mul_eq_one _ h1
  have := hu.map (algebraMap (LocRing p) R)
  simpa using this

section SwProps

variable (κ k' π ξ)

/-- Pattern of a row-type label. -/
noncomputable def patR (r : I ⊕ PivIdx p κ k') (b : ℕ) : R :=
  patF (p := p) v u κ k' ξ r.isLeft b (half p (nR (p := p) (κ := κ) (k' := k') (π := π) zn r))
    (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
    (nR (p := p) (κ := κ) (k' := k') (π := π) zn r / p)

/-- Pattern of a column-type label. -/
noncomputable def patC (c : J ⊕ PivIdx p κ k') (b : ℕ) : R :=
  patF (p := p) v u κ k' ξ c.isLeft b (half p (nC (p := p) (κ := κ) (k' := k') (π := π) yn c))
    (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
    (nC (p := p) (κ := κ) (k' := k') (π := π) yn c / p)

variable {κ k' π ξ}

theorem lt_of_complete {n : ℕ} (hp0 : 0 < p) (h : (n / p + 1) * p ≤ N) : n < N := by
  have := Nat.div_add_mod n p
  have h2 := Nat.mod_lt n hp0
  nlinarith

theorem sw_mul (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1)
    (hzn : ∀ z, zn z < N) (hyn : ∀ w, yn w < N) (r : I ⊕ PivIdx p κ k') (c : J ⊕ PivIdx p κ k') :
    (((nR (p := p) (κ := κ) (k' := k') (π := π) zn r : ℕ) : R) -
        ((nC (p := p) (κ := κ) (k' := k') (π := π) yn c : ℕ) : R)) *
      Schur.Sw (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ) r c =
    (p : R) * (labR (p := p) v u hv hu κ k' π ξ zn 1 r * labC (p := p) v u hv hu κ k' π ξ yn 0 c -
      labR (p := p) v u hv hu κ k' π ξ zn 0 r * labC (p := p) v u hv hu κ k' π ξ yn 1 c) := by
  have hZ1 : Schur.Qm (Hq (p := p) v u hv hu κ k' π ξ zn yn) * Zp (p := p) v u hv hu κ k' π ξ = 1 := by
    rw [Qm_Hq]; exact Qp_mul_Zp v u hv hu hU hpv hodd hp5 hN hH hRad
  have hZ2 : Zp (p := p) v u hv hu κ k' π ξ * Schur.Qm (Hq (p := p) v u hv hu κ k' π ξ zn yn) = 1 := by
    rw [Qm_Hq]; exact Zp_mul_Qp v u hv hu hU hpv hodd hp5 hN hH hRad
  have h := Schur.pivot_displacement (isDisp_Hq v u hv hu zn yn hodd hN hH hzn hyn (ξ := ξ) (π := π)) hZ1 hZ2 r c
  have e0 := congrFun (R0_eq v u hv hu κ k' π ξ zn yn hπ) r
  have e1 := congrFun (R1_eq v u hv hu κ k' π ξ zn yn hπ) r
  have e2 := congrFun (C0_eq v u hv hu κ k' π ξ zn yn hπ) c
  have e3 := congrFun (C1_eq v u hv hu κ k' π ξ zn yn hπ) c
  have hnr : Schur.nodeR (aF (p := p) (κ := κ) (k' := k') (π := π) zn) (bF (p := p) (κ := κ) (k' := k') (π := π) yn) r =
      ((nR (p := p) (κ := κ) (k' := k') (π := π) zn r : ℕ) : R) := by
    rcases r with z | y <;> rfl
  have hnc : Schur.nodeC (aF (p := p) (κ := κ) (k' := k') (π := π) zn) (bF (p := p) (κ := κ) (k' := k') (π := π) yn) c =
      ((nC (p := p) (κ := κ) (k' := k') (π := π) yn c : ℕ) : R) := by
    rcases c with w | x <;> rfl
  rw [hnr, hnc, e0, e1, e2, e3] at h
  linear_combination h

theorem rowLab (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hzn : ∀ z, zn z < N) (r : I ⊕ PivIdx p κ k') :
    ∃ e : R, ∀ b, b ≤ 1 → (p : R) ^ 2 ∣ labR (p := p) v u hv hu κ k' π ξ zn b r -
      e * patR (p := p) v u κ k' π ξ zn r b := by
  rcases r with z | y
  · obtain ⟨e, he⟩ := voutPat v u hv hu hU hpv hodd hp5 hN hH hRad π (hzn z)
    exact ⟨e, fun b hb => by simpa [labR, patR, patF, nR] using he b hb⟩
  · obtain ⟨e, he⟩ := gvPat v u hv hu hU hpv hodd hp5 hN hH hRad π y
    exact ⟨e, fun b hb => by simpa [labR, patR, patF, nR] using he b hb⟩

theorem colLab (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1) (hyn : ∀ w, yn w < N)
    (c : J ⊕ PivIdx p κ k') :
    ∃ e : R, ∀ b, b ≤ 1 → (p : R) ^ 2 ∣ labC (p := p) v u hv hu κ k' π ξ yn b c -
      e * patC (p := p) v u κ k' π ξ yn c b := by
  rcases c with w | x
  · obtain ⟨e, he⟩ := voutPat v u hv hu hU hpv hodd hp5 hN hH hRad (1 - π) (hyn w)
    exact ⟨e, fun b hb => by simpa [labC, patC, patF, nC] using he b hb⟩
  · obtain ⟨e, he⟩ := gvPat v u hv hu hU hpv hodd hp5 hN hH hRad (1 - π) x
    refine ⟨e, fun b hb => ?_⟩
    have := he b hb
    simp only [labC, patC, patF, nC, Sum.elim_inr, Sum.isLeft_inr, Bool.false_eq_true, if_false]
    rw [rowNode_eq_colNode κ k' π hπ]
    exact this

theorem pivR_mem {σ : ℕ} (y : PivIdx p κ k') :
    colNode p κ k' σ y / p ∈ Cper κ k' (oc p κ σ (colNode p κ k' σ y % p)) := by
  have hp0 : 0 < p := hp.out.pos
  rw [colNode_mod, colNode_div hp0]
  exact colPer_mem κ k' _ (oc_le y.1) y.2

theorem pivC_mem (hπ : π ≤ 1) (x : PivIdx p κ k') :
    rowNode p κ k' π x / p ∈ Cper κ k' (oc p κ (1 - π) (rowNode p κ k' π x % p)) := by
  have hp0 : 0 < p := hp.out.pos
  rw [rowNode_mod, rowNode_div hp0, oc_one_sub (p := p) κ π hπ]
  exact rowPer_mem κ k' _ (oc_le x.1) x.2


theorem nR_compl (hzc : ∀ z, (zn z / p + 1) * p ≤ N) (hH : (κ + 2 * k') * p ≤ N)
    (r : I ⊕ PivIdx p κ k') : (nR (p := p) (κ := κ) (k' := k') (π := π) zn r / p + 1) * p ≤ N := by
  have hp0 : 0 < p := hp.out.pos
  rcases r with z | y
  · exact hzc z
  · show (colNode p κ k' π y / p + 1) * p ≤ N
    rw [colNode_div hp0]
    have := colPer_lt (κ := κ) (k' := k') _ (oc_le (π := π) (κ := κ) (p := p) y.1) y.2
    nlinarith

theorem nC_compl (hyc : ∀ w, (yn w / p + 1) * p ≤ N) (hH : (κ + 2 * k') * p ≤ N)
    (c : J ⊕ PivIdx p κ k') : (nC (p := p) (κ := κ) (k' := k') (π := π) yn c / p + 1) * p ≤ N := by
  have hp0 : 0 < p := hp.out.pos
  rcases c with w | x
  · exact hyc w
  · show (rowNode p κ k' π x / p + 1) * p ≤ N
    rw [rowNode_div hp0]
    have := rowPer_lt (κ := κ) (k' := k') _ (oc_le (π := π) (κ := κ) (p := p) x.1) x.2
    nlinarith

/-- The weight of the pair of labels `(r, c)`. -/
noncomputable def wR (r : I ⊕ PivIdx p κ k') (c : J ⊕ PivIdx p κ k') : ℕ :=
  Wlab p r.isLeft c.isLeft (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
    (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
    (nR (p := p) (κ := κ) (k' := k') (π := π) zn r) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c)

/-- **Proposition W.**  The entry `Sw(r, c)` of the pivotal transform is divisible by `p^(3 − W)`, where
`W = 3` for congruent nodes, `0` (one cell), `1` (one period, other half) when the patterns agree, else `2`. -/
theorem sw_dvd (hU : UnitProp p ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) (hπ : π ≤ 1)
    (hzc : ∀ z, (zn z / p + 1) * p ≤ N) (hyc : ∀ w, (yn w / p + 1) * p ≤ N)
    (r : I ⊕ PivIdx p κ k') (c : J ⊕ PivIdx p κ k') :
    (p : R) ^ (3 - wR (p := p) (κ := κ) (k' := k') (π := π) zn yn r c) ∣
      Schur.Sw (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ) r c := by
  have hp0 : 0 < p := hp.out.pos
  have hzn : ∀ z, zn z < N := fun z => lt_of_complete hp0 (hzc z)
  have hyn : ∀ w, yn w < N := fun w => lt_of_complete hp0 (hyc w)
  unfold wR
  by_cases hcg : nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p =
      nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p
  · have : Wlab p r.isLeft c.isLeft
        (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
        (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
        (nR (p := p) (κ := κ) (k' := k') (π := π) zn r) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 3 := by
      unfold Wlab; rw [if_pos hcg]
    rw [this, Nat.sub_self, pow_zero]; exact one_dvd _
  · obtain ⟨U, hUU⟩ := isUnit_natDiff (R := R) hcg
    have hmul := sw_mul v u hv hu zn yn hU hpv hodd hp5 hN hH hRad hπ hzn hyn r c
    rw [← hUU] at hmul
    have hSw : Schur.Sw (Hq (p := p) v u hv hu κ k' π ξ zn yn) (Zp (p := p) v u hv hu κ k' π ξ) r c =
        ((U⁻¹ : Rˣ) : R) * ((p : R) * (labR (p := p) v u hv hu κ k' π ξ zn 1 r *
          labC (p := p) v u hv hu κ k' π ξ yn 0 c - labR (p := p) v u hv hu κ k' π ξ zn 0 r *
          labC (p := p) v u hv hu κ k' π ξ yn 1 c)) := by
      rw [← hmul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hSw]
    refine Dvd.dvd.mul_left ?_ _
    by_cases hpat : r.isLeft = c.isLeft ∧
        oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p) =
          oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p) ∧
        nR (p := p) (κ := κ) (k' := k') (π := π) zn r / p = nC (p := p) (κ := κ) (k' := k') (π := π) yn c / p
    · obtain ⟨hk, ho, hl⟩ := hpat
      obtain ⟨e, he⟩ := rowLab v u hv hu zn hU hpv hodd hp5 hN hH hRad hzn r
      obtain ⟨e', he'⟩ := colLab v u hv hu yn hU hpv hodd hp5 hN hH hRad hπ hyn c
      by_cases hh : half p (nR (p := p) (κ := κ) (k' := k') (π := π) zn r) =
          half p (nC (p := p) (κ := κ) (k' := k') (π := π) yn c)
      · have hW : Wlab p r.isLeft c.isLeft
            (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
            (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
            (nR (p := p) (κ := κ) (k' := k') (π := π) zn r)
            (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 0 := by
          unfold Wlab; rw [if_neg hcg, if_pos ⟨hk, ho, hl⟩, if_pos hh]
        rw [hW]
        have hP : ∀ b, patR (p := p) v u κ k' π ξ zn r b = patC (p := p) v u κ k' π ξ yn c b := by
          intro b; unfold patR patC; rw [hk, ← ho, ← hl, hh]
        have := omega_sq (p := p) (labR (p := p) v u hv hu κ k' π ξ zn 0 r)
          (labR (p := p) v u hv hu κ k' π ξ zn 1 r) (labC (p := p) v u hv hu κ k' π ξ yn 0 c)
          (labC (p := p) v u hv hu κ k' π ξ yn 1 c) e e' (patR (p := p) v u κ k' π ξ zn r 0)
          (patR (p := p) v u κ k' π ξ zn r 1) (he 0 (by norm_num)) (he 1 (by norm_num))
          (by rw [hP 0]; exact he' 0 (by norm_num)) (by rw [hP 1]; exact he' 1 (by norm_num))
        have e3 : (p : R) ^ (3 - 0) = (p : R) * (p : R) ^ 2 := by norm_num; ring
        rw [e3]; exact mul_dvd_mul_left _ this
      · have hW : Wlab p r.isLeft c.isLeft
            (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
            (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
            (nR (p := p) (κ := κ) (k' := k') (π := π) zn r)
            (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 1 := by
          unfold Wlab; rw [if_neg hcg, if_pos ⟨hk, ho, hl⟩, if_neg hh]
        rw [hW]
        have hcompl := nR_compl (p := p) (κ := κ) (k' := k') (π := π) (N := N) zn hzc hH r
        have hlc : r.isLeft = false → nR (p := p) (κ := κ) (k' := k') (π := π) zn r / p ∈
            Cper κ k' (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p)) := by
          intro hl'
          rcases r with z | y
          · simp at hl'
          · exact pivR_mem y
        have hQ : ∀ b, b ≤ 1 → (p : R) ∣ patR (p := p) v u κ k' π ξ zn r b -
            patC (p := p) v u κ k' π ξ yn c b := by
          intro b _
          have hf := patF_halves v u hodd hN hU hpv hH r.isLeft
            (o := oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
            (l := nR (p := p) (κ := κ) (k' := k') (π := π) zn r / p) b hcompl hlc (oc_le _)
          unfold patR patC
          rw [← hk, ← ho, ← hl]
          rcases half_eq (p := p) (nR (p := p) (κ := κ) (k' := k') (π := π) zn r) with h0 | h1
          · rw [h0] at hh
            have h1' : half p (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 1 := by
              rcases half_eq (p := p) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) with h | h
              · exact absurd h.symm hh
              · exact h
            rw [h0, h1']
            have := dvd_neg.2 hf
            simpa using this
          · rw [h1]
            have h0' : half p (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 0 := by
              rcases half_eq (p := p) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) with h | h
              · exact h
              · exact absurd (by rw [h1, h]) hh
            rw [h0']
            exact hf
        have := omega_one (p := p) (labR (p := p) v u hv hu κ k' π ξ zn 0 r)
          (labR (p := p) v u hv hu κ k' π ξ zn 1 r) (labC (p := p) v u hv hu κ k' π ξ yn 0 c)
          (labC (p := p) v u hv hu κ k' π ξ yn 1 c) e e' (patR (p := p) v u κ k' π ξ zn r 0)
          (patR (p := p) v u κ k' π ξ zn r 1) (patC (p := p) v u κ k' π ξ yn c 0)
          (patC (p := p) v u κ k' π ξ yn c 1) (he 0 (by norm_num)) (he 1 (by norm_num))
          (he' 0 (by norm_num)) (he' 1 (by norm_num)) (hQ 0 (by norm_num)) (hQ 1 (by norm_num))
        have e3 : (p : R) ^ (3 - 1) = (p : R) * (p : R) := by norm_num [pow_two]
        rw [e3]; exact mul_dvd_mul_left _ this
    · have hW : Wlab p r.isLeft c.isLeft
          (oc p κ π (nR (p := p) (κ := κ) (k' := k') (π := π) zn r % p))
          (oc p κ (1 - π) (nC (p := p) (κ := κ) (k' := k') (π := π) yn c % p))
          (nR (p := p) (κ := κ) (k' := k') (π := π) zn r)
          (nC (p := p) (κ := κ) (k' := k') (π := π) yn c) = 2 := by
        unfold Wlab; rw [if_neg hcg, if_neg hpat]
      rw [hW]
      simp


/-- **Lemma C, parity**: the class of the residue of a node `n` for the system `σ` (`σ ∈ {0,1}` is the
parity of the pivot columns of period `κ`) is read off the parity of `n` and of its period:
`o(ω_n) = (n/p + κ) mod 2` if `n ≡ σ (mod 2)`, else `(n/p + κ + 1) mod 2`. -/
theorem oc_node (hodd : p % 2 = 1) {σ : ℕ} (hσ : σ ≤ 1) (n : ℕ) :
    oc p κ σ (n % p) = if n % 2 = σ then (n / p + κ) % 2 else (n / p + κ + 1) % 2 := by
  have hn := Nat.div_add_mod n p
  have h1 : (p * (n / p)) % 2 = (n / p) % 2 := by
    rw [Nat.mul_mod, hodd]; simp
  have h2 : (p * κ) % 2 = κ % 2 := by
    rw [Nat.mul_mod, hodd]; simp
  unfold oc
  rw [Nat.mul_comm κ p]
  generalize p * (n / p) = X at hn h1
  generalize p * κ = Y at h2 ⊢
  generalize n % p = w at hn ⊢
  generalize n / p = a at h1 ⊢
  split_ifs <;> omega

end SwProps

end PropW

end SchurIface

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.sw_dvd
#print axioms CatalanCore.Uniform.Content.Sweep.pi2_Vout
#print axioms CatalanCore.Uniform.Content.Sweep.oc_node
