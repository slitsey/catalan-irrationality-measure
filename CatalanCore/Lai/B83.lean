module

public import CatalanCore.Lai.B83BasisBridge
public import CatalanCore.Lai.B83DNode
public import CatalanCore.Lai.B83HalfBridge
public import CatalanCore.Lai.NV

@[expose] public section

/-! # `CatalanCore.Lai.B83`: Theorem B83 (ledger LB09), the final assembly

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §2-3.  Let `n ≥ 4` and `p` prime with `8n/3 < p < 3n - 1`
(the band; it forces `p ≥ 17`, hence `p ∉ {2, 3, 5}`), `p ∉ {13, 24359}`, `a, b ∈ ℤ_(p)` with `b` a unit and
`v_p(X) ≥ -3`.  Then `J_n(a, b, X) ≠ 0`.

* `diagA_of`, `diagC_of`: the plain-basis diagonal blocks `DiagA`, `DiagC` of `B83Bridge`, as the sum of the
  own nodes (`B83.own_entry_A/C`), the D-nodes (`dnode_A/C`) and the other residues (`cross_nodeB`, above
  threshold), split by `entB_split_own` (from `entB_split`);
* `hBB_band`: the reduced half block, from `B83HalfBridge.half_block_unit` through `hBB_of`;
* `b83_core`: `J_n(a, b, X'/p³) ≠ 0` (`B83Bridge.det_gramF_ne_zero` and the Gram criterion);
* `nv_plane_B83` (`ℓ⁴ ∤ q ⇒ J_n(a, b, x) ≠ 0`), `nv_ratio_B83` (`ℓ ∤ p ⇒ J_n(q, -p, 0) ≠ 0`).

The paper's exact valuation `v_p(J_n) = -21n + 7p - 7` is not stated: it needs the valuation of the change
of basis from `elF` to the monomials, and the criterion only uses `J_n ≠ 0`.

Say μ, never B, for the irrationality measure. -/

set_option autoImplicit false

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid CatalanCore.Lai
  CatalanCore.Lai.B83Bridge
open scoped Nat

namespace CatalanCore.Lai.B83Main

noncomputable section

/-! ### Part 1: nodes at the other residues -/

theorem ndB_eval (n k : ℕ) (F : ℚ[X]) :
    MvPolynomial.eval ![(0 : ℚ), 1, 0] (laiNd n k F) = ndB n k F := by
  unfold laiNd laiU laiV ndB
  simp only [map_mul, map_add, map_sub, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

theorem entB_eval (n : ℕ) (F : ℚ[X]) :
    MvPolynomial.eval ![(0 : ℚ), 1, 0] (laiL n F) = entB n F := by
  rw [laiL_channels]
  simp only [map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring

section Nodes

variable {n p A2 a : ℕ} [hp : Fact p.Prime]

theorem win_data (hb : BandPar n p A2 a) : p - 2 * n < p ∧ sig n p (p - 2 * n) = 5 := by
  have hr6 := band_r6 (p := p) hb.h1 hb.h2
  have hr2 := band_r2 (p := p) hb.h1 hb.h2
  have h1 := hb.h1
  have h2 := hb.h2
  refine ⟨by omega, ?_⟩
  unfold sig; rw [hr6, hr2]
  have : ¬ (p - 2 * n ≤ 6 * n - 2 * p) := by omega
  simp [this]

/-- **One node at a non-window residue with strict slack**: `v_p ≥ thr + 1` of the `b`-summand. -/
theorem cross_nodeB (hb : BandPar n p A2 a) (x y : FIdx n p 5) {s : ℕ} (hs : s < p) {l : ℕ}
    (hl : l ≤ Lc n p s) (hd : defF n p 5 x y s ≤ -1) :
    (p : ℚ) ^ (-((pot2F n p 5 x + pot2F n p 5 y + 1) / 2 + 1)) *
      ndB n (s + l * p) (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)) ∈ LocRing p := by
  classical
  have h := band_rng (p := p) hb.h1 hb.h2
  obtain ⟨hs0, hsW⟩ := win_data hb
  have hμ : ∀ r < p, sig n p r = 5 → mu n p r = 0 := fun r hr hrs => band_mu hb.h1 hb.h2 r hr hrs
  have hE := cross_node_ok h 5 (p - 2 * n) hs0 hsW 0 hμ x y s hs l hl hd
  have hF : elF n p 5 0 (orthA (cLoc (Lc n p (p - 2 * n))) 0) x *
      elF n p 5 0 (orthA (cLoc (Lc n p (p - 2 * n))) 0) y =
      (((ExZ n p 5 x) * (ExZ n p 5 y)).map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
    rw [elF_band 5 0 rfl hμ, elF_band 5 0 rfl hμ, ← Polynomial.map_mul, Polynomial.map_map]
    rfl
  rw [hF] at hE
  have hg : ∀ v : TVar, GV p 0 (specT (tauU n p (p - 2 * n)) (tauV n p (p - 2 * n)) v) := by
    rintro (i | ⟨l, _ | _⟩)
    · exact GV.var i
    · exact GV.const_loc (mn_tauU_mem n (p - 2 * n) l)
    · exact GV.const_loc (mn_tauV_mem n (p - 2 * n) h.h8 l)
  have h3 := GV.subst hE (specT (tauU n p (p - 2 * n)) (tauV n p (p - 2 * n))) hg
  rw [bind_nodeT] at h3
  have h4 := GV.evalPt h3 ![0, 1, 0] (fun i => by fin_cases i <;> simp [(LocRing p).one_mem])
  rwa [ndB_eval] at h4

/-- the deficit of an own pair at another residue is `≤ -1`. -/
theorem defF_own_le (hb : BandPar n p A2 a) {r i i' s : ℕ} (hrp : r < p) (hra : r < a)
    (hi : i < mF n p 5 r) (hi' : i' < mF n p 5 r) (hs : s < p) (hs5 : sig n p s ≠ 5) (hne : s ≠ r) :
    defF n p 5 (ownIx n p hrp hi) (ownIx n p hrp hi') s ≤ -1 := by
  have h1 := hb.h1
  have h2 := hb.h2
  have ha := hb.ha
  have hmr := band_sigmu h1 h2 r hrp
  have hms := band_sigmu h1 h2 s hs
  have hr5 : sig n p r ≠ 5 := by rcases hmr with ⟨a', -⟩ | ⟨a', -⟩ | ⟨a', -, c⟩ <;> omega
  have hFr := (band_mF h1 h2 r hrp).2 hr5
  have hFs := (band_mF h1 h2 s hs).2 hs5
  have hrs : ¬ r = s := fun h => hne h.symm
  simp only [defF, pot2F, nuF, ownIx, Fin.val_mk, hrs, ite_false]
  omega

theorem Lc_A (hb : BandPar n p A2 a) {r : ℕ} (hr : r ≤ A2) : Lc n p r = 2 := by
  have h6 := band_r6 (p := p) hb.h1 hb.h2
  have h7 := band_q6 (p := p) hb.h1 hb.h2
  have hA2 := hb.hA2
  have hle : r ≤ r6 n p := by omega
  simp [Lc, hle, h7]

theorem Lc_C (hb : BandPar n p A2 a) {r : ℕ} (hr : A2 < r) : Lc n p r = 1 := by
  have h6 := band_r6 (p := p) hb.h1 hb.h2
  have h7 := band_q6 (p := p) hb.h1 hb.h2
  have hA2 := hb.hA2
  have hle : ¬ r ≤ r6 n p := by omega
  simp [Lc, hle, h7]

/-- **Split of `entB` at an own residue**: window nodes, own nodes, all other residues. -/
theorem entB_split_own (hb : BandPar n p A2 a) {r : ℕ} (hra : r < a) (F : ℚ[X]) :
    entB n F = dWinB n p F + ∑ l ∈ range (Lc n p r + 1), ndB n (r + l * p) F +
      ∑ s ∈ ((range p).filter (fun s => ¬ sig n p s = 5)).erase r,
        ∑ l ∈ range (Lc n p s + 1), ndB n (s + l * p) F := by
  have h := band_rng (p := p) hb.h1 hb.h2
  rw [entB_split h F]
  have hap := hb.ap
  have hrp : r < p := by omega
  have hmem : r ∈ (range p).filter (fun s => ¬ sig n p s = 5) := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hrp, ?_⟩
    have := hb.ha
    rcases band_sigmu hb.h1 hb.h2 r hrp with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨hg, -, c⟩ <;> omega
  rw [← Finset.add_sum_erase _ _ hmem]
  ring

/-- the other residues of an own pair are above threshold. -/
theorem other_nodes (hb : BandPar n p A2 a) {r : ℕ} (hra : r < a) (hrp : r < p) {i i' : ℕ}
    (hi : i < mF n p 5 r) (hi' : i' < mF n p 5 r) (t : ℤ)
    (ht : (pot2F n p 5 (ownIx n p hrp hi) + pot2F n p 5 (ownIx n p hrp hi') + 1) / 2 = t)
    (F : ℚ[X])
    (hF : ((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')).map (Int.castRingHom ℚ) = F) :
    (p : ℚ) ^ (-(t + 1)) * ∑ s ∈ ((range p).filter (fun s => ¬ sig n p s = 5)).erase r,
        ∑ l ∈ range (Lc n p s + 1), ndB n (s + l * p) F ∈ LocRing p := by
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun s hs => ?_
  have hs' := Finset.mem_erase.1 hs
  have hs'' := Finset.mem_filter.1 hs'.2
  have hsp := Finset.mem_range.1 hs''.1
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun l hl => ?_
  have hd := defF_own_le hb hrp hra hi hi' hsp hs''.2 hs'.1
  have := cross_nodeB hb (ownIx n p hrp hi) (ownIx n p hrp hi') hsp (l := l)
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)) hd
  rw [ht, hF] at this
  exact this

/-- `ndB` in the form of `B83OwnNode` (the point `(0, 1, 0)`). -/
theorem ndB_own (n k : ℕ) (F : ℚ[X]) :
    ndB n k F = (laiCoef n k : ℚ) * (B83.ownU (0 : LocRing p) 1 k * F.derivative.eval (-(k : ℚ)) +
      B83.ownE n (0 : LocRing p) 1 0 k * F.eval (-(k : ℚ))) := by
  unfold ndB B83.ownU B83.ownE
  simp only [Subring.coe_zero, Subring.coe_one, zero_div]
  ring

theorem scale_aux (t : ℤ) (m : ℕ) (hm : (m : ℤ) = t + 4) (own Z : ℚ)
    (h : (p : ℚ) ^ 4 * own = (p : ℚ) ^ m * Z) : own = (p : ℚ) ^ t * Z := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : (p : ℚ) ^ m = (p : ℚ) ^ t * (p : ℚ) ^ 4 := by
    have : (p : ℚ) ^ (m : ℤ) = (p : ℚ) ^ (t + 4) := by rw [hm]
    rw [zpow_natCast, zpow_add₀ hp0] at this
    rw [this]; norm_cast
  rw [e] at h
  have h4 : (p : ℚ) ^ 4 ≠ 0 := pow_ne_zero _ hp0
  apply mul_left_cancel₀ h4
  linear_combination h

theorem unscale_aux (t : ℤ) (y : ℚ) : (p : ℚ) ^ (-t) * ((p : ℚ) ^ t * y) = y := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← mul_assoc, ← zpow_add₀ hp0, neg_add_cancel, zpow_zero, one_mul]

theorem shift_aux (t : ℤ) (O : ℚ) :
    (p : ℚ) ^ (-t) * O = (p : ℚ) * ((p : ℚ) ^ (-(t + 1)) * O) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← mul_assoc, ← zpow_one_add₀ hp0]
  congr 2
  ring

theorem redQ_p : redQ p ((p : ℕ) : LocRing p) = 0 := (redQ_eq_zero_iff p _).2 dvd_rfl

/-- **Plain-basis diagonal blocks of the `A` residues (Lemma A).** -/
theorem diagA_of (hb : BandPar n p A2 a) : DiagA n p A2 a := by
  intro r hr i i' hi hi'
  have ha := hb.ap
  have hA := hb.hAp
  have hA2 := hb.lt
  have h3n := hb.h2
  have hp11 := hb.p11
  have h5 : 5 ≤ p := by omega
  have hra : r < a := by omega
  have hrp : r < p := by omega
  have hmF : mF n p 5 r = 4 := mF_A hb hr
  have hi_ : i < mF n p 5 r := by omega
  have hi'_ : i' < mF n p 5 r := by omega
  have hF : ((ExZ n p 5 (ownIx n p hrp hi_)) * ExZ n p 5 (ownIx n p hrp hi'_)).map (Int.castRingHom ℚ) =
      B83.eB A2 a r i * B83.eB A2 a r i' := ExZ_pair_eq h5 ha hA hA2 h3n hra hrp hi_ hi'_
  have hthr : (pot2F n p 5 (ownIx n p hrp hi_) + pot2F n p 5 (ownIx n p hrp hi'_) + 1) / 2 =
      (i : ℤ) + i' - 4 := by
    rw [pot2F_own, pot2F_own, sig_A hb hr]; push_cast; omega
  obtain ⟨yD, hD1, hD2⟩ := dnode_A h5 ha hA hA2 h3n hr hrp hi_ hi'_
  rw [hF, hthr] at hD1
  obtain ⟨Z, hZ1, hZ2⟩ := B83.own_entry_A h5 ha hA hA2 hr i i' (0 : LocRing p) 1 0
  have hoth := other_nodes hb hra hrp hi_ hi'_ ((i : ℤ) + i' - 4) hthr _ hF
  have hsplit := entB_split_own hb hra (B83.eB A2 a r i * B83.eB A2 a r i')
  rw [Lc_A hb hr] at hsplit
  have hown : ∑ l ∈ range (2 + 1), ndB n (r + l * p) (B83.eB A2 a r i * B83.eB A2 a r i') =
      ∑ j ∈ range 3, (laiCoef n (r + j * p) : ℚ) *
          (B83.ownU (0 : LocRing p) 1 (r + j * p) *
              (derivative (B83.eB A2 a r i * B83.eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            B83.ownE n (0 : LocRing p) 1 0 (r + j * p) *
              (B83.eB A2 a r i * B83.eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) :=
    Finset.sum_congr rfl fun l _ => ndB_own _ _ _
  have hZ1' : (p : ℚ) ^ 4 * ∑ l ∈ range (2 + 1), ndB n (r + l * p) (B83.eB A2 a r i * B83.eB A2 a r i') =
      (p : ℚ) ^ (i + i') * (Z : ℚ) := by rw [hown]; exact hZ1
  have hown2 := scale_aux ((i : ℤ) + i' - 4) (i + i') (by push_cast; ring) _ _ hZ1'
  refine ⟨yD + Z + ((p : ℕ) : LocRing p) * ⟨_, hoth⟩, ?_, ?_⟩
  · simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
    rw [hsplit, hD1, hown2, mul_add, mul_add, unscale_aux, unscale_aux]
    rw [shift_aux ((i : ℤ) + i' - 4)]
  · rw [map_add, map_add, map_mul, redQ_p, zero_mul, add_zero, hD2, hZ2, map_one]
    unfold B83.hA
    ring

/-- **Plain-basis diagonal blocks of the `C` residues (Lemma C).** -/
theorem diagC_of (hb : BandPar n p A2 a) : DiagC n p A2 a := by
  intro r hr1 hr2 i i' hi hi'
  have ha := hb.ap
  have hA := hb.hAp
  have hA2 := hb.lt
  have h3n := hb.h2
  have hp11 := hb.p11
  have h5 : 5 ≤ p := by omega
  have hrp : r < p := by omega
  have hmF : mF n p 5 r = 3 := mF_C hb hr1 hr2
  have hi_ : i < mF n p 5 r := by omega
  have hi'_ : i' < mF n p 5 r := by omega
  have hF : ((ExZ n p 5 (ownIx n p hrp hi_)) * ExZ n p 5 (ownIx n p hrp hi'_)).map (Int.castRingHom ℚ) =
      B83.eB A2 a r i * B83.eB A2 a r i' := ExZ_pair_eq h5 ha hA hA2 h3n hr2 hrp hi_ hi'_
  have hthr : (pot2F n p 5 (ownIx n p hrp hi_) + pot2F n p 5 (ownIx n p hrp hi'_) + 1) / 2 =
      (i : ℤ) + i' - 2 := by
    rw [pot2F_own, pot2F_own, sig_C hb hr1 hr2]; push_cast; omega
  obtain ⟨yD, hD1, hD2⟩ := dnode_C h5 ha hA hA2 h3n hr1 hr2 hrp hi_ hi'_
  rw [hF, hthr] at hD1
  obtain ⟨Z, hZ1, hZ2⟩ := B83.own_entry_C h5 ha hA hA2 hr1 hr2 i i' (0 : LocRing p) 1 0
  have hoth := other_nodes hb hr2 hrp hi_ hi'_ ((i : ℤ) + i' - 2) hthr _ hF
  have hsplit := entB_split_own hb hr2 (B83.eB A2 a r i * B83.eB A2 a r i')
  rw [Lc_C hb hr1] at hsplit
  have hown : ∑ l ∈ range (1 + 1), ndB n (r + l * p) (B83.eB A2 a r i * B83.eB A2 a r i') =
      ∑ j ∈ range 2, (laiCoef n (r + j * p) : ℚ) *
          (B83.ownU (0 : LocRing p) 1 (r + j * p) *
              (derivative (B83.eB A2 a r i * B83.eB A2 a r i')).eval (-(Nat.cast (r + j * p) : ℚ)) +
            B83.ownE n (0 : LocRing p) 1 0 (r + j * p) *
              (B83.eB A2 a r i * B83.eB A2 a r i').eval (-(Nat.cast (r + j * p) : ℚ))) :=
    Finset.sum_congr rfl fun l _ => ndB_own _ _ _
  have hZ1' : (p : ℚ) ^ 4 * ∑ l ∈ range (1 + 1), ndB n (r + l * p) (B83.eB A2 a r i * B83.eB A2 a r i') =
      (p : ℚ) ^ (2 + (i + i')) * (Z : ℚ) := by rw [hown]; exact hZ1
  have hown2 := scale_aux ((i : ℤ) + i' - 2) (2 + (i + i')) (by push_cast; ring) _ _ hZ1'
  refine ⟨yD + Z + ((p : ℕ) : LocRing p) * ⟨_, hoth⟩, ?_, ?_⟩
  · simp only [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast]
    rw [hsplit, hD1, hown2, mul_add, mul_add, unscale_aux, unscale_aux]
    rw [shift_aux ((i : ℤ) + i' - 2)]
  · rw [map_add, map_add, map_mul, redQ_p, zero_mul, add_zero, hD2, hZ2, map_one]
    unfold B83.hC
    ring

end Nodes

/-! ### Part 2: the half block -/

section Half

variable {n p A2 a : ℕ} [hp : Fact p.Prime]

theorem redQ_ne_of_unit {x : LocRing p} (h : Wilson.PUnit' p (x : ℚ)) : redQ p x ≠ 0 := by
  intro h0
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p x).1 h0
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hxe : (x : ℚ) = (p : ℚ) * (y : ℚ) := by rw [hy]; simp
  have hy0 : (y : ℚ) ≠ 0 := fun hh => h.1 (by rw [hxe, hh, mul_zero])
  have hv := h.2
  rw [hxe, padicValRat.mul hp0 hy0, padicValRat.self hp.out.one_lt] at hv
  have := B83HalfBridge.padicValRat_nonneg_of_mem y.2
  omega

theorem gRed_mem_gen {A : ℕ} (hB : B83Half.Band p n a A) {K : ℕ} (hK : K = 3 * n - 1 - p) (i j : Fin K) :
    B83HalfBridge.gRed p n a A K i j ∈ LocRing p := by
  subst hK
  have h := B83HalfBridge.gRed_entry hB i j
  have h1 : B83HalfBridge.gRed p n a A (3 * n - 1 - p) i j =
      (B83HalfBridge.gRed p n a A (3 * n - 1 - p) i j - B83HalfBridge.gTarget p n a A (3 * n - 1 - p) i j) +
        B83HalfBridge.gTarget p n a A (3 * n - 1 - p) i j := by ring
  rw [h1]
  exact (LocRing p).add_mem h.zero_pow_mem (B83HalfBridge.gTarget_mem hB i j)

theorem gRed_unit_gen {A : ℕ} (hB : B83Half.Band p n a A) {K : ℕ} (hK : K = 3 * n - 1 - p) :
    Wilson.PUnit' p (B83HalfBridge.gRed p n a A K).det := by
  subst hK
  exact B83HalfBridge.half_block_unit hB

/-- **The reduced half block is nonsingular** (`hBB` of `det_gram_ne_zero`), from `half_block_unit`. -/
theorem hBB_band (hb : BandPar n p A2 a) :
    (Matrix.of fun j j' : Fin (xtwo n p).toNat => redQ p (ZB hb (Sum.inr j) (Sum.inr j'))).det ≠ 0 := by
  have hK := xtwo_toNat hb
  have hap := hb.ap
  have hAp := hb.hAp
  have hlt := hb.lt
  have h2 := hb.h2
  have hp11 := hb.p11
  have hBand : B83Half.Band p n a A2 := ⟨by omega, by omega, by omega, hlt, h2⟩
  let z : Fin (xtwo n p).toNat → Fin (xtwo n p).toNat → LocRing p := fun i j =>
    ⟨B83HalfBridge.gRed p n a A2 (xtwo n p).toNat i j, gRed_mem_gen hBand hK i j⟩
  have hz : ∀ j j' : Fin (xtwo n p).toNat, (z j j' : ℚ) =
      (p : ℚ) ^ (-(3 : ℤ)) * entB n (B83Half.PiA a A2 ^ 2 * X ^ ((j : ℕ) + j')) := by
    intro j j'
    show B83HalfBridge.gRed p n a A2 (xtwo n p).toNat j j' = _
    unfold B83HalfBridge.gRed
    simp only [Matrix.of_apply]
    rw [B83HalfBridge.gGram_eq, ← B83HalfBridge.laiL_eval_b, entB_eval, zpow_neg]
    norm_cast
  refine hBB_of hb z hz ?_
  have e : (Matrix.of fun j j' => redQ p (z j j')) = (redQ p).mapMatrix (Matrix.of z) := rfl
  rw [e, ← RingHom.map_det]
  apply redQ_ne_of_unit
  have e2 : (((Matrix.of z).det : LocRing p) : ℚ) =
      (B83HalfBridge.gRed p n a A2 (xtwo n p).toNat).det := by
    have := RingHom.map_det (LocRing p).subtype (Matrix.of z)
    rw [show (LocRing p).subtype.mapMatrix (Matrix.of z) = B83HalfBridge.gRed p n a A2 (xtwo n p).toNat from by
      ext i j; rfl] at this
    exact this
  rw [e2]
  exact gRed_unit_gen hBand hK

end Half

/-! ### Part 3: degrees and the number of basis elements -/

section Deg

variable {n p A2 a : ℕ} [hp : Fact p.Prime]

omit hp in
theorem sum_muB (hb : BandPar n p A2 a) : ∑ t ∈ range a, B83.muB A2 t = 3 * a + (A2 + 1) := by
  have hlt := hb.lt
  rw [← Finset.sum_range_add_sum_Ico _ (show A2 + 1 ≤ a by omega)]
  have e1 : ∑ t ∈ range (A2 + 1), B83.muB A2 t = 4 * (A2 + 1) := by
    rw [Finset.sum_congr rfl (fun t ht => B83.muB_le (by have := Finset.mem_range.1 ht; omega) :
      ∀ t ∈ range (A2 + 1), B83.muB A2 t = 4)]
    simp [mul_comm]
  have e2 : ∑ t ∈ Ico (A2 + 1) a, B83.muB A2 t = 3 * (a - (A2 + 1)) := by
    rw [Finset.sum_congr rfl (fun t ht => B83.muB_gt (by have := (Finset.mem_Ico.1 ht).1; omega) :
      ∀ t ∈ Ico (A2 + 1) a, B83.muB A2 t = 3)]
    simp [mul_comm]
  rw [e1, e2]
  omega

omit hp in
theorem natDegree_eB_le (hb : BandPar n p A2 a) {r i : ℕ} (hr : r < a) (hi : i < B83.muB A2 r) :
    (B83.eB A2 a r i).natDegree ≤ p := by
  unfold B83.eB B83.PsiPoly
  refine natDegree_mul_le.trans ?_
  have h1 : ((X + C (r : ℚ)) ^ i).natDegree ≤ i := by
    refine natDegree_pow_le.trans ?_
    rw [natDegree_X_add_C]; simp
  have h2 : (∏ t ∈ (range a).erase r, (X + C (t : ℚ)) ^ B83.muB A2 t).natDegree ≤
      ∑ t ∈ (range a).erase r, B83.muB A2 t := by
    refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    refine natDegree_pow_le.trans ?_
    rw [natDegree_X_add_C]; simp
  have h3 : ∑ t ∈ (range a).erase r, B83.muB A2 t + B83.muB A2 r = 3 * a + (A2 + 1) := by
    rw [Finset.sum_erase_add _ _ (Finset.mem_range.2 hr)]; exact sum_muB hb
  have hap := hb.ap
  have hAp := hb.hAp
  omega

omit hp in
theorem natDegree_g_le (hb : BandPar n p A2 a) (j : ℕ) :
    (X ^ j * B83Half.PiA a A2 : ℚ[X]).natDegree ≤ j + (p + 1) := by
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have h2 : (B83Half.PiA a A2).natDegree ≤ ∑ t ∈ range a, B83.muB A2 t := by
    unfold B83Half.PiA
    refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
    refine natDegree_pow_le.trans ?_
    rw [natDegree_X_add_C]
    simp [B83.muB]
  have h3 := sum_muB hb
  have hap := hb.ap
  have hAp := hb.hAp
  omega

theorem natDegree_ExZ_lt (hb : BandPar n p A2 a) (x : FIdx n p 5) :
    ((ExZ n p 5 x).map (Int.castRingHom ℚ)).natDegree < 3 * n := by
  have h2 := hb.h2
  rcases x with ⟨r0, i⟩ | j
  · have hr0 : (r0 : ℕ) < a := by
      by_contra hge
      have := mF_D hb r0.2 (by omega)
      have := i.2
      omega
    rw [ExZ_inl_map hb r0 i hr0]
    have := natDegree_eB_le hb hr0 (i := i) (lt_of_lt_of_eq i.2 (mF_lt hb hr0))
    omega
  · rw [ExZ_inr_map hb j]
    have := natDegree_g_le hb j
    have hj := j.2
    have hK := xtwo_toNat hb
    omega

theorem card_FIdx (hb : BandPar n p A2 a) : Fintype.card (FIdx n p 5) = 3 * n := by
  rw [← Fintype.card_congr (fEquiv hb)]
  simp only [IX, IA, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have hK := xtwo_toNat hb
  have hap := hb.ap
  have hAp := hb.hAp
  have hlt := hb.lt
  have h2 := hb.h2
  rw [hK]
  omega

end Deg

/-! ### Part 4: Theorem B83 -/

section Main

variable {p : ℕ} [hp : Fact p.Prime]

/-- **Theorem B83 (core).**  `n`, `p` prime in the band `8n < 3p`, `p + 1 < 3n`, `p ∉ {13, 24359}`
(`p ∉ {2, 3, 5}` is automatic: the band forces `p ≥ 17`), `a, b, X' ∈ ℤ_(p)`, `b` a unit:
`J_n(a, b, X'/p³) ≠ 0`. -/
theorem b83_core (n : ℕ) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (h13 : p ≠ 13) (h24359 : p ≠ 24359)
    (a b X' : LocRing p) (hb : redQ p b ≠ 0) :
    MvPolynomial.eval ![(a : ℚ), (b : ℚ), (X' : ℚ) / (p : ℚ) ^ 3] (laiJ n) ≠ 0 := by
  classical
  have hbp := BandPar.of_range (n := n) (p := p) h1 h2
  have hdet := det_gramF_ne_zero hbp (diagA_of hbp) (diagC_of hbp) a b X' hb h13 h24359 (hBB_band hbp)
  let e : FIdx n p 5 ≃ Fin (3 * n) := Fintype.equivOfCardEq (by rw [card_FIdx hbp, Fintype.card_fin])
  rw [CatalanCore.Lai.NV.eval_laiJ]
  refine mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero 2 (by positivity))) ?_
  refine CatalanCore.Lai.NV.hankel_det_ne_zero_of_gram _ e
    (fun x => (ExZ n p 5 x).map (Int.castRingHom ℚ)) (fun x => ?_) ?_
  · exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast natDegree_ExZ_lt hbp x)
  · have hdet' := hdet
    simp only [CatalanCore.Lai.NV.eval_laiL] at hdet'
    simpa only [← Polynomial.map_mul] using hdet'

/-- **Theorem B83**, in the paper's form: `n ≥ 1`, `p` a prime with `8n/3 < p < 3n - 1` and
`p ∉ {2, 3, 5, 13, 24359}`, `a, b ∈ ℤ_(p)` with `b` a unit and `X ∈ ℚ` with `p³ X ∈ ℤ_(p)`
(that is `v_p(X) ≥ -3`): `J_n(a, b, X) ≠ 0`. -/
theorem b83_nonvanishing (n : ℕ) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n)
    (hp5 : p ∉ ({2, 3, 5, 13, 24359} : Finset ℕ)) (a b : LocRing p) (hb : redQ p b ≠ 0)
    (X : ℚ) (hX : (p : ℚ) ^ 3 * X ∈ LocRing p) :
    MvPolynomial.eval ![(a : ℚ), (b : ℚ), X] (laiJ n) ≠ 0 := by
  have h13 : p ≠ 13 := fun h => hp5 (by simp [h])
  have h24359 : p ≠ 24359 := fun h => hp5 (by simp [h])
  have hl := CatalanCore.Lai.NV.l_ne_zero p
  have key := b83_core n h1 h2 h13 h24359 a b ⟨_, hX⟩ hb
  have hv : (![(a : ℚ), (b : ℚ), ((⟨_, hX⟩ : LocRing p) : ℚ) / (p : ℚ) ^ 3] : Fin 3 → ℚ) =
      ![(a : ℚ), (b : ℚ), X] := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp; field_simp
  rw [hv] at key
  exact key

theorem nv_pt_B83 (n : ℕ) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (h13 : p ≠ 13) (h24359 : p ≠ 24359)
    (a b : ℤ) (hb : ¬ (p : ℤ) ∣ b) (pp : ℤ) (q : ℕ) (hq : 0 < q) (hq4 : ¬ p ^ 4 ∣ q) :
    MvPolynomial.eval ![(a : ℚ), (b : ℚ), (pp : ℚ) / (q : ℚ)] (laiJ n) ≠ 0 := by
  have hmem : ((p : ℚ) ^ 3 * (pp : ℤ) / (q : ℚ)) ∈ LocRing p :=
    CatalanCore.Lai.NV.mem_locRing_scaled pp hq hq4
  have hb' : redQ p (b : LocRing p) ≠ 0 := by
    rw [map_intCast]
    intro h0
    exact hb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0)
  have key := b83_core n h1 h2 h13 h24359 ((a : ℤ) : LocRing p) (b : LocRing p) ⟨_, hmem⟩ hb'
  have hl := CatalanCore.Lai.NV.l_ne_zero p
  have hv : (![(((a : ℤ) : LocRing p) : ℚ), ((b : LocRing p) : ℚ),
      ((⟨_, hmem⟩ : LocRing p) : ℚ) / (p : ℚ) ^ 3] : Fin 3 → ℚ) =
      ![(a : ℚ), (b : ℚ), (pp : ℚ) / (q : ℚ)] := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp; field_simp
  rw [hv] at key
  exact key

/-- **Corollary `nv_plane_B83`** (plane, `e = 4`): `a, b ∈ ℤ`, `p ∤ b`, `p⁴ ∤ q`:
`J_n(a, b, pp/q) ≠ 0`, that is `Q_n(pp/q) ≠ 0` for the plane family. -/
theorem nv_plane_B83 (n : ℕ) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (h13 : p ≠ 13)
    (h24359 : p ≠ 24359) (a b pp : ℤ) (q : ℕ) (hb : ¬ (p : ℤ) ∣ b) (hq : 0 < q) (hq4 : ¬ p ^ 4 ∣ q) :
    (laiPlaneFam a b).evalQ n ((pp : ℚ) / (q : ℚ)) ≠ 0 := by
  rw [plane_evalQ]
  exact nv_pt_B83 n h1 h2 h13 h24359 a b hb pp q hq hq4

/-- **Corollary `nv_ratio_B83`** (ratio, `e = 1`): `p ∤ pp`: `J_n(qq, -pp, 0) ≠ 0`, that is
`Q_n(pp/qq) ≠ 0` for the ratio family. -/
theorem nv_ratio_B83 (n : ℕ) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (h13 : p ≠ 13)
    (h24359 : p ≠ 24359) (pp qq : ℤ) (hq : qq ≠ 0) (hpp : ¬ (p : ℤ) ∣ pp) :
    laiRatioFam.evalQ n ((pp : ℚ) / (qq : ℚ)) ≠ 0 := by
  have hq' : (qq : ℚ) ≠ 0 := by exact_mod_cast hq
  intro h0
  have hs := ratio_scaled n pp qq hq'
  have hb' : redQ p (((-pp : ℤ)) : LocRing p) ≠ 0 := by
    rw [map_intCast]
    intro h0
    apply hpp
    have : ((-pp : ℤ) : ZMod p) = 0 := h0
    rw [Int.cast_neg, neg_eq_zero] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have key := b83_core n h1 h2 h13 h24359 ((qq : ℤ) : LocRing p) ((-pp : ℤ) : LocRing p) 0 hb'
  have hv : (![(((qq : ℤ) : LocRing p) : ℚ), (((-pp : ℤ) : LocRing p) : ℚ),
      ((0 : LocRing p) : ℚ) / (p : ℚ) ^ 3] : Fin 3 → ℚ) = ![(qq : ℚ), -(pp : ℚ), 0] := by
    funext i
    fin_cases i
    · simp
    · simp
    · simp
  rw [hv] at key
  exact key (hs.symm.trans (mul_eq_zero_of_right _ h0))

end Main

end

end CatalanCore.Lai.B83Main

#print axioms CatalanCore.Lai.B83Main.diagA_of
#print axioms CatalanCore.Lai.B83Main.diagC_of
#print axioms CatalanCore.Lai.B83Main.hBB_band
#print axioms CatalanCore.Lai.B83Main.card_FIdx
#print axioms CatalanCore.Lai.B83Main.natDegree_ExZ_lt
#print axioms CatalanCore.Lai.B83Main.b83_core
#print axioms CatalanCore.Lai.B83Main.b83_nonvanishing
#print axioms CatalanCore.Lai.B83Main.nv_plane_B83
#print axioms CatalanCore.Lai.B83Main.nv_ratio_B83
