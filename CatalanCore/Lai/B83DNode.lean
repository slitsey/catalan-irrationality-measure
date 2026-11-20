module

public import CatalanCore.Lai.B83Weighted
public import CatalanCore.Lai.B83Blocks

@[expose] public section

/-! # `CatalanCore.Lai.B83DNode`: the D-node exact values of the integral block (Theorem B83, ledger LB04b/LB05b, D part)

Note `N9-LAI-SMALLPRIME-NV-2026-11-20.md` §3.4, Lemmas A and C, "D-nodes".  Band `8n/3 < p < 3n - 1`, `a = p - 2n`
odd, `A₂ = 6n - 2p < a`, classes `A = [0, A₂]` (E2 multiplicity `μ' = 4`), `C = (A₂, a)` (`μ' = 3`), window
`D = [a, p)` (`σ = 5`, `μ = 0`, nodes `k = s, s + p`).

For the pair `e_{r,i} e_{r,i'}` of the E2 basis at one own residue `r ∈ A ∪ C`, `m = i + i'`, `F = e_{r,i} e_{r,i'}`,
the `b`-channel of `L_n(F)` over the nodes of the window,

  `dWinB n p F = ∑_{s ∈ D} ∑_{l ≤ Lc} ndB n (s + l p) F`   (`ndB` is the summand of `entB`),

is `p^{thr} y` with `y ∈ ℤ_(p)` and

* `dnode_A` (`r ≤ A₂`, `thr = m - 4`): `ȳ = corrA(m) · wtB`, `corrA 5 = -7·32`, `corrA 6 = 12·32`, `0` otherwise;
* `dnode_C` (`A₂ < r < a`, `thr = m - 2`): `ȳ = corrC(m) · wtB`, `corrC 3 = -7·8`, `corrC 4 = -16·8`, `0` otherwise.

These are exactly the D-node corrections `corrA`, `corrC` of `B83Blocks.hA`, `hC` which cancel `Φ_A(5) = 224`,
`Φ_A(6) = -384` (resp. `Φ_C(3) = 56`, `Φ_C(4) = 128`) of the own nodes, closing `h₅ = h₆ = 0`, `h₃ = -52`, `h₄ = -130`
of `det_intBlock_band_ne`.

Method: Lemma P (`res_second`) at the window gives the jet main term `Mmain` (`dwin_main`, `GV 3`), whose sums
`Σ c̄_s F(-s)` (second order), `Σ c̄_s F'(-s)`, `Σ c̄_s λ₀(s) F(-s)` are evaluated by the polynomial data `G, H` of the pair
(`gOwn`, `hOwn`, with `G(r) ≠ 0` for `m = 5, 3` and a simple zero at `r` for `m = 6, 4`), the Faulhaber bridge and the
harmonic shift lemma with a boundary derivative term (`harmSum_window_neg_d`); the unit `K` of Lemma R is pinned at the last
residue `s = p - 1` (`Kz_rho`: `K = A₂!² / (2n)!³`), so that `κ K = K₀` and `K₀ P_r(r)³ = 32 resp. 8 · wtB` (Lemma U83).
-/

open Finset Polynomial CatalanCore.Basic CatalanCore.Content CatalanCore.Arith.Hybrid
open scoped Nat

namespace CatalanCore.Lai

noncomputable section

/-! ### Part 1: the D-window node sum of the `b`-channel and its jet main term -/

section DJet

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The `b`-channel summand of the node `k` of `L_n(F)`: the summand of `entB`. -/
def ndB (n k : ℕ) (F : ℚ[X]) : ℚ :=
  (laiCoef n k : ℚ) *
    (-2 * Hq 3 k * F.derivative.eval (-(k : ℚ)) + (2 * laiH n k * Hq 3 k - 6 * Hq 4 k) * F.eval (-(k : ℚ)))

/-- The window `D = {s < p : σ(s) = 5}`. -/
def Dw (n p : ℕ) : Finset ℕ := (range p).filter (fun s => sig n p s = 5)

lemma mem_Dw {s : ℕ} : s ∈ Dw n p ↔ s < p ∧ sig n p s = 5 := by
  unfold Dw; simp [Finset.mem_filter, Finset.mem_range]

/-- The `b`-channel node sum over the window `D` (nodes `s + l p`, `l ≤ Lc`). -/
def dWinB (n p : ℕ) (F : ℚ[X]) : ℚ :=
  ∑ s ∈ Dw n p, ∑ l ∈ range (Lc n p s + 1), ndB n (s + l * p) F

lemma orthA_zero {R : Type*} [CommRing R] (c : ℕ → R) : orthA c 0 = 1 := by
  simp [orthA, orthDet]

/-- **Lemma P at the window `D` (`μ = 0`)**: node sums against the jet main term, for any `V ∈ ℤ[X]`. -/
theorem dwin_jetMPT (h : Rng n p) (s0 : ℕ) (hs0 : s0 < p) (hsW : sig n p s0 = 5)
    (V : ℤ[X]) :
    GV p 3
      (∑ s ∈ Dw n p, ∑ l ∈ range (Lc n p s0 + 1),
          nodeT (p := p) n (Kset n p 5) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) (s + l * p)
            (V.map zphi) -
        ∑ s ∈ Dw n p, resJet n p s (Lc n p s0) 0 (tauU n p s0)
          (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) (orthA (cLoc (Lc n p s0)) 0) (V.map zphi)) := by
  have hpp := h.p5
  have hp3 : 3 ≤ p := by omega
  have h8 := h.h8
  rw [← Finset.sum_sub_distrib]
  refine GV.sum fun s hs => ?_
  obtain ⟨hsp, hsg⟩ := mem_Dw.1 hs
  have hLs : Lc n p s = Lc n p s0 := by
    rw [mn_Lc_eq, mn_Lc_eq, (mn_flags_of_sig (n := n) (p := p) (s := s) (s' := s0)
      (by rw [hsg, hsW])).1]
  obtain ⟨b1, b2⟩ := mn_Lc_bound h s hsp
  rw [hLs] at b1 b2
  obtain ⟨hK0, hK⟩ := mn_hKn h 5 s0 hs0 hsW s hsp hsg
  have hAP : PInt p (orthA (cLoc (Lc n p s0)) 0) := orthA_pint _ _ (fun i => GV_cLoc _ i)
  have hAd : (orthA (cLoc (Lc n p s0)) 0).natDegree ≤ 0 := orthA_natDegree_le _ _
  have := res_second n (Kset n p 5) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) h8 hp3 s hsp
    (Lc n p s0) b1 b2 hK hK0 0 _ hAP hAd (V.map zphi) (PInt_map_zphi V)
  simp only [shiftP_zero_orth, one_pow, one_mul] at this
  have e : (sig n p s : ℤ) + 2 * ((0 : ℕ) : ℤ) - 2 = 3 := by rw [hsg]; norm_num
  rw [e] at this
  exact this

end DJet

section DEval

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The evaluation point `(a, b, X) = (0, 1, 0)`, `T = τ`. -/
def vτ (n p s0 : ℕ) : TVar → ℚ
  | Sum.inl i => ![(0 : ℚ), 1, 0] i
  | Sum.inr (l, false) => tauU n p s0 l
  | Sum.inr (l, true) => tauV n p s0 l

/-- evaluation of `MPT` at `vτ`. -/
def evτ (n p s0 : ℕ) : MPT →+* ℚ := MvPolynomial.eval (vτ n p s0)

lemma evτ_C (n p s0 : ℕ) (x : ℚ) : evτ n p s0 (MvPolynomial.C x) = x := by
  simp [evτ]

lemma evτ_bT (n p s0 : ℕ) : evτ n p s0 bT = 1 := by
  simp [evτ, bT, vτ]

lemma evτ_aT (n p s0 : ℕ) : evτ n p s0 aT = 0 := by
  simp [evτ, aT, vτ]

lemma evτ_Tu (n p s0 l : ℕ) : evτ n p s0 (Tu l) = tauU n p s0 l := by
  simp [evτ, Tu, vτ]

lemma evτ_Tv (n p s0 l : ℕ) : evτ n p s0 (Tv l) = tauV n p s0 l := by
  simp [evτ, Tv, vτ]

lemma evτ_ren (n p s0 : ℕ) (f : MP) :
    evτ n p s0 (ren f) = MvPolynomial.eval ![(0 : ℚ), 1, 0] f := by
  have h := MvPolynomial.aeval_bind₁ (R := ℚ) (S := ℚ) (vτ n p s0)
    (fun i : Fin 3 => (MvPolynomial.X (Sum.inl i) : MPT)) f
  have e : (fun i : Fin 3 => (MvPolynomial.aeval (vτ n p s0)) (MvPolynomial.X (Sum.inl i) : MPT)) =
      ![(0 : ℚ), 1, 0] := by
    funext i; simp [vτ]
  rw [e] at h
  simpa [ren, evτ, MvPolynomial.coe_aeval_eq_eval] using h

lemma eval_laiNd (n k : ℕ) (F0 : ℚ[X]) :
    MvPolynomial.eval ![(0 : ℚ), 1, 0] (laiNd n k F0) = ndB n k F0 := by
  unfold laiNd laiU laiV ndB
  simp only [map_mul, map_add, map_sub, map_neg, MvPolynomial.eval_C, MvPolynomial.eval_X, map_ofNat]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

lemma evτ_nodeT (n p s0 k : ℕ) (F0 : ℚ[X]) :
    evτ n p s0 (nodeT (p := p) n (Kset n p 5) (sigN n p) (clN n p) (tauU n p s0) (tauV n p s0) k
      (F0.map (MvPolynomial.C : ℚ →+* MPT))) = ndB n k F0 := by
  unfold nodeT
  rw [map_add, ndT_map, evτ_ren, eval_laiNd]
  split_ifs
  · rw [modNdT_map]
    unfold modNd
    simp only [map_mul, map_add, map_sub, evτ_C, evτ_bT, evτ_Tu, evτ_Tv, sub_self, mul_zero]
    simp
  · simp

lemma linM_one {R : Type*} [CommRing R] (m : ℕ → R) : linM m (1 : R[X]) = m 0 := by
  have := linM_monomial m 0 (1 : R)
  simpa using this

lemma linM_X {R : Type*} [CommRing R] (m : ℕ → R) : linM m (Polynomial.X : R[X]) = m 1 := by
  have := linM_monomial m 1 (1 : R)
  simpa using this

lemma evτ_polyEval (n p s0 : ℕ) (R : MPT[X]) (x : MPT) :
    evτ n p s0 (R.eval x) = (R.map (evτ n p s0)).eval (evτ n p s0 x) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma cLoc_one_zero : cLoc 1 0 = Tv 1 := by simp [cLoc]

lemma cLoc_one_one : cLoc 1 1 = Tu 1 - Tv 1 := by simp [cLoc]; ring

lemma evτ_resJet_L1 (n p s0 s : ℕ) (hsg : sig n p s = 5) (kap : ℕ → ℚ) (R : MPT[X]) :
    evτ n p s0 (resJet n p s 1 0 (tauU n p s0) kap (orthA (cLoc 1) 0) R) =
      (p : ℚ) * (cbarZ n p s : ℚ) *
        (evτ n p s0 (R.eval (MvPolynomial.C (-(s : ℚ)))) * tauV n p s0 1 +
          (p : ℚ) * (evτ n p s0 ((Polynomial.derivative R).eval (MvPolynomial.C (-(s : ℚ)))) -
              lam0 n p s * evτ n p s0 (R.eval (MvPolynomial.C (-(s : ℚ))))) *
            (tauU n p s0 1 - tauV n p s0 1)) := by
  have e : ((sig n p s : ℤ) - 4) = 1 := by rw [hsg]; norm_num
  rw [orthA_zero]
  unfold resJet locUtau locAk
  simp only [one_pow, mul_one, map_add, map_mul, map_sub, evτ_C, evτ_bT, evτ_aT, linM_one, linM_X,
    cLoc_one_zero, cLoc_one_one, evτ_Tu, evτ_Tv, Nat.cast_zero, mul_zero, add_zero, zero_add, e, zpow_one,
    Finset.sum_range_one, Polynomial.eval_one, sub_self, zero_mul, one_mul]

end DEval

section DMain

variable {n p : ℕ} [hp : Fact p.Prime]

/-- The jet main term of the `b`-channel of the window `D`: `p κ Σ_s c̄_s [-7 F(-s) + 5p (F'(-s) - λ₀ F(-s))]`. -/
def Mmain (n p : ℕ) (F : ℚ[X]) : ℚ :=
  ∑ s ∈ Dw n p, (p : ℚ) * (cbarZ n p s : ℚ) * (kapZ n p 1 1 1 : ℚ) *
    (-7 * F.eval (-(s : ℚ)) + 5 * (p : ℚ) * (F.derivative.eval (-(s : ℚ)) - lam0 n p s * F.eval (-(s : ℚ))))

section Band

variable {a A2 : ℕ}

lemma sig_D {s : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (has : a ≤ s) (hsp : s < p) :
    sig n p s = 5 := by
  rw [sig_eq_flags, NV7.bflag_eq n a A2 s hA (by omega), NV7.eflag_eq n a s ha (by omega)]
  rw [if_pos (by omega), if_pos has]

lemma D_iff {s : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)   :
    s ∈ Dw n p ↔ a ≤ s ∧ s < p := by
  rw [mem_Dw]
  constructor
  · rintro ⟨hs, hsg⟩
    refine ⟨?_, hs⟩
    by_contra hc
    push Not at hc
    rw [sig_eq_flags, NV7.bflag_eq n a A2 s hA (by omega), NV7.eflag_eq n a s ha (by omega)] at hsg
    split_ifs at hsg <;> omega
  · rintro ⟨h1', h2'⟩
    exact ⟨h2', sig_D h5 ha hA hA2 h1' h2'⟩

lemma flags_D {s : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (has : a ≤ s) (hsp : s < p) :
    bflag n p s = 1 ∧ eflag n p s = 1 := by
  rw [NV7.bflag_eq n a A2 s hA (by omega), NV7.eflag_eq n a s ha (by omega)]
  exact ⟨if_pos (by omega), if_pos has⟩

lemma Lc_D {s : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (has : a ≤ s) (hsp : s < p) :
    Lc n p s = 1 := by
  rw [mn_Lc_eq, (flags_D h5 ha hA hA2 has hsp).1, NV7.q6_eq n a A2 hA (by omega)]

/-- values of the node constants at a `D` residue. -/
lemma tau_D {s0 : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (has : a ≤ s0)
    (hsp : s0 < p) :
    tauU n p s0 1 = -2 * (kapZ n p 1 1 1 : ℚ) ∧ tauV n p s0 1 = -7 * (kapZ n p 1 1 1 : ℚ) := by
  obtain ⟨hb, he⟩ := flags_D h5 ha hA hA2 has hsp
  have hk : s0 + 1 * p ≤ 6 * n := by omega
  have hp1 : 1 < p := by omega
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := NV7.Hq_vals
  have hδ := NV7.laiDelta_class (ℓ := p) n a A2 s0 1 ha hA (by omega) hsp (by norm_num) hk
  constructor
  · unfold tauU
    rw [if_pos hp1, hb, he]
    unfold uL
    rw [g6]; ring
  · unfold tauV
    rw [if_pos ⟨hp1, hk⟩, hb, he]
    unfold vL
    rw [hδ, if_pos has, if_pos (by omega)]
    norm_num [g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]
    ring

lemma map_zphi_evτ (n p s0 : ℕ) (V : ℤ[X]) :
    (V.map zphi).map (evτ n p s0) = V.map (Int.castRingHom ℚ) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext_int _ _

lemma map_zphi_C (V : ℤ[X]) :
    V.map zphi = (V.map (Int.castRingHom ℚ)).map (MvPolynomial.C : ℚ →+* MPT) := by
  rw [Polynomial.map_map]
  rfl

theorem dwin_main (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (V : ℤ[X]) :
    (p : ℚ) ^ (-(3 : ℤ)) *
      (dWinB n p (V.map (Int.castRingHom ℚ)) - Mmain n p (V.map (Int.castRingHom ℚ))) ∈ LocRing p := by
  have h8' : 8 * n < 3 * p := by omega
  have h : Rng n p := band_rng h8' h3n
  have hs0 : a < p := by omega
  have hsW : sig n p a = 5 := sig_D h5 ha hA hA2 le_rfl hs0
  have hJ := dwin_jetMPT h a hs0 hsW V
  have hg : ∀ v : TVar, vτ n p a v ∈ LocRing p := by
    rintro (i | ⟨l, _ | _⟩)
    · fin_cases i <;> simp [vτ, (LocRing p).one_mem, (LocRing p).zero_mem]
    · exact mn_tauU_mem (p := p) n a l
    · exact mn_tauV_mem (p := p) n a h.h8 l
  have hE := GV.evalPt hJ (vτ n p a) hg
  change (p : ℚ) ^ (-(3 : ℤ)) * evτ n p a _ ∈ LocRing p at hE
  simp only [map_sub, map_sum] at hE
  have h1 : ∑ s ∈ Dw n p, ∑ l ∈ range (Lc n p a + 1),
      evτ n p a (nodeT (p := p) n (Kset n p 5) (sigN n p) (clN n p) (tauU n p a) (tauV n p a) (s + l * p)
        (V.map zphi)) = dWinB n p (V.map (Int.castRingHom ℚ)) := by
    unfold dWinB
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨has, hsp⟩ := (D_iff h5 ha hA hA2).1 hs
    rw [Lc_D h5 ha hA hA2 has hsp, Lc_D h5 ha hA hA2 le_rfl hs0]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zphi_C, evτ_nodeT]
  obtain ⟨hU, hV7⟩ := tau_D h5 ha hA hA2 (le_refl a) hs0
  have h2 : ∑ s ∈ Dw n p, evτ n p a (resJet n p s (Lc n p a) 0 (tauU n p a)
      (fun l => (kapZ n p (bflag n p s) (eflag n p s) l : ℚ)) (orthA (cLoc (Lc n p a)) 0) (V.map zphi)) =
      Mmain n p (V.map (Int.castRingHom ℚ)) := by
    unfold Mmain
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨has, hsp⟩ := (D_iff h5 ha hA hA2).1 hs
    rw [Lc_D h5 ha hA hA2 le_rfl hs0, evτ_resJet_L1 n p a s (sig_D h5 ha hA hA2 has hsp),
      evτ_polyEval, evτ_polyEval, map_zphi_evτ, ← Polynomial.derivative_map, map_zphi_evτ, evτ_C, hU, hV7]
    ring
  rw [h1, h2] at hE
  exact hE

end Band

end DMain

/-! ### Part 2: the window sums modulo `p²` -/

section DSums

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma Dz_zero (S : Finset ℕ) (s : ℕ) : Dz S s 0 = 1 := by
  unfold Dz; simp

/-- `c̄_s F(-s) = K G(s) (1 + p(Ξ + e₀))` in `ℤ/p²` for `μ = 0` (the window `D`). -/
lemma cbar_G (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) {s : ℕ} (hs : s ∈ Dw n p) :
    ((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ZMod (p ^ 2)) =
      Kz * G.eval (s : ZMod (p ^ 2)) * jetp p (xiR n p s + e0Z n p s) := by
  have := star_cbar 5 (Dw n p) (fun r => mem_Dw) 0 hμ Kz hK s hs (V.eval (-(s : ℤ))) (G.eval (s : ZMod (p ^ 2)))
    (poly_ident_eval 5 V G hGE s)
  rw [Dz_zero] at this
  simpa using this

lemma rho_cbar_G (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) {s : ℕ} (hs : s ∈ Dw n p) :
    (((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ZMod p)) = ρ Kz * ρ (G.eval (s : ZMod (p ^ 2))) := by
  have h := congrArg ρ (cbar_G Kz hK hμ V G hGE hs)
  rw [map_mul, map_mul, jetp_cast_one, mul_one] at h
  rw [← h]
  simp

lemma rho_eval_map (G : (ZMod (p ^ 2))[X]) (m : ℕ) :
    (G.map ρ).eval ((m : ℕ) : ZMod p) = ρ (G.eval (m : ZMod (p ^ 2))) := by
  rw [← map_natCast ρ m, Polynomial.eval_map, Polynomial.eval₂_at_apply]

/-- a polynomial of degree `≤ p - 2` vanishing off `D ∪ {r}`: `Σ_D G ≡ -G(r)` (mod `p`). -/
lemma sumD_poly (G : (ZMod (p ^ 2))[X]) (hGd : G.natDegree ≤ p - 2) (r : ℕ) (hrp : r < p)
    (hrD : r ∉ Dw n p) (hGv : ∀ m, m < p → m ∉ Dw n p → m ≠ r → G.eval (m : ZMod (p ^ 2)) = 0) :
    ∑ s ∈ Dw n p, ρ (G.eval (s : ZMod (p ^ 2))) = - ρ (G.eval (r : ZMod (p ^ 2))) := by
  have h := sum_window_poly_zero (G.map ρ) (Polynomial.natDegree_map_le.trans hGd) (insert r (Dw n p))
    (fun s hs => by
      rcases Finset.mem_insert.1 hs with rfl | hs
      · exact hrp
      · exact (mem_Dw.1 hs).1)
    (fun m hm hmW => by
      rw [rho_eval_map, hGv m hm (fun h' => hmW (Finset.mem_insert_of_mem h'))
        (fun h' => hmW (h' ▸ Finset.mem_insert_self _ _)), map_zero])
  rw [Finset.sum_insert hrD] at h
  simp only [rho_eval_map] at h
  linear_combination h

lemma sumD_poly_van (G : (ZMod (p ^ 2))[X]) (hGd : G.natDegree ≤ p - 2)
    (hGv : ∀ m, m < p → m ∉ Dw n p → G.eval (m : ZMod (p ^ 2)) = 0) :
    ∑ s ∈ Dw n p, ρ (G.eval (s : ZMod (p ^ 2))) = 0 := by
  have h := sum_window_poly_zero (G.map ρ) (Polynomial.natDegree_map_le.trans hGd) (Dw n p)
    (fun s hs => (mem_Dw.1 hs).1)
    (fun m hm hmW => by rw [rho_eval_map, hGv m hm hmW, map_zero])
  simpa [rho_eval_map] using h

/-- **Lemma SH with a boundary derivative term** (`harmSum_window_neg` without the vanishing of `G'`):
`∑_W G(s) H_{s-α} = ∫G + ∑_{j<α} G'(j)` when `G` vanishes at every residue outside `W`. -/
theorem harmSum_window_neg_d {K : Type*} [CommRing K] [CharP K p] (G : K[X]) (hdeg : G.natDegree ≤ p - 4)
    (h5 : 5 ≤ p) (W : Finset ℕ) (α : ℕ) (hα : α < p) (hW : ∀ s ∈ W, α ≤ s ∧ s < p)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : K) = 0) :
    ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s - α)) =
      harmSum p G + ∑ j ∈ range α, G.derivative.eval ((j : ℕ) : K) := by
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hshift : ∀ m ∈ range p, m ∉ W.image (· - α) →
      (G.comp (X + C (α : K))).eval ((m : ℕ) : K) = 0 := by
    intro m hm hmW
    have hm' : m < p := Finset.mem_range.1 hm
    simp only [eval_comp, eval_add, eval_X, eval_C]
    by_cases hmα : m + α < p
    · have hr : m + α ∉ W := by
        intro h; exact hmW (Finset.mem_image.2 ⟨m + α, h, by omega⟩)
      have := hG (m + α) hmα hr
      rwa [Nat.cast_add] at this
    · have hr : m + α - p ∉ W := by
        intro h; have := hW _ h; omega
      have := hG (m + α - p) (by omega) hr
      rwa [Nat.cast_sub (by omega), Nat.cast_add, hpK, sub_zero] at this
  have hA : ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s - α)) =
      harmSum p (G.comp (X + C (α : K))) := by
    unfold harmSum
    have hinj : Set.InjOn (· - α) (W : Set ℕ) := fun a ha b hb h => by
      have := hW a ha; have := hW b hb; simp only at h; omega
    rw [← Finset.sum_subset (s₁ := W.image (· - α)) (s₂ := range p)
      (fun m hm => by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_range.2 (by have := hW s hs; omega))
      (fun m hm hmW => by rw [hshift m hm hmW, zero_mul]), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hW s hs
    simp only [eval_comp, eval_add, eval_X, eval_C]
    congr 2
    rw [Nat.cast_sub this.1]; ring
  rw [hA, harmSum_shift_nat_neg G hdeg h5 α]

lemma rho_of_p_mul_eq {x y : ZMod (p ^ 2)} (h : (p : ZMod (p ^ 2)) * x = (p : ZMod (p ^ 2)) * y) :
    ρ x = ρ y := by
  have h0 : (p : ZMod (p ^ 2)) * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  set z := x - y with hz
  have h1 : ρ z = ((z.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val z]
    rw [map_natCast]
  have h2 : ((p * z.val : ℕ) : ZMod (p ^ 2)) = 0 := by
    have := h0
    conv_lhs at this => rw [← ZMod.natCast_zmod_val z]
    push_cast
    exact this
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h3 : p ∣ z.val := by
    have : p * p ∣ p * z.val := by rw [← pow_two]; exact h2
    exact (Nat.mul_dvd_mul_iff_left hp.out.pos).1 this
  have : ρ z = 0 := by rw [h1, ZMod.natCast_eq_zero_iff]; exact h3
  rw [hz, map_sub] at this
  exact sub_eq_zero.1 this

/-- **First/second order sum of `c̄_s F(-s)`** over `D` (`G` vanishes off `D`):
`Σ_D c̄_s F(-s) = p S₁` with `S₁ ≡ K (∫G + Σ_D G (Ξ + e₀))` (mod `p`). -/
theorem S_second (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) (hGd : G.natDegree ≤ p - 2)
    (hGv : ∀ m, m < p → m ∉ Dw n p → G.eval (m : ZMod (p ^ 2)) = 0) :
    ∃ S₁ : ℤ, (∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ))) = (p : ℤ) * S₁ ∧
      (S₁ : ZMod p) = ρ Kz * (harmSum p (G.map ρ) +
        ∑ s ∈ Dw n p, ρ (G.eval (s : ZMod (p ^ 2))) * ρ (xiR n p s + e0Z n p s)) := by
  classical
  have hS0 : ((∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [Finset.sum_congr rfl (fun s hs => by
      have := rho_cbar_G Kz hK hμ V G hGE hs
      push_cast at this
      exact this), ← Finset.mul_sum, sumD_poly_van G hGd hGv, mul_zero]
  obtain ⟨S₁, hS₁⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 hS0
  refine ⟨S₁, hS₁, ?_⟩
  obtain ⟨y, hy1, hy2⟩ := faulhaber_bridge G hGd
  have hsub : ∑ s ∈ Dw n p, G.eval (s : ZMod (p ^ 2)) = ∑ s ∈ range p, G.eval (s : ZMod (p ^ 2)) := by
    refine Finset.sum_subset (fun s hs => Finset.mem_range.2 (mem_Dw.1 hs).1) (fun m hm hmW => ?_)
    exact hGv m (Finset.mem_range.1 hm) hmW
  have hZ : ((∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ZMod (p ^ 2)) =
      (p : ZMod (p ^ 2)) * (Kz * (y + ∑ s ∈ Dw n p, G.eval (s : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s))) := by
    push_cast
    rw [Finset.sum_congr rfl (fun s hs => by
      have := cbar_G Kz hK hμ V G hGE hs
      push_cast at this
      exact this)]
    unfold jetp
    have e : ∀ s ∈ Dw n p, Kz * G.eval (s : ZMod (p ^ 2)) * (1 + (p : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s)) =
        Kz * G.eval (s : ZMod (p ^ 2)) + (p : ZMod (p ^ 2)) *
          (Kz * (G.eval (s : ZMod (p ^ 2)) * (xiR n p s + e0Z n p s))) := fun s _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      hsub, hy1]
    ring
  rw [hS₁] at hZ
  push_cast at hZ
  have := rho_of_p_mul_eq (x := (S₁ : ZMod (p ^ 2))) (y := Kz * (y + ∑ s ∈ Dw n p, G.eval (s : ZMod (p ^ 2)) *
    (xiR n p s + e0Z n p s))) hZ
  have hS1 : ρ ((S₁ : ℤ) : ZMod (p ^ 2)) = ((S₁ : ℤ) : ZMod p) := by simp
  rw [← hS1, this, map_mul, map_add, hy2 (ZMod p) ρ, map_sum]
  congr 2
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul]

/-- first order, `G(r) ≠ 0` allowed: `Σ_D c̄_s F(-s) ≡ -K G(r)` (mod `p`). -/
lemma S_first (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) (hGd : G.natDegree ≤ p - 2) (r : ℕ) (hrp : r < p)
    (hrD : r ∉ Dw n p)
    (hGv : ∀ m, m < p → m ∉ Dw n p → m ≠ r → G.eval (m : ZMod (p ^ 2)) = 0) :
    ((∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ZMod p) =
      -(ρ Kz * ρ (G.eval (r : ZMod (p ^ 2)))) := by
  push_cast
  rw [Finset.sum_congr rfl (fun s hs => by
    have := rho_cbar_G Kz hK hμ V G hGE hs
    push_cast at this
    exact this), ← Finset.mul_sum, sumD_poly G hGd r hrp hrD hGv, mul_neg]

/-- the harmonic sums over the window `D`: `H_{s-α}` against `G`, with `G` vanishing off `D`. -/
lemma harmD_sub (Gρ : (ZMod p)[X]) (h5 : 5 ≤ p) (hd : Gρ.natDegree ≤ p - 4) {a A2 n : ℕ} (ha : a + 2 * n = p)
    (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (α : ℕ) (hαa : α ≤ a)
    (hv : ∀ m, m < p → m ∉ Dw n p → Gρ.eval ((m : ℕ) : ZMod p) = 0) :
    ∑ s ∈ Dw n p, Gρ.eval ((s : ℕ) : ZMod p) * harm p (s - α) =
      harmSum p Gρ + ∑ j ∈ range α, Gρ.derivative.eval ((j : ℕ) : ZMod p) := by
  have := harmSum_window_neg_d Gρ hd h5 (Dw n p) α (by omega)
    (fun s hs => by
      obtain ⟨h1, h2⟩ := (D_iff h5 ha hA hA2).1 hs
      exact ⟨by omega, h2⟩) hv
  simpa [ZMod.castHom_self] using this

section BandData

variable {a A2 : ℕ}

lemma band_h1 (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) : 8 * n < 3 * p := by omega

lemma r6_band (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) : r6 n p = A2 := by
  rw [band_r6 (band_h1 ha hA hA2) h3n]; omega

lemma xi_D (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (h3n : p + 1 < 3 * n)
    {s : ℕ} (hs : s ∈ Dw n p) :
    ρ (xiR n p s + e0Z n p s) = -4 * harm p (s - (A2 + 1)) + 3 * harm p (s - a) := by
  obtain ⟨has, hsp⟩ := (D_iff h5 ha hA hA2).1 hs
  have h1 := band_h1 ha hA hA2
  have hR := band_rng (p := p) h1 h3n
  obtain ⟨hb, he⟩ := flags_D h5 ha hA hA2 has hsp
  rw [rho_XiE0 hR hsp, band_lam h1 h3n, band_q6 h1 h3n, band_q2 h1 h3n, band_r6 h1 h3n, band_r2 h1 h3n,
    hb, he]
  have e1 : harm p (6 * n - 2 * p + 1 * p - s) = harm p (s - (A2 + 1)) := by
    have hm : 6 * n - 2 * p + 1 * p - s < p := by omega
    have := harm_refl (p := p) (by omega) hm
    have e : p - 1 - (6 * n - 2 * p + 1 * p - s) = s - (A2 + 1) := by omega
    rw [e] at this
    exact this.symm
  have e2 : 2 * n + s - 1 * p = s - a := by omega
  rw [e1, e2]
  push_cast
  ring

end BandData

section BandSums

variable {a A2 : ℕ}

/-- `Σ_{j<α} G'(j)` when `G'` vanishes at every `j < α` except `r`. -/
lemma sum_deriv_single (Gρ : (ZMod p)[X]) (α r : ℕ)
    (hv : ∀ j, j < α → j ≠ r → Gρ.derivative.eval ((j : ℕ) : ZMod p) = 0) :
    ∑ j ∈ range α, Gρ.derivative.eval ((j : ℕ) : ZMod p) =
      if r < α then Gρ.derivative.eval ((r : ℕ) : ZMod p) else 0 := by
  by_cases hr : r < α
  · rw [if_pos hr]
    refine Finset.sum_eq_single_of_mem r (Finset.mem_range.2 hr) fun j hj hjr => ?_
    exact hv j (Finset.mem_range.1 hj) hjr
  · rw [if_neg hr]
    refine Finset.sum_eq_zero fun j hj => ?_
    have := Finset.mem_range.1 hj
    exact hv j this (by omega)

/-- **Second-order window sum** (`G` vanishes off `D`, `G'` vanishes on `A ∪ C` except at the own residue `r`):
`Σ_D c̄_s F(-s) = p S₁`, `S̄₁ = K (3 [r < a] G'(r) - 4 [r ≤ A₂] G'(r))`. -/
theorem S_value (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) (hGd : G.natDegree ≤ p - 4)
    (hGv : ∀ m, m < p → m ∉ Dw n p → G.eval (m : ZMod (p ^ 2)) = 0) (r : ℕ)
    (hG' : ∀ j, j < a → j ≠ r → (G.map ρ).derivative.eval ((j : ℕ) : ZMod p) = 0) :
    ∃ S₁ : ℤ, (∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ))) = (p : ℤ) * S₁ ∧
      (S₁ : ZMod p) = ρ Kz * (3 * (if r < a then (G.map ρ).derivative.eval ((r : ℕ) : ZMod p) else 0) -
        4 * (if r < A2 + 1 then (G.map ρ).derivative.eval ((r : ℕ) : ZMod p) else 0)) := by
  obtain ⟨S₁, hS, hS₁⟩ := S_second Kz hK hμ V G hGE (by omega) hGv
  refine ⟨S₁, hS, ?_⟩
  rw [hS₁]
  have hGρd : (G.map ρ).natDegree ≤ p - 4 := Polynomial.natDegree_map_le.trans hGd
  have hvρ : ∀ m, m < p → m ∉ Dw n p → (G.map ρ).eval ((m : ℕ) : ZMod p) = 0 := fun m hm hmW => by
    rw [rho_eval_map, hGv m hm hmW, map_zero]
  have hA1 := harmD_sub (G.map ρ) h5 hGρd ha hA hA2 (A2 + 1) (by omega) hvρ
  have hA2' := harmD_sub (G.map ρ) h5 hGρd ha hA hA2 a le_rfl hvρ
  rw [sum_deriv_single _ _ r (fun j hj hjr => hG' j (by omega) hjr)] at hA1
  rw [sum_deriv_single _ _ r (fun j hj hjr => hG' j hj hjr)] at hA2'
  have e : ∑ s ∈ Dw n p, ρ (G.eval (s : ZMod (p ^ 2))) * ρ (xiR n p s + e0Z n p s) =
      -4 * ∑ s ∈ Dw n p, (G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (s - (A2 + 1)) +
        3 * ∑ s ∈ Dw n p, (G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (s - a) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [xi_D h5 ha hA hA2 h3n hs, rho_eval_map]
    ring
  rw [e, hA1, hA2']
  ring

lemma lam0_D (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (h3n : p + 1 < 3 * n)
    {s : ℕ} (hs : s ∈ Dw n p) :
    ρ (lam0Z n p s) = -5 * harm p s + 2 * harm p (s - (A2 + 1)) + 3 * harm p (s - a) := by
  obtain ⟨has, hsp⟩ := (D_iff h5 ha hA hA2).1 hs
  have h1 := band_h1 ha hA hA2
  have hR := band_rng (p := p) h1 h3n
  obtain ⟨hb, he⟩ := flags_D h5 ha hA hA2 has hsp
  rw [rho_lam0 hR hsp, band_r6 h1 h3n, band_r2 h1 h3n, hb, he]
  have e1 : harm p (6 * n - 2 * p + 1 * p - s) = harm p (s - (A2 + 1)) := by
    have hm : 6 * n - 2 * p + 1 * p - s < p := by omega
    have := harm_refl (p := p) (by omega) hm
    have e : p - 1 - (6 * n - 2 * p + 1 * p - s) = s - (A2 + 1) := by omega
    rw [e] at this
    exact this.symm
  have e2 : 2 * n + s - 1 * p = s - a := by omega
  rw [e1, e2]

/-- `λ₀(s)` as an element of `ℤ_(p)` (junk value `0` for `s ≥ p`). -/
def lam0L (n p s : ℕ) [Fact p.Prime] : LocRing p :=
  if h : s < p then ⟨lam0 n p s, lam0_mem n s h⟩ else 0

lemma lam0L_val {s : ℕ} (hs : s < p) : (lam0L n p s : ℚ) = lam0 n p s := by
  unfold lam0L; rw [dif_pos hs]

lemma redQ_lam0L {s : ℕ} (hs : s < p) : redQ p (lam0L n p s) = ρ (lam0Z n p s) := by
  unfold lam0L; rw [dif_pos hs]; exact redQ_lam0 n s hs

/-- the rational sum `U = Σ_D c̄_s λ₀(s) F(-s)` and its reduction. -/
theorem U_value (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s))
    (hμ : ∀ r ∈ Dw n p, mu n p r = 0) (V : ℤ[X]) (G : (ZMod (p ^ 2))[X])
    (hGE : G * Epoly n p 5 = QhatPoly n p 5 * Vneg p V) (hGd : G.natDegree ≤ p - 4)
    (hGv : ∀ m, m < p → m ∉ Dw n p → G.eval (m : ZMod (p ^ 2)) = 0) (r : ℕ)
    (hG' : ∀ j, j < a → j ≠ r → (G.map ρ).derivative.eval ((j : ℕ) : ZMod p) = 0) :
    ∃ u : LocRing p, (u : ℚ) = ∑ s ∈ Dw n p, (cbarZ n p s : ℚ) * lam0 n p s * ((V.eval (-(s : ℤ)) : ℤ) : ℚ) ∧
      redQ p u = ρ Kz * (2 * (if r < A2 + 1 then (G.map ρ).derivative.eval ((r : ℕ) : ZMod p) else 0) +
        3 * (if r < a then (G.map ρ).derivative.eval ((r : ℕ) : ZMod p) else 0)) := by
  have hGρd : (G.map ρ).natDegree ≤ p - 4 := Polynomial.natDegree_map_le.trans hGd
  have hvρ : ∀ m, m < p → m ∉ Dw n p → (G.map ρ).eval ((m : ℕ) : ZMod p) = 0 := fun m hm hmW => by
    rw [rho_eval_map, hGv m hm hmW, map_zero]
  have hA0 := harmD_sub (G.map ρ) h5 hGρd ha hA hA2 0 (by omega) hvρ
  have hA1 := harmD_sub (G.map ρ) h5 hGρd ha hA hA2 (A2 + 1) (by omega) hvρ
  have hA2' := harmD_sub (G.map ρ) h5 hGρd ha hA hA2 a le_rfl hvρ
  rw [sum_deriv_single _ _ r (fun j hj hjr => hG' j (by omega) hjr)] at hA1
  rw [sum_deriv_single _ _ r (fun j hj hjr => hG' j hj hjr)] at hA2'
  simp only [Nat.sub_zero, Finset.range_zero, Finset.sum_empty, add_zero] at hA0
  refine ⟨∑ s ∈ Dw n p, lam0L n p s * ((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : LocRing p), ?_, ?_⟩
  · push_cast
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [lam0L_val (mem_Dw.1 hs).1]
    ring
  · rw [map_sum]
    have e : ∀ s ∈ Dw n p, redQ p (lam0L n p s * ((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : LocRing p)) =
        ρ Kz * (-5 * ((G.map ρ).eval ((s : ℕ) : ZMod p) * harm p s) +
          2 * ((G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (s - (A2 + 1))) +
          3 * ((G.map ρ).eval ((s : ℕ) : ZMod p) * harm p (s - a))) := by
      intro s hs
      rw [map_mul, redQ_lam0L (mem_Dw.1 hs).1, lam0_D h5 ha hA hA2 h3n hs, map_intCast,
        rho_cbar_G Kz hK hμ V G hGE hs, rho_eval_map]
      ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hA0, hA1, hA2']
    ring

end BandSums

end DSums

/-! ### Part 3: the polynomial data `G, H` of an own pair -/

section OwnData

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

theorem dn_sigmu (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 0 ∧ mu n p s = 3 ∧ s ≤ 6 * n - 2 * p) ∨
    (sig n p s = 2 ∧ mu n p s = 2 ∧ 6 * n - 2 * p < s ∧ s < p - 2 * n) ∨
    (sig n p s = 5 ∧ mu n p s = 0 ∧ p - 2 * n ≤ s) := by
  have h := band_rng (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hlam := band_lam (p := p) h1 h2
  have hmu := mu_formula h hs
  rw [hlam] at hmu
  have e : sig n p s = (if s ≤ 6 * n - 2 * p then 0 else 2) + (if p - 2 * n ≤ s then 3 else 0) := by
    unfold sig; rw [hr6, hr2]
  by_cases c1 : s ≤ 6 * n - 2 * p
  · have c2 : ¬ p - 2 * n ≤ s := by omega
    have hsg : sig n p s = 0 := by rw [e, if_pos c1, if_neg c2]
    refine Or.inl ⟨hsg, ?_, c1⟩
    rw [hmu, hsg]; norm_num
  · by_cases c2 : p - 2 * n ≤ s
    · have hsg : sig n p s = 5 := by rw [e, if_neg c1, if_pos c2]
      refine Or.inr (Or.inr ⟨hsg, ?_, c2⟩)
      rw [hmu, hsg]; norm_num
    · have hsg : sig n p s = 2 := by rw [e, if_neg c1, if_neg c2]
      refine Or.inr (Or.inl ⟨hsg, ?_, by omega, by omega⟩)
      rw [hmu, hsg]; norm_num

theorem dn_mexp (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 5 → mexp n p 5 s = 0) ∧ (sig n p s ≠ 5 → mexp n p 5 s = 3) := by
  have hlam := band_lam (p := p) h1 h2
  rcases dn_sigmu h1 h2 s hs with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨hg, -⟩
  · refine ⟨fun e => by omega, fun _ => ?_⟩
    unfold mexp; rw [hlam, hg]; norm_num
  · refine ⟨fun e => by omega, fun _ => ?_⟩
    unfold mexp; rw [hlam, hg]; norm_num
  · refine ⟨fun _ => ?_, fun e => absurd hg e⟩
    unfold mexp; rw [hlam, hg]; norm_num

theorem dn_mF (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (s : ℕ) (hs : s < p) :
    (sig n p s = 5 → mF n p 5 s = 0) ∧ (sig n p s ≠ 5 → mF n p 5 s = mu n p s + 1) := by
  refine ⟨fun e => ?_, fun e => ?_⟩
  · unfold mF; rw [if_pos e]
    rcases dn_sigmu h1 h2 s hs with ⟨hg, -⟩ | ⟨hg, -⟩ | ⟨-, hm, -⟩ <;> omega
  · unfold mF; rw [if_neg e]

/-- the exponent function of `g` in `G = ± ∏ (q - X)^{g_q}`. -/
def gmOwn (n p r g0 : ℕ) : ℕ → ℕ := fun q => if q = r then g0 else mexp n p 5 q

/-- the exponents of `V(-X)` for the own pair `e_{r,i} e_{r,i'}`, `m = i + i'`. -/
def exOwn (n p r m : ℕ) : ℕ → ℕ := fun q =>
  if sig n p q = 5 then 0 else if q = r then m else 2 * mF n p 5 q

lemma exF_own {r : ℕ} (hr : r < p) {i : ℕ} (hi : i < mF n p 5 r) (q : ℕ) :
    exF n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ : FIdx n p 5) q =
      if sig n p q = 5 then 0 else if q = r then i else mF n p 5 q := by
  unfold exF poleF
  by_cases h5 : sig n p q = 5
  · simp [h5]
  · by_cases hq : q = r
    · subst hq; simp [h5, Nat.sub_sub_self hi.le]
    · have : ¬ r = q := fun e => hq e.symm
      simp [h5, hq, this]

lemma ExZ_own {r : ℕ} (hr : r < p) {i i' : ℕ} (hi : i < mF n p 5 r) (hi' : i' < mF n p 5 r) :
    ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ : FIdx n p 5) * ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i', hi'⟩⟩ : FIdx n p 5) =
      ∏ q ∈ range p, (Polynomial.X + Polynomial.C (q : ℤ)) ^ exOwn n p r (i + i') q := by
  rw [ExZ_mul]
  simp only [jF, add_zero, pow_zero, one_mul]
  refine Finset.prod_congr rfl fun q _ => ?_
  congr 1
  rw [exF_own hr hi, exF_own hr hi']
  unfold exOwn
  by_cases h5 : sig n p q = 5
  · simp [h5]
  · by_cases hq : q = r
    · subst hq; simp [h5]
    · simp [h5, hq]; ring

/-- the sign `(-1)^{Σ m_q}`. -/
def sgnOwn (n p : ℕ) : ZMod (p ^ 2) := (-1) ^ (∑ q ∈ range p, mexp n p 5 q)

/-- `G = ± ∏ (q - X)^{g_q}`. -/
def gOwn (n p r g0 : ℕ) : (ZMod (p ^ 2))[X] := Polynomial.C (sgnOwn n p) * Pr (cR p) (range p) (gmOwn n p r g0)

/-- `H = ± Σ_q ex_q ∏ ..`. -/
def hOwn (n p r g0 m : ℕ) : (ZMod (p ^ 2))[X] :=
  Polynomial.C (sgnOwn n p) * Ht (cR p) (range p) (gmOwn n p r g0) (exOwn n p r m)

lemma own_hkey (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hrW : sig n p r ≠ 5) {m g0 : ℕ}
    (hg : g0 + 2 * mu n p r + 2 = 3 + m) :
    ∀ q ∈ range p, gmOwn n p r g0 q + e2F n p 5 q = mexp n p 5 q + exOwn n p r m q := by
  intro q hq
  have hqp := Finset.mem_range.1 hq
  simp only [gmOwn, exOwn, e2F, gexp]
  by_cases h5 : sig n p q = 5
  · have hqr : q ≠ r := fun e => hrW (e ▸ h5)
    simp [h5, hqr, (dn_mexp h1 h2 q hqp).1 h5]
  · have hm3 := (dn_mexp h1 h2 q hqp).2 h5
    by_cases hqr : q = r
    · subst hqr
      simp [h5, hm3]
      omega
    · have hmF := (dn_mF h1 h2 q hqp).2 h5
      simp [h5, hqr, hm3, hmF]
      omega

lemma own_V (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) {i i' : ℕ} (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) :
    Vneg p (ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ : FIdx n p 5) *
        ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i', hi'⟩⟩ : FIdx n p 5)) =
      Pr (cR p) (range p) (exOwn n p r (i + i')) := by
  rw [ExZ_own hr hi hi']
  have := Vneg_form (p := p) 0 (exOwn n p r (i + i'))
  simpa using this

theorem gOwn_identity (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) (hrW : sig n p r ≠ 5)
    {i i' : ℕ} (hi : i < mF n p 5 r) (hi' : i' < mF n p 5 r) {g0 : ℕ}
    (hg : g0 + 2 * mu n p r + 2 = 3 + (i + i')) :
    gOwn n p r g0 * Epoly n p 5 = QhatPoly n p 5 *
      Vneg p (ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ : FIdx n p 5) *
        ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i', hi'⟩⟩ : FIdx n p 5)) := by
  have hkey := own_hkey h1 h2 hrW hg
  have hP : Pr (cR p) (range p) (gmOwn n p r g0) * Pr (cR p) (range p) (e2F n p 5) =
      Pr (cR p) (range p) (mexp n p 5) * Pr (cR p) (range p) (exOwn n p r (i + i')) := by
    rw [Pr_mul, Pr_mul]
    exact Pr_congr _ _ (fun q hq => hkey q hq)
  rw [own_V h1 h2 hr hi hi', Epoly_eq, Qhat_eq]
  unfold gOwn sgnOwn
  linear_combination (Polynomial.C ((-1 : ZMod (p ^ 2)) ^ ∑ q ∈ range p, mexp n p 5 q)) * hP

theorem hOwn_identity (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) (hrW : sig n p r ≠ 5)
    {i i' : ℕ} (hi : i < mF n p 5 r) (hi' : i' < mF n p 5 r) {g0 : ℕ} (hg0 : 1 ≤ g0)
    (hg : g0 + 2 * mu n p r + 2 = 3 + (i + i')) :
    hOwn n p r g0 (i + i') * Epoly n p 5 = QhatPoly n p 5 *
      Vneg p (Polynomial.derivative (ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i, hi⟩⟩ : FIdx n p 5) *
        ExZ n p 5 (Sum.inl ⟨⟨r, hr⟩, ⟨i', hi'⟩⟩ : FIdx n p 5))) := by
  have hkey := own_hkey h1 h2 hrW hg
  have hpos : ∀ q ∈ range p, 1 ≤ exOwn n p r (i + i') q →
      1 ≤ gmOwn n p r g0 q ∧ 1 ≤ exOwn n p r (i + i') q := by
    intro q hq hex
    have hqp := Finset.mem_range.1 hq
    refine ⟨?_, hex⟩
    unfold gmOwn
    by_cases hqr : q = r
    · rw [if_pos hqr]; exact hg0
    · rw [if_neg hqr]
      have h5 : ¬ sig n p q = 5 := by
        intro h5
        unfold exOwn at hex
        rw [if_pos h5] at hex
        omega
      rw [(dn_mexp h1 h2 q hqp).2 h5]; omega
  have hH : Ht (cR p) (range p) (gmOwn n p r g0) (exOwn n p r (i + i')) * Pr (cR p) (range p) (e2F n p 5) =
      Pr (cR p) (range p) (mexp n p 5) * Ht (cR p) (range p) (exOwn n p r (i + i')) (exOwn n p r (i + i')) :=
    Ht_mul (cR p) (range p) (gmOwn n p r g0) (exOwn n p r (i + i')) (e2F n p 5) (mexp n p 5)
      (exOwn n p r (i + i')) (fun q hq => by have := hkey q hq; omega) hpos
  rw [Vneg_deriv, own_V h1 h2 hr hi hi', derivative_Pr, neg_neg, Epoly_eq, Qhat_eq]
  unfold hOwn sgnOwn
  linear_combination (Polynomial.C ((-1 : ZMod (p ^ 2)) ^ ∑ q ∈ range p, mexp n p 5 q)) * hH

end OwnData

/-! ### Part 4: values, vanishing and degrees of `G, H` -/

section OwnValues

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma eval_Pr' (c : ℕ → ZMod (p ^ 2)) (N : Finset ℕ) (a : ℕ → ℕ) (x : ZMod (p ^ 2)) :
    (Pr c N a).eval x = ∏ q ∈ N, (c q - x) ^ a q := by
  unfold Pr qq
  simp [Polynomial.eval_prod]

/-- `∏_{q ≠ r} (q - r)^{m_q}`. -/
def P3r (n p r : ℕ) : ZMod (p ^ 2) :=
  ∏ q ∈ (range p).erase r, ((q : ZMod (p ^ 2)) - (r : ZMod (p ^ 2))) ^ mexp n p 5 q

lemma gOwn_eval_r0 {r : ℕ} (hr : r < p) :
    (gOwn n p r 0).eval (r : ZMod (p ^ 2)) = sgnOwn n p * P3r n p r := by
  unfold gOwn
  rw [Polynomial.eval_mul, Polynomial.eval_C, eval_Pr', ← Finset.mul_prod_erase (range p) _ (Finset.mem_range.2 hr)]
  unfold gmOwn P3r cR
  simp only [if_true, pow_zero, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [if_neg (Finset.ne_of_mem_erase hq)]

lemma Pl_eval_r {r : ℕ} (hr : r < p) :
    (Pl (cR p) (range p) (gmOwn n p r 1) r).eval (r : ZMod (p ^ 2)) = P3r n p r := by
  unfold Pl
  rw [Polynomial.eval_mul, Polynomial.eval_prod]
  unfold gmOwn P3r cR
  simp only [if_true, Nat.sub_self, pow_zero, Polynomial.eval_pow, Polynomial.eval_one, one_mul]
  refine Finset.prod_congr rfl fun q hq => ?_
  rw [if_neg (Finset.ne_of_mem_erase hq)]
  simp [qq]

lemma gOwn_deriv_r1 {r : ℕ} (hr : r < p) :
    (gOwn n p r 1).derivative.eval (r : ZMod (p ^ 2)) = -(sgnOwn n p * P3r n p r) := by
  have hPr : Pr (cR p) (range p) (gmOwn n p r 1) =
      qq (cR p) r * Pl (cR p) (range p) (gmOwn n p r 1) r :=
    Pr_eq_Pl _ _ _ (Finset.mem_range.2 hr) (by simp [gmOwn])
  unfold gOwn
  rw [Polynomial.derivative_C_mul, hPr, Polynomial.derivative_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul, Pl_eval_r hr]
  simp [qq, cR]

lemma hOwn_eval_r1 {r : ℕ} (hr : r < p) (m : ℕ) :
    (hOwn n p r 1 m).eval (r : ZMod (p ^ 2)) =
      sgnOwn n p * ((exOwn n p r m r : ℕ) * P3r n p r) := by
  unfold hOwn Ht
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finset_sum]
  congr 1
  rw [Finset.sum_eq_single r]
  · rw [Polynomial.eval_mul, Polynomial.eval_C, Pl_eval_r hr]
  · intro q hq hqr
    have : (Pl (cR p) (range p) (gmOwn n p r 1) q).eval (r : ZMod (p ^ 2)) = 0 := by
      unfold Pl
      rw [Polynomial.eval_mul, Polynomial.eval_prod]
      have hz : ∏ x ∈ (range p).erase q, (qq (cR p) x ^ gmOwn n p r 1 x).eval (r : ZMod (p ^ 2)) = 0 := by
        refine Finset.prod_eq_zero (i := r) (Finset.mem_erase.2 ⟨fun e => hqr e.symm, Finset.mem_range.2 hr⟩) ?_
        simp [gmOwn, qq, cR]
      rw [hz, mul_zero]
    rw [Polynomial.eval_mul, this, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hr) h

lemma not_D_of_lt {a A2 : ℕ} (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    {q : ℕ} (hq : q < a) : q ∉ Dw n p := by
  intro h
  have := (D_iff h5 ha hA hA2).1 h
  omega

section Vanish

variable {a A2 : ℕ}

lemma sig_ne5_of_notD {m : ℕ} (hm : m < p) (hD : m ∉ Dw n p) : sig n p m ≠ 5 :=
  fun e => hD (mem_Dw.2 ⟨hm, e⟩)

lemma gOwn_van (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} {g0 : ℕ} {m : ℕ} (hm : m < p)
    (hD : m ∉ Dw n p) (hmr : m ≠ r ∨ 1 ≤ g0) :
    (gOwn n p r g0).eval (m : ZMod (p ^ 2)) = 0 := by
  have h5 := sig_ne5_of_notD hm hD
  have hg : 1 ≤ gmOwn n p r g0 m := by
    unfold gmOwn
    by_cases hmr' : m = r
    · rw [if_pos hmr']; rcases hmr with h | h
      · exact absurd hmr' h
      · exact h
    · rw [if_neg hmr', (dn_mexp h1 h2 m hm).2 h5]; omega
  unfold gOwn
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have := eval_Pr_zero (cR p) (range p) (gmOwn n p r g0) (Finset.mem_range.2 hm) hg
  simp only [cR] at this
  rw [this, mul_zero]

lemma gOwn_deriv_van (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r g0 : ℕ} {m : ℕ} (hm : m < p)
    (hD : m ∉ Dw n p) (hmr : m ≠ r) :
    (gOwn n p r g0).derivative.eval (m : ZMod (p ^ 2)) = 0 := by
  have h5 := sig_ne5_of_notD hm hD
  have hg : 2 ≤ gmOwn n p r g0 m := by
    unfold gmOwn
    rw [if_neg hmr, (dn_mexp h1 h2 m hm).2 h5]; omega
  unfold gOwn
  rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  have := eval_derivative_Pr_zero (cR p) (range p) (gmOwn n p r g0) (Finset.mem_range.2 hm) hg
  simp only [cR] at this
  rw [this, mul_zero]

lemma hOwn_van (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r g0 m0 : ℕ} {m : ℕ} (hm : m < p)
    (hD : m ∉ Dw n p) (hmr : m ≠ r) :
    (hOwn n p r g0 m0).eval (m : ZMod (p ^ 2)) = 0 := by
  have h5 := sig_ne5_of_notD hm hD
  have hg : 2 ≤ gmOwn n p r g0 m := by
    unfold gmOwn
    rw [if_neg hmr, (dn_mexp h1 h2 m hm).2 h5]; omega
  unfold hOwn
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have := eval_Ht_zero (cR p) (range p) (gmOwn n p r g0) (exOwn n p r m0) (Finset.mem_range.2 hm) hg
  simp only [cR] at this
  rw [this, mul_zero]

end Vanish

section Degrees

lemma sum_mexp_band (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) :
    ∑ q ∈ range p, mexp n p 5 q = 3 * (p - 2 * n) := by
  classical
  have h := band_rng (p := p) h1 h2
  have hr6 := band_r6 (p := p) h1 h2
  have hr2 := band_r2 (p := p) h1 h2
  have hcard : ((range p).filter (fun s => sig n p s = 5)).card = tieW n p := by
    rw [card_sig_five h, (band_xtwo h1 h2).2]
    unfold szD; rw [hr6, hr2]; omega
  have := sum_mexp_eq h 5 hcard (band_xtwo_pos h1 h2)
  have hx : (xtwo n p).toNat = 3 * n - 1 - p := by
    rw [(band_xtwo h1 h2).1]; simp
  rw [hx] at this
  omega

lemma sum_gm_band (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) (hrW : sig n p r ≠ 5)
    (g0 : ℕ) : ∑ q ∈ range p, gmOwn n p r g0 q + 3 = 3 * (p - 2 * n) + g0 := by
  classical
  have hmr : mexp n p 5 r = 3 := (dn_mexp h1 h2 r hr).2 hrW
  rw [← sum_mexp_band h1 h2, ← Finset.add_sum_erase (range p) _ (Finset.mem_range.2 hr),
    ← Finset.add_sum_erase (range p) (fun q => mexp n p 5 q) (Finset.mem_range.2 hr)]
  have : ∑ q ∈ (range p).erase r, gmOwn n p r g0 q = ∑ q ∈ (range p).erase r, mexp n p 5 q :=
    Finset.sum_congr rfl fun q hq => by unfold gmOwn; rw [if_neg (Finset.ne_of_mem_erase hq)]
  rw [this, hmr]
  unfold gmOwn
  rw [if_pos rfl]
  omega

lemma gOwn_deg (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) (hrW : sig n p r ≠ 5)
    (g0 : ℕ) : (gOwn n p r g0).natDegree ≤ 3 * (p - 2 * n) + g0 - 3 := by
  have := sum_gm_band h1 h2 hr hrW g0
  unfold gOwn
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_Pr_le _ _ _).trans ?_
  omega

lemma hOwn_deg (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {r : ℕ} (hr : r < p) (hrW : sig n p r ≠ 5)
    (g0 m : ℕ) : (hOwn n p r g0 m).natDegree ≤ 3 * (p - 2 * n) + g0 - 3 := by
  have := sum_gm_band h1 h2 hr hrW g0
  unfold hOwn
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_Ht_le _ _ _ _).trans ?_
  omega

end Degrees

section RhoValues

lemma rho_sgn (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {a : ℕ} (ha : a + 2 * n = p) (hodd : a % 2 = 1) :
    ρ (sgnOwn n p) = -1 := by
  unfold sgnOwn
  rw [map_pow, map_neg, map_one, sum_mexp_band h1 h2]
  have : p - 2 * n = a := by omega
  rw [this]
  exact Odd.neg_one_pow (by rw [Nat.odd_iff]; omega)

lemma rho_P3r (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) {a A2 r : ℕ} (ha : a + 2 * n = p)
    (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (hodd : a % 2 = 1) (hr : r < a) :
    ρ (P3r n p r) = B83.PrB p a r ^ 3 := by
  have hap : a ≤ p := by omega
  unfold P3r
  rw [map_prod]
  simp only [map_pow, map_sub, map_natCast]
  have hsub : (range a).erase r ⊆ (range p).erase r := Finset.erase_subset_erase r (Finset.range_subset_range.2 hap)
  rw [← Finset.prod_subset hsub (fun q hq hq' => by
    have hqa : ¬ q < a := fun h => hq' (Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hq).1, Finset.mem_range.2 h⟩)
    have hqp := Finset.mem_range.1 (Finset.mem_erase.1 hq).2
    have hs5 : sig n p q = 5 := sig_D h5 ha hA hA2 (by omega) hqp
    rw [(dn_mexp h1 h2 q hqp).1 hs5, pow_zero])]
  have hc : ∀ q ∈ (range a).erase r, (((q : ℕ) : ZMod p) - ((r : ℕ) : ZMod p)) ^ mexp n p 5 q =
      (-1) ^ 3 * (((r : ℕ) : ZMod p) - ((q : ℕ) : ZMod p)) ^ 3 := by
    intro q hq
    have hqa := Finset.mem_range.1 (Finset.mem_erase.1 hq).2
    have hs5 := not_D_of_lt h5 ha hA hA2 hqa
    rw [(dn_mexp h1 h2 q (by omega)).2 (sig_ne5_of_notD (by omega) hs5)]
    ring
  rw [Finset.prod_congr rfl hc, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow,
    Finset.card_erase_of_mem (Finset.mem_range.2 hr), Finset.card_range]
  unfold B83.PrB
  have : ((-1 : ZMod p) ^ 3) ^ (a - 1) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    have : Even (a - 1) := by rw [Nat.even_iff]; omega
    have h' : ((-1 : ZMod p) ^ (a - 1)) = 1 := this.neg_one_pow
    rw [h']; simp
  rw [this, one_mul]

end RhoValues

end OwnValues

/-! ### Part 5: the unit `K` -/

section KzVal

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma rho_Jt_last (h5 : 5 ≤ p) {a' : ℕ} (ha' : a' ≤ p - 1) :
    ρ (Jt p a' (p - 1)) = (((p - 1 - a') ! : ℕ) : ZMod p) := by
  have := Jt_ge p a' (p - 1 - a') 0 (by omega)
  rw [show a' + (p - 1 - a') = p - 1 by omega] at this
  rw [this]
  simp

lemma rho_fact (m : ℕ) : ρ ((m ! : ℕ) : ZMod (p ^ 2)) = ((m ! : ℕ) : ZMod p) := by
  rw [map_natCast]

lemma rho_fact_inv {m : ℕ} (hm : m < p) : ρ (((m ! : ℕ) : ZMod (p ^ 2))⁻¹) = (((m ! : ℕ) : ZMod p))⁻¹ := by
  rw [rho_inv (isUnit_fact_p2 (p := p) m hm), rho_fact]

theorem kz_alg {F : Type*} [Field F] {A B Fv E D W Pe Cs Qh Kz : F} (hB : B ≠ 0)
    (hFv : Fv ≠ 0) (hE : E ≠ 0) (hD : D ≠ 0) (hW : W ≠ 0)
    (hPe : Pe * (Fv ^ 2 * E ^ 6) = W ^ 8) (hQ : Qh * E ^ 3 = W ^ 3)
    (hCs : Cs = (A / (W * B)) ^ 2 * (E / (W * D)) ^ 3) (hK : Cs * Pe = Kz * Qh)
    (hBF : B ^ 2 * Fv ^ 2 = 1) : Kz = A ^ 2 / D ^ 3 := by
  have hPe' : Pe = W ^ 8 / (Fv ^ 2 * E ^ 6) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ hFv) (pow_ne_zero _ hE))]; exact hPe
  have hQ' : Qh = W ^ 3 / E ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hE)]; exact hQ
  rw [hPe', hQ', hCs] at hK
  rw [eq_div_iff (pow_ne_zero _ hD)]
  field_simp at hK
  linear_combination hK.symm - (Kz * D ^ 3) * hBF

lemma Pe_gexp_band {a A2 : ℕ} (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (ha : a + 2 * n = p)
    (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) (s : ℕ) :
    Pe p (gexp n p 5) s * (Jt p (A2 + 1) s ^ 2 * Jt p a s ^ 6) = Jt p 0 s ^ 8 := by
  have hsum : ∀ r < p, gexp n p 5 r +
      ((fun r => 2 * (if A2 + 1 ≤ r then 1 else 0) + 6 * (if a ≤ r then 1 else 0)) r) = (fun _ => 8) r := by
    intro r hr
    unfold gexp
    simp only
    rcases dn_sigmu h1 h2 r hr with ⟨hg, hm, hc⟩ | ⟨hg, hm, hc, hc'⟩ | ⟨hg, hm, hc⟩
    · have e1 : ¬ A2 + 1 ≤ r := by omega
      have e2 : ¬ a ≤ r := by omega
      simp [hg, hm, e1, e2]
    · have e1 : A2 + 1 ≤ r := by omega
      have e2 : ¬ a ≤ r := by omega
      simp [hg, hm, e1, e2]
    · have e1 : A2 + 1 ≤ r := by omega
      have e2 : a ≤ r := by omega
      simp [hg, hm, e1, e2]
  calc Pe p (gexp n p 5) s * (Jt p (A2 + 1) s ^ 2 * Jt p a s ^ 6)
      = Pe p (gexp n p 5) s * Pe p (fun r => 2 * (if A2 + 1 ≤ r then 1 else 0) + 6 * (if a ≤ r then 1 else 0)) s := by
        rw [Pe_add, Pe_smul, Pe_smul, Pe_ind, Pe_ind]
    _ = Pe p (fun r => gexp n p 5 r + (2 * (if A2 + 1 ≤ r then 1 else 0) + 6 * (if a ≤ r then 1 else 0))) s :=
        (Pe_add _ _ _).symm
    _ = Pe p (fun _ => 8) s := Pe_congr _ _ _ hsum
    _ = Jt p 0 s ^ 8 := Pe_const 8 s

lemma Qhat_band {a A2 : ℕ} (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) (ha : a + 2 * n = p)
    (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a) {s : ℕ} (hs : s ∈ Dw n p) :
    Qhat n p 5 s * Jt p a s ^ 3 = Jt p 0 s ^ 3 := by
  obtain ⟨has, hsp⟩ := (D_iff h5 ha hA hA2).1 hs
  have hq : Qhat n p 5 s = Pe p (mexp n p 5) s := by
    unfold Qhat Pe
    refine Finset.prod_congr rfl fun r _ => ?_
    by_cases hr : r = s
    · subst hr; rw [if_pos rfl, (dn_mexp h1 h2 r hsp).1 (sig_D h5 ha hA hA2 has hsp), pow_zero]
    · rw [if_neg hr]
  have hsum : ∀ r < p, mexp n p 5 r + ((fun r => 3 * (if a ≤ r then 1 else 0)) r) = (fun _ => 3) r := by
    intro r hr
    simp only
    rcases dn_sigmu h1 h2 r hr with ⟨hg, hm, hc⟩ | ⟨hg, hm, hc, hc'⟩ | ⟨hg, hm, hc⟩
    · have e2 : ¬ a ≤ r := by omega
      rw [(dn_mexp h1 h2 r hr).2 (by omega), if_neg e2]
    · have e2 : ¬ a ≤ r := by omega
      rw [(dn_mexp h1 h2 r hr).2 (by omega), if_neg e2]
    · have e2 : a ≤ r := by omega
      rw [(dn_mexp h1 h2 r hr).1 hg, if_pos e2]
  rw [hq]
  calc Pe p (mexp n p 5) s * Jt p a s ^ 3
      = Pe p (mexp n p 5) s * Pe p (fun r => 3 * (if a ≤ r then 1 else 0)) s := by
        rw [Pe_smul, Pe_ind]
    _ = Pe p (fun r => mexp n p 5 r + 3 * (if a ≤ r then 1 else 0)) s := (Pe_add _ _ _).symm
    _ = Pe p (fun _ => 3) s := Pe_congr _ _ _ hsum
    _ = Jt p 0 s ^ 3 := Pe_const 3 s

section KzMain

variable {a A2 : ℕ}

lemma dn_fz_ne {m : ℕ} (hm : m < p) : ((m ! : ℕ) : ZMod p) ≠ 0 := fz_ne_zero (p := p) hm

lemma rho_Cs_last (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) :
    ρ (Cs p (r6 n p) (r2 n p) (bflag n p (p - 1)) (eflag n p (p - 1)) (p - 1)) =
      ((((A2 ! : ℕ) : ZMod p)) / ((((p - 1) ! : ℕ) : ZMod p) * (((A2 + 1) ! : ℕ) : ZMod p))) ^ 2 *
        ((((2 * n - 1) ! : ℕ) : ZMod p) / ((((p - 1) ! : ℕ) : ZMod p) * (((2 * n) ! : ℕ) : ZMod p))) ^ 3 := by
  obtain ⟨hb, he⟩ := flags_D h5 ha hA hA2 (show a ≤ p - 1 by omega) (show p - 1 < p by omega)
  rw [hb, he, r6_band h5 ha hA hA2 h3n, band_r2 (band_h1 ha hA hA2) h3n]
  have e1 : A2 + 1 * p - (p - 1) = A2 + 1 := by omega
  have e2 : 2 * n + (p - 1) - 1 * p = 2 * n - 1 := by omega
  unfold Cs Bw Bwi
  rw [e1, e2]
  simp only [map_mul, map_pow, rho_fact, rho_fact_inv (show p - 1 < p by omega),
    rho_fact_inv (show A2 + 1 < p by omega), rho_fact_inv (show 2 * n < p by omega)]
  simp only [div_eq_mul_inv]
  ring

theorem Kz_rho (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (Kz : ZMod (p ^ 2))
    (hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s)) :
    ρ Kz = (((A2 ! : ℕ) : ZMod p)) ^ 2 / (((2 * n) ! : ℕ) : ZMod p) ^ 3 := by
  have h1 := band_h1 ha hA hA2
  have hs : p - 1 ∈ Dw n p := (D_iff h5 ha hA hA2).2 ⟨by omega, by omega⟩
  have hKs := congrArg ρ (hK (p - 1) hs)
  unfold fR at hKs
  rw [map_mul, map_mul, map_mul, jetp_cast_one, mul_one, rho_Cs_last h5 ha hA hA2 h3n] at hKs
  have hPe := congrArg ρ (Pe_gexp_band h5 h1 h3n ha hA hA2 (p - 1))
  have hQ := congrArg ρ (Qhat_band h5 h1 h3n ha hA hA2 hs)
  simp only [map_mul, map_pow] at hPe hQ
  rw [rho_Jt_last h5 (show A2 + 1 ≤ p - 1 by omega), rho_Jt_last h5 (show a ≤ p - 1 by omega),
    rho_Jt_last h5 (show 0 ≤ p - 1 by omega)] at hPe
  rw [rho_Jt_last h5 (show a ≤ p - 1 by omega), rho_Jt_last h5 (show 0 ≤ p - 1 by omega)] at hQ
  have ea : p - 1 - a = 2 * n - 1 := by omega
  have e0 : p - 1 - 0 = p - 1 := by omega
  rw [ea, e0] at hPe hQ
  have hBF : ((((A2 + 1) ! : ℕ) : ZMod p)) ^ 2 * (((p - 1 - (A2 + 1)) ! : ℕ) : ZMod p) ^ 2 = 1 := by
    have := fact_reflect (p := p) (A2 + 1) (by omega)
    rw [← mul_pow, this, ← pow_mul]
    rw [show (A2 + 1 + 1) * 2 = 2 * (A2 + 2) by ring, pow_mul]
    simp
  refine kz_alg (A := (((A2 ! : ℕ) : ZMod p))) (B := (((A2 + 1) ! : ℕ) : ZMod p))
    (Fv := (((p - 1 - (A2 + 1)) ! : ℕ) : ZMod p)) (E := ((((2 * n - 1) ! : ℕ) : ZMod p)))
    (D := (((2 * n) ! : ℕ) : ZMod p)) (W := ((((p - 1) ! : ℕ) : ZMod p))) (Pe := ρ (Pe p (gexp n p 5) (p - 1))) (Qh := ρ (Qhat n p 5 (p - 1)))
    (Cs := ((((A2 ! : ℕ) : ZMod p)) / ((((p - 1) ! : ℕ) : ZMod p) * (((A2 + 1) ! : ℕ) : ZMod p))) ^ 2 *
        ((((2 * n - 1) ! : ℕ) : ZMod p) / ((((p - 1) ! : ℕ) : ZMod p) * (((2 * n) ! : ℕ) : ZMod p))) ^ 3)
    (dn_fz_ne (by omega))
    (dn_fz_ne (by omega)) (dn_fz_ne (by omega)) (dn_fz_ne (by omega)) (dn_fz_ne (by omega)) ?_ ?_ rfl ?_ hBF
  · exact hPe
  · exact hQ
  · exact hKs

lemma rho_val (x : ZMod (p ^ 2)) : (((x.val : ℕ) : ℤ) : ZMod p) = ρ x := by
  have h1 : ρ x = ((x.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val x]
    rw [map_natCast]
  rw [h1]; simp

lemma kap_D (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) :
    ((kapZ n p 1 1 1 : ℤ) : ZMod p) = -32 := by
  unfold kapZ
  rw [rho_val, band_q6 h1 h2, band_q2 h1 h2]
  have hW : (((p - 1) ! : ℕ) : ZMod p) = -1 := CatalanCore.Content.wilson p
  have hWi : ρ ((((p - 1) ! : ℕ) : ZMod (p ^ 2))⁻¹) = -1 := by
    rw [rho_fact_inv (by omega), hW]; norm_num
  have hW2 : ρ (((p - 1) ! : ℕ) : ZMod (p ^ 2)) = -1 := by rw [rho_fact, hW]
  unfold Kc Aw Awi
  simp only [map_mul, map_pow, map_add, map_one, hW2, hWi, rho_fact, map_natCast, ZMod.natCast_self, zero_mul,
    add_zero]
  rw [show (2 - 1 - 1 : ℕ) = 0 by norm_num, show (0 + 1 + 1 : ℕ) = 2 by norm_num]
  simp only [rho_fact_inv (show 1 < p by omega), rho_fact_inv (show 0 < p by omega)]
  norm_num [Nat.factorial]

end KzMain

end KzVal

/-! ### Part 6: assembly -/

section Assembly

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

lemma loc7 : (((7 : LocRing p)) : ℚ) = 7 := by
  have : (7 : LocRing p) = ((7 : ℕ) : LocRing p) := by norm_num
  rw [this, Subring.coe_natCast]; norm_num

lemma loc5 : (((5 : LocRing p)) : ℚ) = 5 := by
  have : (5 : LocRing p) = ((5 : ℕ) : LocRing p) := by norm_num
  rw [this, Subring.coe_natCast]; norm_num

lemma eval_map_neg (V : ℤ[X]) (s : ℕ) :
    (V.map (Int.castRingHom ℚ)).eval (-(s : ℚ)) = ((V.eval (-(s : ℤ)) : ℤ) : ℚ) := by
  have := Polynomial.eval_intCast_map (Int.castRingHom ℚ) V (-(s : ℤ))
  simpa using this

lemma Mmain_eq (V : ℤ[X]) :
    Mmain n p (V.map (Int.castRingHom ℚ)) =
      (p : ℚ) * (kapZ n p 1 1 1 : ℚ) *
        (-7 * ((∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ℚ) +
          5 * (p : ℚ) * (((∑ s ∈ Dw n p, cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) : ℤ) : ℚ) -
            ∑ s ∈ Dw n p, (cbarZ n p s : ℚ) * lam0 n p s * ((V.eval (-(s : ℤ)) : ℤ) : ℚ))) := by
  unfold Mmain
  have e : ∀ s ∈ Dw n p, (p : ℚ) * (cbarZ n p s : ℚ) * (kapZ n p 1 1 1 : ℚ) *
      (-7 * (V.map (Int.castRingHom ℚ)).eval (-(s : ℚ)) +
        5 * (p : ℚ) * ((V.map (Int.castRingHom ℚ)).derivative.eval (-(s : ℚ)) -
          lam0 n p s * (V.map (Int.castRingHom ℚ)).eval (-(s : ℚ)))) =
      (p : ℚ) * (kapZ n p 1 1 1 : ℚ) *
        (-7 * ((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ℚ) +
          5 * (p : ℚ) * (((cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) : ℤ) : ℚ) -
            (cbarZ n p s : ℚ) * lam0 n p s * ((V.eval (-(s : ℤ)) : ℤ) : ℚ))) := by
    intro s _
    rw [Polynomial.derivative_map, eval_map_neg V s, eval_map_neg (Polynomial.derivative V) s]
    push_cast
    ring
  rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  push_cast
  ring

section OwnAssembly

variable {a A2 : ℕ}

include hp in
lemma a_odd (h5 : 5 ≤ p) (ha : a + 2 * n = p) : a % 2 = 1 := by
  rcases hp.out.eq_two_or_odd with h | h
  · omega
  · omega

lemma U_int (V : ℤ[X]) :
    ∃ u : LocRing p, (u : ℚ) = ∑ s ∈ Dw n p, (cbarZ n p s : ℚ) * lam0 n p s * ((V.eval (-(s : ℤ)) : ℤ) : ℚ) := by
  refine ⟨∑ s ∈ Dw n p, lam0L n p s * ((cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : LocRing p), ?_⟩
  push_cast
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [lam0L_val (mem_Dw.1 hs).1]
  ring

/-- the exact decomposition of the `b`-channel window sum (any `V ∈ ℤ[X]`). -/
theorem dwin_decomp (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (V : ℤ[X]) :
    ∃ z : LocRing p, dWinB n p (V.map (Int.castRingHom ℚ)) =
      (p : ℚ) * (kapZ n p 1 1 1 : ℚ) *
        (-7 * ((∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) : ℤ) : ℚ) +
          5 * (p : ℚ) * (((∑ s ∈ Dw n p, cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) : ℤ) : ℚ) -
            ∑ s ∈ Dw n p, (cbarZ n p s : ℚ) * lam0 n p s * ((V.eval (-(s : ℤ)) : ℤ) : ℚ))) +
        (p : ℚ) ^ 3 * (z : ℚ) := by
  have hm := dwin_main h5 ha hA hA2 h3n V
  refine ⟨⟨_, hm⟩, ?_⟩
  rw [← Mmain_eq]
  show _ = _ + (p : ℚ) ^ 3 * ((p : ℚ) ^ (-(3 : ℤ)) * _)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [← mul_assoc, show (p : ℚ) ^ 3 = (p : ℚ) ^ (3 : ℤ) by norm_cast, ← zpow_add₀ hp0]
  norm_num

/-- **D-window value, own pair with `m = 6` (A) / `4` (C)** (`g₀ = 1`).  `thr = 2`: the `b`-channel window sum is
`p² y` with `ȳ = K₀ P_r(r)³ ((-7)(3 - 4δ) + 5(m - (2δ + 3)))`, `δ = [r ≤ A₂]`. -/
theorem dwin_own_g1 (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) {r i i' : ℕ} (hr : r < a) (hrp : r < p) (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) (hg : 1 + 2 * mu n p r + 2 = 3 + (i + i')) :
    ∃ y : LocRing p,
      dWinB n p (((ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i, hi⟩⟩ : FIdx n p 5)) *
        ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i', hi'⟩⟩ : FIdx n p 5)).map (Int.castRingHom ℚ)) =
        (p : ℚ) ^ 2 * (y : ℚ) ∧
      redQ p y = B83.K0B p n A2 * B83.PrB p a r ^ 3 *
        ((-7) * (3 - 4 * (if r < A2 + 1 then (1 : ZMod p) else 0)) +
          5 * (((i + i' : ℕ) : ZMod p) - (2 * (if r < A2 + 1 then (1 : ZMod p) else 0) + 3))) := by
  have h1 := band_h1 ha hA hA2
  have hR : Rng n p := band_rng h1 h3n
  have hodd := a_odd h5 ha
  have hrD : r ∉ Dw n p := not_D_of_lt h5 ha hA hA2 hr
  have hrW : sig n p r ≠ 5 := sig_ne5_of_notD hrp hrD
  have hpar : (lam n p - ((5 : ℕ) : ℤ)) % 2 = 0 := by rw [band_lam h1 h3n]; norm_num
  obtain ⟨Kz, -, hKall⟩ := lemmaR_p2 hR 5 hpar
  have hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s) :=
    fun s hs => hKall s (mem_Dw.1 hs).1 (mem_Dw.1 hs).2
  have hμ : ∀ r' ∈ Dw n p, mu n p r' = 0 :=
    fun r' hr' => band_mu h1 h3n r' (mem_Dw.1 hr').1 (mem_Dw.1 hr').2
  have hGE := gOwn_identity h1 h3n hrp hrW hi hi' hg
  have hHE := hOwn_identity h1 h3n hrp hrW hi hi' (le_refl 1) hg
  have hGdeg := gOwn_deg h1 h3n hrp hrW 1
  have hHdeg := hOwn_deg h1 h3n hrp hrW 1 (i + i')
  have hGd : (gOwn n p r 1).natDegree ≤ p - 4 := by omega
  have hHd : (hOwn n p r 1 (i + i')).natDegree ≤ p - 2 := by omega
  have hGv : ∀ m, m < p → m ∉ Dw n p → (gOwn n p r 1).eval (m : ZMod (p ^ 2)) = 0 :=
    fun m hm hD => gOwn_van h1 h3n hm hD (Or.inr le_rfl)
  have hHv : ∀ m, m < p → m ∉ Dw n p → m ≠ r → (hOwn n p r 1 (i + i')).eval (m : ZMod (p ^ 2)) = 0 :=
    fun m hm hD hmr => hOwn_van h1 h3n hm hD hmr
  have hG' : ∀ j, j < a → j ≠ r → ((gOwn n p r 1).map ρ).derivative.eval ((j : ℕ) : ZMod p) = 0 := by
    intro j hj hjr
    rw [Polynomial.derivative_map, rho_eval_map, gOwn_deriv_van h1 h3n (by omega) (not_D_of_lt h5 ha hA hA2 hj) hjr,
      map_zero]
  have hgd : ((gOwn n p r 1).map ρ).derivative.eval ((r : ℕ) : ZMod p) = B83.PrB p a r ^ 3 := by
    rw [Polynomial.derivative_map, rho_eval_map, gOwn_deriv_r1 hrp, map_neg, map_mul,
      rho_sgn h1 h3n ha hodd, rho_P3r h5 h1 h3n ha hA hA2 hodd hr]
    ring
  have hHr : ρ ((hOwn n p r 1 (i + i')).eval (r : ZMod (p ^ 2))) = -(((i + i' : ℕ) : ZMod p) * B83.PrB p a r ^ 3) := by
    rw [hOwn_eval_r1 hrp, map_mul, map_mul, rho_sgn h1 h3n ha hodd, rho_P3r h5 h1 h3n ha hA hA2 hodd hr, map_natCast]
    have : exOwn n p r (i + i') r = i + i' := by unfold exOwn; rw [if_neg hrW, if_pos rfl]
    rw [this]; ring
  set V := (ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i, hi⟩⟩ : FIdx n p 5)) *
    ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i', hi'⟩⟩ : FIdx n p 5) with hV
  obtain ⟨S₁, hS, hS₁⟩ := S_value h5 ha hA hA2 h3n Kz hK hμ V (gOwn n p r 1) hGE hGd hGv r hG'
  have hT := S_first Kz hK hμ (Polynomial.derivative V) (hOwn n p r 1 (i + i')) hHE hHd r hrp hrD hHv
  obtain ⟨u, hu, hredu⟩ := U_value h5 ha hA hA2 h3n Kz hK hμ V (gOwn n p r 1) hGE hGd hGv r hG'
  obtain ⟨z, hz⟩ := dwin_decomp h5 ha hA hA2 h3n V
  set T : ℤ := ∑ s ∈ Dw n p, cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) with hTdef
  refine ⟨(kapZ n p 1 1 1 : LocRing p) * (((-7 : ℤ) : LocRing p) * (S₁ : LocRing p) + ((5 : ℤ) : LocRing p) * ((T : LocRing p) - u)) + (p : LocRing p) * z, ?_, ?_⟩
  · rw [hz, hS, ← hu]
    push_cast
    rw [loc7, loc5]
    ring
  · have hkap := kap_D h5 h1 h3n
    have hKz := Kz_rho h5 ha hA hA2 h3n Kz hK
    have hK0 : B83.K0B p n A2 = ((kapZ n p 1 1 1 : ℤ) : ZMod p) * ρ Kz := by
      rw [hkap, hKz]
      unfold B83.K0B fz
      rw [CatalanCore.Content.wilson p]
      field_simp
    simp only [map_add, map_mul, map_sub, map_intCast, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
    rw [hredu, hS₁, hT, hgd, hHr, hK0]
    push_cast
    split_ifs with hrA <;> ring

/-- **D-window value, own pair with `m = 5` (A) / `3` (C)** (`g₀ = 0`).  `thr = 1`: the `b`-channel window sum is
`p y` with `ȳ = -7 K₀ P_r(r)³`. -/
theorem dwin_own_g0 (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) {r i i' : ℕ} (hr : r < a) (hrp : r < p) (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) (hg : 0 + 2 * mu n p r + 2 = 3 + (i + i')) :
    ∃ y : LocRing p,
      dWinB n p (((ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i, hi⟩⟩ : FIdx n p 5)) *
        ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i', hi'⟩⟩ : FIdx n p 5)).map (Int.castRingHom ℚ)) =
        (p : ℚ) * (y : ℚ) ∧
      redQ p y = -7 * (B83.K0B p n A2 * B83.PrB p a r ^ 3) := by
  have h1 := band_h1 ha hA hA2
  have hR : Rng n p := band_rng h1 h3n
  have hodd := a_odd h5 ha
  have hrD : r ∉ Dw n p := not_D_of_lt h5 ha hA hA2 hr
  have hrW : sig n p r ≠ 5 := sig_ne5_of_notD hrp hrD
  have hpar : (lam n p - ((5 : ℕ) : ℤ)) % 2 = 0 := by rw [band_lam h1 h3n]; norm_num
  obtain ⟨Kz, -, hKall⟩ := lemmaR_p2 hR 5 hpar
  have hK : ∀ s ∈ Dw n p, fR n p 5 s = Kz * Qhat n p 5 s * jetp p (xiR n p s) :=
    fun s hs => hKall s (mem_Dw.1 hs).1 (mem_Dw.1 hs).2
  have hμ : ∀ r' ∈ Dw n p, mu n p r' = 0 :=
    fun r' hr' => band_mu h1 h3n r' (mem_Dw.1 hr').1 (mem_Dw.1 hr').2
  have hGE := gOwn_identity h1 h3n hrp hrW hi hi' hg
  have hGdeg := gOwn_deg h1 h3n hrp hrW 0
  have hGd : (gOwn n p r 0).natDegree ≤ p - 2 := by omega
  have hGv : ∀ m, m < p → m ∉ Dw n p → m ≠ r → (gOwn n p r 0).eval (m : ZMod (p ^ 2)) = 0 :=
    fun m hm hD hmr => gOwn_van h1 h3n hm hD (Or.inl hmr)
  set V := (ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i, hi⟩⟩ : FIdx n p 5)) *
    ExZ n p 5 (Sum.inl ⟨⟨r, hrp⟩, ⟨i', hi'⟩⟩ : FIdx n p 5) with hV
  have hS := S_first Kz hK hμ V (gOwn n p r 0) hGE hGd r hrp hrD hGv
  obtain ⟨u, hu⟩ := U_int (n := n) (p := p) V
  obtain ⟨z, hz⟩ := dwin_decomp h5 ha hA hA2 h3n V
  set T : ℤ := ∑ s ∈ Dw n p, cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) with hTdef
  set S : ℤ := ∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) with hSdef
  refine ⟨(kapZ n p 1 1 1 : LocRing p) * (((-7 : ℤ) : LocRing p) * (S : LocRing p) +
    ((5 : ℤ) : LocRing p) * (p : LocRing p) * ((T : LocRing p) - u)) + (p : LocRing p) ^ 2 * z, ?_, ?_⟩
  · rw [hz, ← hu]
    push_cast
    rw [loc7, loc5]
    ring
  · have hkap := kap_D h5 h1 h3n
    have hKz := Kz_rho h5 ha hA hA2 h3n Kz hK
    have hK0 : B83.K0B p n A2 = ((kapZ n p 1 1 1 : ℤ) : ZMod p) * ρ Kz := by
      rw [hkap, hKz]
      unfold B83.K0B fz
      rw [CatalanCore.Content.wilson p]
      field_simp
    simp only [map_add, map_mul, map_pow, map_sub, map_intCast, map_natCast, ZMod.natCast_self]
    rw [hS, gOwn_eval_r0 hrp, map_mul, rho_sgn h1 h3n ha hodd, rho_P3r h5 h1 h3n ha hA hA2 hodd hr, hK0]
    ring

end OwnAssembly

end Assembly

/-! ### Part 7: the D-node exact values of the `A`- and `C`-blocks -/

section Final

variable {n p : ℕ} [hp : Fact p.Prime]

local notation "ρ" => ZMod.castHom (dvd_pow_self p (two_ne_zero)) (ZMod p)

/-- the own element `e_{r,i}` of the E2 family (`r < p`, `i < μ'_r`). -/
def ownIx (n p : ℕ) {r i : ℕ} (hrp : r < p) (hi : i < mF n p 5 r) : FIdx n p 5 :=
  Sum.inl ⟨⟨r, hrp⟩, ⟨i, hi⟩⟩

section

variable {a A2 : ℕ}

/-- the window contribution is `p` times an `ℤ_(p)`-element, for every `V`. -/
theorem dwin_low (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) (V : ℤ[X]) (thr : ℤ) (hthr : thr ≤ 0) :
    ∃ y : LocRing p, dWinB n p (V.map (Int.castRingHom ℚ)) = (p : ℚ) ^ thr * (y : ℚ) ∧ redQ p y = 0 := by
  obtain ⟨u, hu⟩ := U_int (n := n) (p := p) V
  obtain ⟨z, hz⟩ := dwin_decomp h5 ha hA hA2 h3n V
  set T : ℤ := ∑ s ∈ Dw n p, cbarZ n p s * (Polynomial.derivative V).eval (-(s : ℤ)) with hTdef
  set S : ℤ := ∑ s ∈ Dw n p, cbarZ n p s * V.eval (-(s : ℤ)) with hSdef
  set y₀ : LocRing p := (kapZ n p 1 1 1 : LocRing p) * (((-7 : ℤ) : LocRing p) * (S : LocRing p) +
    ((5 : ℤ) : LocRing p) * (p : LocRing p) * ((T : LocRing p) - u)) + (p : LocRing p) ^ 2 * z with hy0
  have hk : 1 - thr = (((1 - thr).toNat : ℕ) : ℤ) := by omega
  refine ⟨(p : LocRing p) ^ (1 - thr).toNat * y₀, ?_, ?_⟩
  · have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hd : dWinB n p (V.map (Int.castRingHom ℚ)) = (p : ℚ) * (y₀ : ℚ) := by
      rw [hz, ← hu, hy0]
      push_cast
      rw [loc7, loc5]
      ring
    have hpow : (p : ℚ) ^ thr * (p : ℚ) ^ (1 - thr).toNat = p := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]
      have : thr + (((1 - thr).toNat : ℕ) : ℤ) = 1 := by omega
      rw [this, zpow_one]
    rw [hd]
    push_cast
    rw [← mul_assoc, hpow]
  · rw [map_mul, map_pow, map_natCast, ZMod.natCast_self, zero_pow (by omega), zero_mul]

lemma pot2F_own (n p : ℕ) {r i : ℕ} (hrp : r < p) (hi : i < mF n p 5 r) :
    pot2F n p 5 (ownIx n p hrp hi) = 2 * (i : ℤ) - 4 + (sig n p r : ℤ) := by
  simp [ownIx, pot2F]

/-- **The D-node values of the `A`-block (Lemma A, `m = 5, 6`).**  For `r ≤ A₂` and the pair `e_{r,i} e_{r,i'}`,
`thr = i + i' - 4`: the `b`-channel sum over the window `D` is `p^{thr} y` with `ȳ = corrA(i + i') · wtB`
(`corrA 5 = -7·32`, `corrA 6 = 12·32`, `0` otherwise). -/
theorem dnode_A (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) {r i i' : ℕ} (hr : r ≤ A2) (hrp : r < p) (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) :
    ∃ y : LocRing p,
      dWinB n p (((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')).map (Int.castRingHom ℚ)) =
        (p : ℚ) ^ ((pot2F n p 5 (ownIx n p hrp hi) + pot2F n p 5 (ownIx n p hrp hi') + 1) / 2) * (y : ℚ) ∧
      redQ p y = (B83.corrA (i + i') : ZMod p) * B83.wtB p n A2 a 0 r := by
  have h1 := band_h1 ha hA hA2
  have hodd := a_odd h5 ha
  have hcls : sig n p r = 0 ∧ mu n p r = 3 := by
    rcases dn_sigmu h1 h3n r hrp with ⟨h1', h2', -⟩ | ⟨-, -, h3', -⟩ | ⟨h1', -, h3'⟩
    · exact ⟨h1', h2'⟩
    · omega
    · omega
  obtain ⟨hsig, hmu⟩ := hcls
  have hmF : mF n p 5 r = 4 := by rw [(dn_mF h1 h3n r hrp).2 (by omega), hmu]
  have hthr : (pot2F n p 5 (ownIx n p hrp hi) + pot2F n p 5 (ownIx n p hrp hi') + 1) / 2 =
      (i : ℤ) + i' - 4 := by
    rw [pot2F_own, pot2F_own, hsig]; push_cast; omega
  have hi4 : i < 4 := hmF ▸ hi
  have hi4' : i' < 4 := hmF ▸ hi'
  rw [hthr]
  by_cases hm5 : i + i' = 5
  · have hg : 0 + 2 * mu n p r + 2 = 3 + (i + i') := by omega
    obtain ⟨y, h1', h2⟩ := dwin_own_g0 h5 ha hA hA2 h3n (by omega) hrp hi hi' hg
    have e : (i : ℤ) + i' - 4 = 1 := by omega
    refine ⟨y, ?_, ?_⟩
    · rw [e, zpow_one]; exact h1'
    · rw [h2, hm5]
      unfold B83.wtB B83.corrA
      rw [if_pos rfl]
      have := B83.u83_A h5 ha hA hA2 hodd hr
      push_cast
      rw [mul_comm (-7 : ZMod p), this] ; ring
  by_cases hm6 : i + i' = 6
  · have hg : 1 + 2 * mu n p r + 2 = 3 + (i + i') := by omega
    obtain ⟨y, h1', h2⟩ := dwin_own_g1 h5 ha hA hA2 h3n (by omega) hrp hi hi' hg
    have e : (i : ℤ) + i' - 4 = 2 := by omega
    refine ⟨y, ?_, ?_⟩
    · rw [e]; exact_mod_cast h1'
    · rw [if_pos (show r < A2 + 1 by omega)] at h2
      have key := B83.u83_A h5 ha hA hA2 hodd hr
      rw [h2, hm6]
      unfold B83.wtB B83.corrA
      norm_num
      linear_combination 12 * key
  · obtain ⟨y, h1', h2⟩ := dwin_low h5 ha hA hA2 h3n
      ((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')) ((i : ℤ) + i' - 4) (by omega)
    refine ⟨y, h1', ?_⟩
    rw [h2]
    unfold B83.corrA
    rw [if_neg hm5, if_neg hm6]
    simp

/-- **The D-node values of the `C`-block (Lemma C, `m = 3, 4`).**  For `A₂ < r < a`, `thr = i + i' - 2`:
the window sum is `p^{thr} y` with `ȳ = corrC(i + i') · wtB` (`corrC 3 = -7·8`, `corrC 4 = -16·8`). -/
theorem dnode_C (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) {r i i' : ℕ} (hr1 : A2 < r) (hr2 : r < a) (hrp : r < p) (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) :
    ∃ y : LocRing p,
      dWinB n p (((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')).map (Int.castRingHom ℚ)) =
        (p : ℚ) ^ ((pot2F n p 5 (ownIx n p hrp hi) + pot2F n p 5 (ownIx n p hrp hi') + 1) / 2) * (y : ℚ) ∧
      redQ p y = (B83.corrC (i + i') : ZMod p) * B83.wtB p n A2 a 1 r := by
  have h1 := band_h1 ha hA hA2
  have hodd := a_odd h5 ha
  have hcls : sig n p r = 2 ∧ mu n p r = 2 := by
    rcases dn_sigmu h1 h3n r hrp with ⟨-, -, h3'⟩ | ⟨h1', h2', -⟩ | ⟨h1', -, h3'⟩
    · omega
    · exact ⟨h1', h2'⟩
    · omega
  obtain ⟨hsig, hmu⟩ := hcls
  have hmF : mF n p 5 r = 3 := by rw [(dn_mF h1 h3n r hrp).2 (by omega), hmu]
  have hthr : (pot2F n p 5 (ownIx n p hrp hi) + pot2F n p 5 (ownIx n p hrp hi') + 1) / 2 =
      (i : ℤ) + i' - 2 := by
    rw [pot2F_own, pot2F_own, hsig]; push_cast; omega
  have hi3 : i < 3 := hmF ▸ hi
  have hi3' : i' < 3 := hmF ▸ hi'
  rw [hthr]
  by_cases hm3 : i + i' = 3
  · have hg : 0 + 2 * mu n p r + 2 = 3 + (i + i') := by omega
    obtain ⟨y, h1', h2⟩ := dwin_own_g0 h5 ha hA hA2 h3n hr2 hrp hi hi' hg
    have e : (i : ℤ) + i' - 2 = 1 := by omega
    refine ⟨y, ?_, ?_⟩
    · rw [e, zpow_one]; exact h1'
    · have key := B83.u83_C h5 ha hA hodd hr1 hr2
      rw [h2, hm3]
      unfold B83.wtB B83.corrC
      norm_num
      linear_combination 7 * key
  by_cases hm4 : i + i' = 4
  · have hg : 1 + 2 * mu n p r + 2 = 3 + (i + i') := by omega
    obtain ⟨y, h1', h2⟩ := dwin_own_g1 h5 ha hA hA2 h3n hr2 hrp hi hi' hg
    have e : (i : ℤ) + i' - 2 = 2 := by omega
    refine ⟨y, ?_, ?_⟩
    · rw [e]; exact_mod_cast h1'
    · rw [if_neg (show ¬ r < A2 + 1 by omega)] at h2
      have key := B83.u83_C h5 ha hA hodd hr1 hr2
      rw [h2, hm4]
      unfold B83.wtB B83.corrC
      norm_num
      linear_combination 16 * key
  · obtain ⟨y, h1', h2⟩ := dwin_low h5 ha hA hA2 h3n
      ((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')) ((i : ℤ) + i' - 2) (by omega)
    refine ⟨y, h1', ?_⟩
    rw [h2]
    unfold B83.corrC
    rw [if_neg hm3, if_neg hm4]
    simp

end

end Final

/-! ### Part 8: the interface -/

section Interface

variable {n p : ℕ} [hp : Fact p.Prime]

theorem entB_eq_sum (n : ℕ) (F : ℚ[X]) : entB n F = ∑ k ∈ range (6 * n + 1), ndB n k F := rfl

/-- **Split of the `b`-entry into the window `D` and the other residues.** -/
theorem entB_split (h : Rng n p) (F : ℚ[X]) :
    entB n F = dWinB n p F +
      ∑ s ∈ (range p).filter (fun s => ¬ sig n p s = 5), ∑ l ∈ range (Lc n p s + 1), ndB n (s + l * p) F := by
  rw [entB_eq_sum, sum_nodes_fiber h (fun k => ndB n k F)]
  rw [← Finset.sum_filter_add_sum_filter_not (range p) (fun s => sig n p s = 5)]
  rfl

section Bridge

variable {a A2 : ℕ}

/-- `Ψ_r(X) = ∏_{t < a, t ≠ r} (X + t)^{μ_t}` (`μ_t = 4` on `A`, `3` on `C`). -/
def PsiPolyD (A2 a r : ℕ) : ℚ[X] := ∏ t ∈ (range a).erase r, (X + C (t : ℚ)) ^ B83.muB A2 t

/-- the basis element `e_{r,i} = (X + r)^i Ψ_r`. -/
def eBD (A2 a r i : ℕ) : ℚ[X] := (X + C (r : ℚ)) ^ i * PsiPolyD A2 a r

/-- **Bridge to the explicit form of the pair.** -/
theorem ExZ_pair_eq (h5 : 5 ≤ p) (ha : a + 2 * n = p) (hA : A2 + 2 * p = 6 * n) (hA2 : A2 < a)
    (h3n : p + 1 < 3 * n) {r i i' : ℕ} (hr : r < a) (hrp : r < p) (hi : i < mF n p 5 r)
    (hi' : i' < mF n p 5 r) :
    ((ExZ n p 5 (ownIx n p hrp hi)) * ExZ n p 5 (ownIx n p hrp hi')).map (Int.castRingHom ℚ) =
      eBD A2 a r i * eBD A2 a r i' := by
  have h1 := band_h1 ha hA hA2
  have hrD : r ∉ Dw n p := not_D_of_lt h5 ha hA hA2 hr
  have hrW : sig n p r ≠ 5 := sig_ne5_of_notD hrp hrD
  unfold ownIx
  rw [ExZ_own hrp hi hi']
  have hap : a ≤ p := by omega
  -- restrict to `range a`
  have hz : ∀ q ∈ range p, q ∉ range a →
      (Polynomial.X + Polynomial.C (q : ℤ)) ^ exOwn n p r (i + i') q = 1 := by
    intro q hq hqa
    have hqp := Finset.mem_range.1 hq
    have hqa' : ¬ q < a := fun h => hqa (Finset.mem_range.2 h)
    have hs5 : sig n p q = 5 := sig_D h5 ha hA hA2 (by omega) hqp
    unfold exOwn; rw [if_pos hs5, pow_zero]
  rw [← Finset.prod_subset (Finset.range_subset_range.2 hap) hz,
    ← Finset.mul_prod_erase (range a) _ (Finset.mem_range.2 hr)]
  have hEr : exOwn n p r (i + i') r = i + i' := by unfold exOwn; rw [if_neg hrW, if_pos rfl]
  have hEq : ∀ q ∈ (range a).erase r, exOwn n p r (i + i') q = 2 * B83.muB A2 q := by
    intro q hq
    have hqa := Finset.mem_range.1 (Finset.mem_erase.1 hq).2
    have hqr := (Finset.mem_erase.1 hq).1
    have hqp : q < p := by omega
    have hqW := sig_ne5_of_notD hqp (not_D_of_lt h5 ha hA hA2 hqa)
    unfold exOwn
    rw [if_neg hqW, if_neg hqr, (dn_mF h1 h3n q hqp).2 hqW]
    rcases dn_sigmu h1 h3n q hqp with ⟨-, hm, hc⟩ | ⟨-, hm, hc, -⟩ | ⟨hg, -, -⟩
    · rw [hm, B83.muB_le (by omega)]
    · rw [hm, B83.muB_gt (by omega)]
    · exact absurd hg hqW
  rw [Finset.prod_congr rfl (fun q hq => by rw [hEq q hq])]
  unfold eBD PsiPolyD
  rw [hEr, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_prod]
  simp only [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  rw [pow_add]
  have : ∏ t ∈ (range a).erase r, ((Polynomial.X : ℚ[X]) + Polynomial.C ((t : ℤ) : ℚ)) ^ (2 * B83.muB A2 t) =
      (∏ t ∈ (range a).erase r, (Polynomial.X + Polynomial.C (t : ℚ)) ^ B83.muB A2 t) ^ 2 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [pow_mul']
    simp
  simp only [Int.coe_castRingHom, Int.cast_natCast] at this ⊢
  rw [this]
  ring

end Bridge

end Interface

end

end CatalanCore.Lai

#print axioms CatalanCore.Lai.dwin_main
#print axioms CatalanCore.Lai.Kz_rho
#print axioms CatalanCore.Lai.kap_D
#print axioms CatalanCore.Lai.dwin_own_g0
#print axioms CatalanCore.Lai.dwin_own_g1
#print axioms CatalanCore.Lai.dnode_A
#print axioms CatalanCore.Lai.dnode_C
#print axioms CatalanCore.Lai.ExZ_pair_eq
#print axioms CatalanCore.Lai.entB_split
