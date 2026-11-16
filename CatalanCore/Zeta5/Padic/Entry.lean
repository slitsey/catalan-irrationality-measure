module

public import CatalanCore.Zeta5.Padic.Pair
public import CatalanCore.Zeta5.Parity.Centred

@[expose] public section

/-!
# ZC06(b), part 6: the entries of the centred Gram matrix (steps E1, E3)

For rows `s, t` of the centred class basis the entry `μ_X(D_N⁶ Ẽ_s Ẽ_t)` is `τ_X(A_st / Π_K)` with
`A_st = pull K (tpolS S_st)` (`entA`).

* `entF_hAloc`, `entF_neg`, `entF_sub`: the local valuations `e_st(c)` (E1).
* `entry_lead`: theorem (A) for the entry: `p^{4-β} μ_X(...) = C z - C y X` with `z` integral,
  `z mod p = ∑_{c<p} locSymb(c)` and `v_p(y) ≥ 5`.
* `locN_entry`: the closed local numerator (E3) at a class representative `1 ≤ a ≤ m`:
  `ā = (-1)^K a⁵ ū_N⁶ Π_s Π_t · B_{I^N_a}⁶ · (-2a z)^{ν_s(a)+ν_t(a)}`.
-/

open Finset Polynomial

namespace Apery

section entry
variable {p : ℕ} [hp : Fact p.Prime]

/-- the shifted roots of the entry numerator `D_N⁶ Ẽ_s Ẽ_t`. -/
noncomputable def entS (p N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) : Multiset (ℤ × ℤ) :=
  6 • ((Icc 1 N).val.map fun j : ℕ => (((j : ℕ) : ℤ), (0 : ℤ))) +
    cShifts p L s.1 s.2 + cShifts p L t.1 t.2

/-- the pulled-back numerator `A_st`. -/
noncomputable def entA (p K N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) : ℚ[X] :=
  pull K (tpolS (entS p N L s t))

/-- the local valuation `e_st(c)`. -/
noncomputable def entF (p N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (c : ZMod p) : ℕ :=
  (if c = 0 then 5 else 0) + ((entS p N L s t).filter fun x => (x.1 : ZMod p) = c).card +
    ((entS p N L s t).filter fun x => (x.1 : ZMod p) = -c).card

lemma entS_fst (N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    (entS p N L s t).map Prod.fst = entryRoots N L s t := by
  rw [entS, Multiset.map_add, Multiset.map_add, Multiset.map_nsmul, Multiset.map_map,
    cShifts_fst, cShifts_fst]
  unfold entryRoots
  congr 2

lemma entS_dvd (N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    ∀ x ∈ entS p N L s t, (p : ℤ) ∣ x.2 := by
  intro x hx
  rw [entS, Multiset.mem_add, Multiset.mem_add] at hx
  rcases hx with (hx | hx) | hx
  · obtain ⟨y, _, rfl⟩ := Multiset.mem_of_mem_nsmul hx |> fun h => Multiset.mem_map.mp h
    exact dvd_zero _
  · exact cShifts_dvd p L _ _ x hx
  · exact cShifts_dvd p L _ _ x hx

lemma tpolS_entS (N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    tpolS (entS p N L s t) =
      D N ^ 6 * tpolS (cShifts p L s.1 s.2) * tpolS (cShifts p L t.1 t.2) := by
  rw [entS, tpolS_add, tpolS_add, tpolS_nsmul, D_eq_tpol, tpol_eq_tpolS, Multiset.map_map]
  rfl

/-- **E1 (a).** -/
lemma entF_hAloc (hp3 : 3 ≤ p) (K N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (x : ℤ) :
    GV p ((entA p K N L s t).comp (C (x : ℚ) + C (p : ℚ) * X)) (entF p N L s t (x : ZMod p)) := by
  have hcomp : (entA p K N L s t).comp (C (x : ℚ) + C (p : ℚ) * X) =
      C ((-1 : ℚ) ^ K) * (Gm p x) ^ 5 * (tpolS (entS p N L s t)).comp (-(Gm p x) ^ 2) := by
    simp only [entA, pull, mul_comp, C_comp, pow_comp, X_comp, comp_assoc, neg_comp]
    rfl
  rw [hcomp]
  have h1 : VG p ((-1 : ℚ) ^ K) 0 := by
    rcases neg_one_pow_eq_or ℚ K with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have h2 := GV_pow' (GV_Gm (p := p) x) 5
  have h3 := GV_tpolS_pull hp3 (entS p N L s t) (entS_dvd N L s t) x
  have := ((GV.C h1).mul h2).mul h3
  refine this.mono (le_of_eq ?_)
  simp only [entF]
  push_cast
  split_ifs <;> ring

/-- **E1 (b).** -/
lemma entF_neg (N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a))
    (c : ZMod p) : entF p N L s t (-c) = entF p N L s t c := by
  simp only [entF, neg_neg, neg_eq_zero]
  ring

/-- **E1 (c).** -/
lemma entF_sub (K N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a))
    (c : ZMod p) :
    (entF p N L s t c : ℚ) - (plc p (PlK K) c).card = classCount p K (entryRoots N L s t) c := by
  unfold classCount
  rw [← entS_fst (p := p) N L s t]
  simp only [entF, card_filter_fst]

lemma entA_odd (K N : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) :
    (entA p K N L s t).comp (-X) = -entA p K N L s t := by
  simp only [entA, pull, mul_comp, C_comp, pow_comp, X_comp, comp_assoc, neg_comp]
  rw [show ((-X : ℚ[X]) ^ 2) = X ^ 2 by ring]
  ring

/-- **Theorem (A) for the entries of the centred Gram matrix.** -/
theorem entry_lead (hp5 : 5 ≤ p) {m : ℕ} (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n))
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (k l : Fin (37 * n)) (β : ℤ)
    (hβ : ∀ c : ZMod p,
      (β : ℚ) ≤ classCount p (40 * n) (entryRoots (3 * n) L (e.symm k) (e.symm l)) c) :
    ∃ z y : ℚ, C ((p : ℚ) ^ (4 - β)) *
        μX (40 * n) (D (3 * n) ^ 6 * cclassF p L e k * cclassF p L e l) = C z - C y * X ∧
      VG p z 0 ∧
      (z : ZMod p) = ∑ c ∈ range p, locSymb p (entA p (40 * n) (3 * n) L (e.symm k) (e.symm l))
        (entF p (3 * n) L (e.symm k) (e.symm l)) (PlK (40 * n)) β c ∧
      VG p y 5 := by
  classical
  set s := e.symm k with hs
  set t := e.symm l with ht
  have hP : D (3 * n) ^ 6 * cclassF p L e k * cclassF p L e l = tpolS (entS p (3 * n) L s t) := by
    rw [tpolS_entS, cclassF_eq, cclassF_eq]
  have hScard : (entS p (3 * n) L s t).card ≤ 18 * n + 2 * (37 * n) := by
    rw [← Multiset.card_map Prod.fst, entS_fst]
    simp only [entryRoots, Multiset.card_add, Multiset.card_nsmul, Multiset.card_map,
      Finset.card_val, Nat.card_Icc]
    have h1 : (classRoots L s.1 s.2).card < 37 * n := classRoots_card_lt L hL e k
    have h2 : (classRoots L t.1 t.2).card < 37 * n := classRoots_card_lt L hL e l
    omega
  have hp3 : 3 ≤ p := by omega
  have hH : ∀ r ∈ PlK (40 * n), dd r < p ^ 2 := by
    intro r hr
    rw [PlK, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [dd_nat]; have := (Finset.mem_Icc.mp hj).2; omega
    · rw [dd_neg (Finset.mem_Icc.mp hj).1]; have := (Finset.mem_Icc.mp hj).2; omega
  have hdeg' : (entA p (40 * n) (3 * n) L s t).natDegree - (PlK (40 * n)).card + 1 < p ^ 2 := by
    have h1 := natDegree_pull_le (40 * n) (tpolS (entS p (3 * n) L s t))
    have h2 := natDegree_tpolS_le (entS p (3 * n) L s t)
    rw [card_PlK]
    unfold entA
    omega
  have hβ' : ∀ c : ZMod p, (β : ℚ) ≤
      (entF p (3 * n) L s t c : ℚ) - (plc p (PlK (40 * n)) c).card := fun c => by
    rw [entF_sub]; exact hβ c
  obtain ⟨h1, h2, h3⟩ := tauX_lead hp5 (entA p (40 * n) (3 * n) L s t) (entF p (3 * n) L s t)
    (entF_hAloc hp3 (40 * n) (3 * n) L s t) (PlK (40 * n)) hsep hH hdeg' β hβ'
  refine ⟨_, (p : ℚ) ^ (4 - β) * ∑ r ∈ PlK (40 * n), resP (entA p (40 * n) (3 * n) L s t)
    (PlK (40 * n)) r, ?_, h1, h2, ?_⟩
  · rw [hP, μX_eq_tauX, ← entA, tauX_eq, C_mul, C_mul]
    ring
  · have := (VG.primePow (p := p) (4 - β)).mul h3
    refine this.mono (le_of_eq ?_)
    push_cast; ring

/-! ### The closed local numerator (E3) -/

/-- the centred factor of the class `b`. -/
noncomputable def cfacQ (p : ℕ) (b : ℕ) : ℚ[X] := X + C ((b : ℚ) ^ 2 - (b : ℚ) * (p : ℚ))

lemma tpolS_cShifts {m : ℕ} (L : Fin (m + 1) → ℕ) (u : Σ a : Fin (m + 1), Fin (L a)) :
    tpolS (cShifts p L u.1 u.2) = ∏ b : Fin (m + 1), cfacQ p b ^ nu L u b := by
  unfold tpolS cShifts
  rw [Multiset.map_add, Multiset.prod_add, prod_map_sum_replicate', Multiset.map_replicate,
    Multiset.prod_replicate, ← Finset.mul_prod_erase Finset.univ
      (fun b : Fin (m + 1) => cfacQ p (b : ℕ) ^ nu L u b) (Finset.mem_univ u.1), mul_comm]
  congr 1
  · simp [cfacQ, nu]
  · refine Finset.prod_congr rfl fun b hb => ?_
    have hb' : b ≠ u.1 := Finset.ne_of_mem_erase hb
    simp [cfacQ, nu, hb']

lemma Gc_eq_Gm (a : ℕ) : Gc p a = Gm p (a : ℤ) := by simp [Gc, Gm]

/-- the own factor at its own residue. -/
lemma cfacQ_own (a : ℕ) :
    (cfacQ p a).comp (-(Gc p a) ^ 2) =
      C (p : ℚ) * (C (-(a : ℚ)) + C (-2 * (a : ℚ)) * X - C (p : ℚ) * X ^ 2) := by
  simp only [cfacQ, add_comp, X_comp, C_comp, Gc]
  simp only [C_sub, C_mul, C_pow, C_neg, C_ofNat]
  ring

lemma GV_own (a : ℕ) : GV p (C (-(a : ℚ)) + C (-2 * (a : ℚ)) * X - C (p : ℚ) * X ^ 2) 0 := by
  have h1 : VG p (-(a : ℚ)) 0 := (VG.natCast a).neg
  have h2 : VG p (-2 * (a : ℚ)) 0 := by
    have := VG.intCast (p := p) (-2 * (a : ℤ)); push_cast at this; exact this
  have h3 : GV p (C (p : ℚ) * X ^ 2) 0 := by
    have := (GV.C (VG.natCast (p := p) p)).mul (GV.X.mul GV.X)
    rw [← sq] at this; exact this.mono (by norm_num)
  exact ((GV.C h1).add (((GV.C h2).mul GV.X).mono (by norm_num))).sub h3

lemma redP_own (hp5 : 5 ≤ p) (a : ℕ) :
    redP p (C (-(a : ℚ)) + C (-2 * (a : ℚ)) * X - C (p : ℚ) * X ^ 2) =
      C (-2 * (a : ZMod p)) * zv := by
  have h1 : VG p (-(a : ℚ)) 0 := (VG.natCast a).neg
  have h2 : VG p (-2 * (a : ℚ)) 0 := by
    have := VG.intCast (p := p) (-2 * (a : ℤ)); push_cast at this; exact this
  have g1 : GV p (C (-(a : ℚ)) + C (-2 * (a : ℚ)) * X) 0 :=
    (GV.C h1).add (((GV.C h2).mul GV.X).mono (by norm_num))
  have g3 : GV p (C (p : ℚ) * X ^ 2) 0 := by
    have := (GV.C (VG.natCast (p := p) p)).mul (GV.X.mul GV.X)
    rw [← sq] at this; exact this.mono (by norm_num)
  have g2 : GV p (X ^ 2 : ℚ[X]) 0 := by
    have := GV.X.mul (GV.X (p := p)); rw [← sq] at this; exact this.mono (by norm_num)
  rw [redP_sub g1 g3, redP_add (GV.C h1) (((GV.C h2).mul GV.X).mono (by norm_num)), redP_C,
    redP_C_mul h2 GV.X, redP_X, redP_C_mul (VG.natCast p) g2, red_natCast, ZMod.natCast_self,
    C_0, zero_mul, sub_zero]
  have e1 : (((-(a : ℚ)) : ℚ) : ZMod p) = -(a : ZMod p) := by push_cast; ring
  have e2 : (((-2 * (a : ℚ)) : ℚ) : ZMod p) = -2 * (a : ZMod p) := by
    rw [show (-2 * (a : ℚ)) = (((-2 * (a : ℤ)) : ℤ) : ℚ) by push_cast; ring, red_intCast]
    push_cast; ring
  rw [e1, e2, zv]
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have : (-2 * (a : ZMod p)) * (1 / 2) = -(a : ZMod p) := by field_simp
  rw [mul_add, ← C_mul, this]
  ring

/-- a far factor at the residue `a`. -/
lemma GV_far (a b : ℕ) : GV p ((cfacQ p b).comp (-(Gc p a) ^ 2)) 0 := by
  have hG : GV p (Gc p a) 0 := by
    unfold Gc
    exact (GV.C (VG.natCast a)).add (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono (by norm_num))
  have h0 : VG p ((b : ℚ) ^ 2 - (b : ℚ) * (p : ℚ)) 0 := by
    have := VG.intCast (p := p) ((b : ℤ) ^ 2 - (b : ℤ) * (p : ℤ)); push_cast at this; exact this
  simp only [cfacQ, add_comp, X_comp, C_comp]
  have := (hG.mul hG).neg
  rw [← sq] at this
  exact (this.mono (by norm_num)).add (GV.C h0)

lemma redP_far (a b : ℕ) :
    redP p ((cfacQ p b).comp (-(Gc p a) ^ 2)) = C ((b : ZMod p) ^ 2 - (a : ZMod p) ^ 2) := by
  have hG : GV p (Gc p a) 0 := by
    unfold Gc
    exact (GV.C (VG.natCast a)).add (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono (by norm_num))
  have hGr : redP p (Gc p a) = C (a : ZMod p) := by
    unfold Gc
    rw [redP_add (GV.C (VG.natCast a)) (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono
      (by norm_num)), redP_C, redP_C_mul (VG.natCast p) GV.X, redP_X, red_natCast, red_natCast,
      ZMod.natCast_self, C_0, zero_mul, add_zero]
  have h0 : VG p ((b : ℚ) ^ 2 - (b : ℚ) * (p : ℚ)) 0 := by
    have := VG.intCast (p := p) ((b : ℤ) ^ 2 - (b : ℤ) * (p : ℤ)); push_cast at this; exact this
  have hsq : GV p (-(Gc p a) ^ 2) 0 := by
    have := (hG.mul hG).neg; rw [← sq] at this; exact this.mono (by norm_num)
  simp only [cfacQ, add_comp, X_comp, C_comp]
  rw [redP_add hsq (GV.C h0), redP_neg, redP_pow hG, hGr, redP_C, ← C_pow, ← C_neg, ← C_add]
  congr 1
  have : (((b : ℚ) ^ 2 - (b : ℚ) * (p : ℚ) : ℚ) : ZMod p) = (b : ZMod p) ^ 2 := by
    rw [show ((b : ℚ) ^ 2 - (b : ℚ) * (p : ℚ)) = ((((b : ℤ) ^ 2 - (b : ℤ) * (p : ℤ)) : ℤ) : ℚ) by
      push_cast; ring, red_intCast]
    push_cast; rw [ZMod.natCast_self]; ring
  rw [this]; ring

lemma GV0_pow {f : ℚ[X]} (h : GV p f 0) (k : ℕ) : GV p (f ^ k) 0 := by
  have := GV_pow' h k; simpa using this

/-- `Ẽ_u` at `x = a + p X`: the own factor carries `p^{ν_u(a)}`. -/
lemma Eu_comp {m : ℕ} (L : Fin (m + 1) → ℕ) (u : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) :
    (tpolS (cShifts p L u.1 u.2)).comp (-(Gc p a) ^ 2) =
      C ((p : ℚ) ^ nu L u a) *
        ((C (-((a : ℕ) : ℚ)) + C (-2 * ((a : ℕ) : ℚ)) * X - C (p : ℚ) * X ^ 2) ^ nu L u a *
          ∏ b ∈ Finset.univ.erase a, ((cfacQ p b).comp (-(Gc p a) ^ 2)) ^ nu L u b) := by
  rw [tpolS_cShifts, Polynomial.prod_comp, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
    pow_comp, cfacQ_own, mul_pow, ← C_pow]
  simp only [pow_comp]
  ring

/-- `D_N` at `x = a + p X`. -/
lemma DN_comp (N a : ℕ) :
    (D N).comp (-(Gc p a) ^ 2) = C ((-1 : ℚ) ^ N) *
      (C ((p : ℚ) ^ (plc p (PlK N) (a : ZMod p)).card) * piF (locI p (PlK N) a) *
        farP p (PlK N) a) := by
  have h1 : (D N).comp (-X ^ 2) = C ((-1 : ℚ) ^ N) * piPl (PlK N) := by
    rw [piPl_PlK, ← mul_assoc, ← C_mul, ← mul_pow, show ((-1 : ℚ) * -1) = 1 by norm_num, one_pow,
      C_1, one_mul]
  have h2 : (D N).comp (-(Gc p a) ^ 2) = ((D N).comp (-X ^ 2)).comp (Gc p a) := by
    rw [comp_assoc]; simp
  rw [h2, h1, mul_comp, C_comp, piPl, prod_comp_Gc]
  rfl

/-- `entF` at a class representative: `e_st(a) = 6 ℓ_N(a) + ν_s(a) + ν_t(a)`. -/
lemma entF_class {m : ℕ} (hm : 2 * m + 1 = p) (K N : ℕ) (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) (ha : a ≠ 0) :
    entF p N L s t (((a : ℕ) : ZMod p)) =
      6 * (plc p (PlK N) (((a : ℕ) : ZMod p))).card + nu L s a + nu L t a := by
  have h := entF_sub (p := p) K N L s t (((a : ℕ) : ZMod p))
  have hc : ccls hm (((a : ℕ) : ZMod p)) = a :=
    (ccls_unique hm _ a (Or.inl (by push_cast; rfl))).symm
  rw [classCount_eq hm, hc, if_neg ha, Bse, card_plc_PlK] at h
  have ha0 : (a : ℕ) ≠ 0 := fun h0 => ha (Fin.ext h0)
  rw [if_neg ha0] at h
  rw [card_plc_PlK]
  have e1 : (((a : ℕ) : ℤ) : ZMod p) = ((a : ℕ) : ZMod p) := Int.cast_natCast _
  rw [e1] at h
  have : (entF p N L s t (((a : ℕ) : ZMod p)) : ℚ) =
      6 * (SX p N ((a : ℕ) : ZMod p) : ℚ) + nu L s a + nu L t a := by linarith
  exact_mod_cast this

/-- **E3: the closed local numerator** at a class representative `a ≠ 0`. -/
theorem locN_entry (hp5 : 5 ≤ p) {m : ℕ} (hm : 2 * m + 1 = p) (K N : ℕ) (L : Fin (m + 1) → ℕ)
    (s t : Σ a : Fin (m + 1), Fin (L a)) (a : Fin (m + 1)) (ha : a ≠ 0) :
    locN p (entA p K N L s t) (entF p N L s t (((a : ℕ) : ZMod p))) a =
      C ((-1 : ZMod p) ^ K * ((a : ℕ) : ZMod p) ^ 5 * locU p (PlK N) a ^ 6 *
          (∏ b ∈ Finset.univ.erase a, (((b : ℕ) : ZMod p) ^ 2 - ((a : ℕ) : ZMod p) ^ 2) ^ nu L s b) *
          (∏ b ∈ Finset.univ.erase a, (((b : ℕ) : ZMod p) ^ 2 - ((a : ℕ) : ZMod p) ^ 2) ^ nu L t b)) *
        piF (locI p (PlK N) a) ^ 6 * (C (-2 * ((a : ℕ) : ZMod p)) * zv) ^ (nu L s a + nu L t a) := by
  classical
  set G := Gc p (a : ℕ) with hG
  set Z : ℚ[X] := C (-((a : ℕ) : ℚ)) + C (-2 * ((a : ℕ) : ℚ)) * X - C (p : ℚ) * X ^ 2 with hZ
  set ℓ := (plc p (PlK N) (((a : ℕ) : ZMod p))).card with hℓ
  set Rs := ∏ b ∈ Finset.univ.erase a, ((cfacQ p b).comp (-G ^ 2)) ^ nu L s b with hRs
  set Rt := ∏ b ∈ Finset.univ.erase a, ((cfacQ p b).comp (-G ^ 2)) ^ nu L t b with hRt
  have hA : (entA p K N L s t).comp G =
      C ((p : ℚ) ^ (6 * ℓ + nu L s a + nu L t a)) *
        (C ((-1 : ℚ) ^ K) * G ^ 5 * (piF (locI p (PlK N) a) ^ 6 * farP p (PlK N) a ^ 6) *
          (Z ^ nu L s a * Rs) * (Z ^ nu L t a * Rt)) := by
    have h0 : (entA p K N L s t).comp G =
        C ((-1 : ℚ) ^ K) * G ^ 5 * (tpolS (entS p N L s t)).comp (-G ^ 2) := by
      simp only [entA, pull, mul_comp, C_comp, pow_comp, X_comp, comp_assoc, neg_comp]
    rw [h0, tpolS_entS, mul_comp, mul_comp, pow_comp, DN_comp, Eu_comp, Eu_comp]
    simp only [mul_pow, ← C_pow, ← pow_mul]
    rw [show ((-1 : ℚ) ^ (N * 6)) = 1 by rw [pow_mul']; norm_num, C_1, one_mul, ← hℓ,
      show 6 * ℓ + nu L s a + nu L t a = ℓ * 6 + nu L s a + nu L t a by ring, pow_add, pow_add,
      C_mul, C_mul, hRs, hRt, hZ, hG]
    simp only [C_mul, C_neg, C_pow, C_ofNat]
    ring
  rw [entF_class hm K N L s t a ha]
  unfold locN
  rw [hA, ← mul_assoc, ← C_mul]
  have hpow : (p : ℚ) ^ (-((6 * ℓ + nu L s a + nu L t a : ℕ) : ℤ)) *
      (p : ℚ) ^ (6 * ℓ + nu L s a + nu L t a) = 1 := by
    rw [zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero))]
  rw [hpow, C_1, one_mul]
  -- the factors are `p`-integral; reduce them one by one
  have hGv : GV p G 0 := by
    rw [hG]; unfold Gc
    exact (GV.C (VG.natCast _)).add (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono (by norm_num))
  have hGr : redP p G = C (((a : ℕ) : ZMod p)) := by
    rw [hG]; unfold Gc
    rw [redP_add (GV.C (VG.natCast _)) (((GV.C (VG.natCast (p := p) p)).mul GV.X).mono
      (by norm_num)), redP_C, redP_C_mul (VG.natCast p) GV.X, redP_X, red_natCast, red_natCast,
      ZMod.natCast_self, C_0, zero_mul, add_zero]
  have hsg : VG p ((-1 : ℚ) ^ K) 0 := by
    rcases neg_one_pow_eq_or ℚ K with h | h <;> rw [h]
    · exact VG.one
    · exact VG.one.neg
  have hZv : GV p Z 0 := GV_own _
  have hRsv : GV p Rs 0 := GV_prod0 _ _ fun b _ => GV0_pow (GV_far _ _) _
  have hRtv : GV p Rt 0 := GV_prod0 _ _ fun b _ => GV0_pow (GV_far _ _) _
  have hPv : GV p (piF (locI p (PlK N) a) ^ 6 : ℚ[X]) 0 := GV0_pow (GV_piF _) _
  have hFv : GV p (farP p (PlK N) a ^ 6) 0 := GV0_pow (GV_farP _ _) _
  have hc1 : GV p (C ((-1 : ℚ) ^ K) * G ^ 5) 0 := by
    have := (GV.C hsg).mul (GV0_pow hGv 5); simpa using this
  have hc2 : GV p (piF (locI p (PlK N) a) ^ 6 * farP p (PlK N) a ^ 6 : ℚ[X]) 0 := by
    have := hPv.mul hFv; simpa using this
  have hc3 : GV p (Z ^ nu L s a * Rs) 0 := by
    have := (GV0_pow hZv (nu L s a)).mul hRsv; simpa using this
  have hc4 : GV p (Z ^ nu L t a * Rt) 0 := by
    have := (GV0_pow hZv (nu L t a)).mul hRtv; simpa using this
  have hc12 : GV p (C ((-1 : ℚ) ^ K) * G ^ 5 *
      (piF (locI p (PlK N) a) ^ 6 * farP p (PlK N) a ^ 6)) 0 := by
    have := hc1.mul hc2; simpa using this
  have hc123 : GV p (C ((-1 : ℚ) ^ K) * G ^ 5 *
      (piF (locI p (PlK N) a) ^ 6 * farP p (PlK N) a ^ 6) * (Z ^ nu L s a * Rs)) 0 := by
    have := hc12.mul hc3; simpa using this
  rw [redP_mul hc123 hc4, redP_mul hc12 hc3, redP_mul hc1 hc2, redP_mul (GV.C hsg) (GV0_pow hGv 5),
    redP_mul hPv hFv, redP_mul (GV0_pow hZv (nu L s a)) hRsv, redP_mul (GV0_pow hZv (nu L t a)) hRtv,
    redP_pow hGv, hGr, redP_pow (GV_piF _), redP_piF, redP_pow (GV_farP _ _), redP_farP,
    redP_pow hZv, redP_pow hZv, hZ, redP_own hp5, redP_C]
  rw [hRs, hRt, redP_prod _ _ (fun b _ => GV0_pow (GV_far _ _) _),
    redP_prod _ _ (fun b _ => GV0_pow (GV_far _ _) _)]
  simp only [redP_pow (GV_far _ _), hG, redP_far]
  have hsgn : ((((-1 : ℚ) ^ K : ℚ)) : ZMod p) = (-1 : ZMod p) ^ K := by push_cast; ring
  rw [hsgn]
  simp only [← C_pow, ← map_prod, locU]
  simp only [C_mul, C_pow, C_neg, C_ofNat, map_prod, pow_add]
  ring

end entry

end Apery
