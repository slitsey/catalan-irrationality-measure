module

public import CatalanCore.Zeta5.Frames.InnerAlloc
public import CatalanCore.Zeta5.Parity.DirectGen

@[expose] public section

/-!
# ZC22: the centred CRT basis

Replace the ordinary CRT factors `t + c²` by `t + c² - c p` (`c = 0` unchanged).  Then

* the basis `Ẽ_{a,i} = ∏_{c ≠ a} (t + c² - c p)^{L_c} (t + a² - a p)^i` has a `p`-adic unit
  coefficient determinant (`cclass_unimodular`; the factors agree with `t + c²` modulo `p`);
* it has the same entry weights: `v_p^G μ_X(D_N⁶ Ẽ_s Ẽ_t / D_K) ≥ w_s + w_t` whenever the class
  count condition of `class_entry` holds (`centred_entry`), hence the same determinant bound
  (`class_frame_centred`, and for the inner allocation `zc22_inner`);
* at `x = a + p r` the factor `t + a² - a p` is exactly `p (-2a z - p r²)` with `z = r + 1/2`
  (`cfac_local_pos`), at `x = -a + p r` it is `p (2a (r - 1/2) - p r²)` (`cfac_local_neg`): the
  leading local monomials are `z^i`.

The entry bound is proved by the direct bound for a general numerator `tauX_direct_gen`, because the
roots of the centred factors are not integers.
-/

open Finset Polynomial

namespace Apery

/-! ### Definitions -/

/-- The centred CRT factor `t + γ² - γ p` over `ℤ`. -/
noncomputable def cfacZ (p : ℕ) (γ : ℤ) : ℤ[X] := X + C (γ ^ 2 - γ * p)

/-- The centred class polynomial `∏_{c ≠ a} (t + c² - c p)^{L_c} (t + a² - a p)^i`. -/
noncomputable def cclassZ (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) : ℤ[X] :=
  (∏ c ∈ Finset.univ.erase a, cfacZ p ((c : ℕ) : ℤ) ^ L c) * cfacZ p ((a : ℕ) : ℤ) ^ i

/-- The centred class basis over `ℚ`. -/
noncomputable def cclassF (p : ℕ) {m n : ℕ} (L : Fin (m + 1) → ℕ)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n)) (k : Fin (37 * n)) : ℚ[X] :=
  (cclassZ p L (e.symm k).1 (e.symm k).2).map (Int.castRingHom ℚ)

lemma cfacZ_map_ZMod (p : ℕ) (γ : ℤ) :
    (cfacZ p γ).map (Int.castRingHom (ZMod p)) = X - C (-((γ : ZMod p) ^ 2)) := by
  simp [cfacZ, sub_eq_add_neg]

lemma cclassZ_map_ZMod (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    (cclassZ p L a i).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase a, (X - C (-(((c : ℕ) : ZMod p) ^ 2))) ^ L c) *
        (X - C (-(((a : ℕ) : ZMod p) ^ 2))) ^ i := by
  unfold cclassZ
  rw [Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_pow]
  simp only [Polynomial.map_pow, cfacZ_map_ZMod]
  push_cast
  rfl

lemma natDegree_cfacZ (p : ℕ) (γ : ℤ) : (cfacZ p γ).natDegree = 1 := natDegree_X_add_C _

lemma natDegree_cclassZ_le (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    (cclassZ p L a i).natDegree ≤ ∑ c ∈ Finset.univ.erase a, L c + i := by
  unfold cclassZ
  refine (natDegree_mul_le).trans (Nat.add_le_add ?_ ?_)
  · refine (natDegree_prod_le _ _).trans ?_
    refine Finset.sum_le_sum fun c _ => ?_
    refine natDegree_pow_le.trans ?_
    rw [natDegree_cfacZ]; simp
  · refine natDegree_pow_le.trans ?_
    rw [natDegree_cfacZ]; simp

lemma cclassZ_card_lt (p : ℕ) {m n : ℕ} (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n)) (k : Fin (37 * n)) :
    (cclassZ p L (e.symm k).1 (e.symm k).2).natDegree < 37 * n := by
  refine (natDegree_cclassZ_le p L _ _).trans_lt ?_
  have h1 := Finset.add_sum_erase Finset.univ L (Finset.mem_univ (e.symm k).1)
  have := (e.symm k).2.isLt
  omega

/-- **ZC22, unimodularity.**  The centred class basis is a `ℤ_p`-unimodular basis. -/
theorem cclass_unimodular {p : ℕ} [hp : Fact p.Prime] {m : ℕ} (hm : 2 * m + 1 = p) {n : ℕ}
    (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n)) :
    (coeffMat (cclassF p L e)).det ≠ 0 ∧ padicValRat p (coeffMat (cclassF p L e)).det = 0 := by
  classical
  have hunit := coeffMat_det_unit (p := p)
    (fun k => cclassZ p L (e.symm k).1 (e.symm k).2) (fun k => cclassZ_card_lt p L hL e k)
    (fun c : Fin (m + 1) => -(((c : ℕ) : ZMod p) ^ 2)) (sq_injective hm) L
    (fun k => (e.symm k).1) (fun k => (e.symm k).2)
    (fun k => (e.symm k).2.isLt)
    (fun k k' h1 h2 => by
      apply e.symm.injective
      exact Sigma.ext h1 (by
        rw [Fin.heq_ext_iff (by rw [h1])]; exact h2))
    (fun k => cclassZ_map_ZMod p L _ _)
  exact hunit

/-! ### Numerators as shifted products -/

/-- `∏ (t + γ² - γ δ)` over a multiset of pairs `(γ, δ)`. -/
noncomputable def tpolS (S : Multiset (ℤ × ℤ)) : ℚ[X] :=
  (S.map fun x => X + C ((x.1 : ℚ) ^ 2 - (x.1 : ℚ) * (x.2 : ℚ))).prod

lemma tpolS_add (S S' : Multiset (ℤ × ℤ)) : tpolS (S + S') = tpolS S * tpolS S' := by
  simp [tpolS, Multiset.map_add, Multiset.prod_add]

lemma tpolS_nsmul (k : ℕ) (S : Multiset (ℤ × ℤ)) : tpolS (k • S) = tpolS S ^ k := by
  induction k with
  | zero => simp [tpolS]
  | succ k ih => rw [succ_nsmul, tpolS_add, ih, pow_succ]

lemma tpol_eq_tpolS (M : Multiset ℤ) : tpol M = tpolS (M.map fun γ => (γ, 0)) := by
  simp [tpol, tpolS, Multiset.map_map, Function.comp_def]

lemma prod_map_sum_replicate' {α γ β : Type*} [CommMonoid β] (s : Finset α) (L : α → ℕ)
    (v : α → γ) (g : γ → β) :
    ((∑ c ∈ s, Multiset.replicate (L c) (v c)).map g).prod = ∏ c ∈ s, g (v c) ^ L c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Multiset.map_add, Multiset.prod_add, ih, Finset.prod_insert ha,
      Multiset.map_replicate, Multiset.prod_replicate]

/-- The roots of the centred class polynomial with their shifts. -/
noncomputable def cShifts (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    Multiset (ℤ × ℤ) :=
  (∑ c ∈ Finset.univ.erase a, Multiset.replicate (L c) (((c : ℕ) : ℤ), (p : ℤ))) +
    Multiset.replicate i (((a : ℕ) : ℤ), (p : ℤ))

lemma cShifts_fst (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    (cShifts p L a i).map Prod.fst = classRoots L a i := by
  unfold cShifts classRoots
  rw [Multiset.map_add, Multiset.map_replicate]
  congr 1
  have := map_sum (Multiset.mapAddMonoidHom Prod.fst)
    (fun c => Multiset.replicate (L c) (((c : ℕ) : ℤ), (p : ℤ))) (Finset.univ.erase a)
  simp only [Multiset.mapAddMonoidHom_apply] at this
  rw [this]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Multiset.map_replicate]

lemma cShifts_dvd (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    ∀ x ∈ cShifts p L a i, (p : ℤ) ∣ x.2 := by
  intro x hx
  unfold cShifts at hx
  rw [Multiset.mem_add] at hx
  rcases hx with hx | hx
  · rw [Multiset.mem_sum] at hx
    obtain ⟨c, _, hc⟩ := hx
    rw [Multiset.eq_of_mem_replicate hc]
  · rw [Multiset.eq_of_mem_replicate hx]

lemma cclassF_eq (p : ℕ) {m n : ℕ} (L : Fin (m + 1) → ℕ)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n)) (k : Fin (37 * n)) :
    cclassF p L e k = tpolS (cShifts p L (e.symm k).1 (e.symm k).2) := by
  unfold cclassF cclassZ cShifts tpolS
  rw [Polynomial.map_mul, Polynomial.map_prod, Multiset.map_add, Multiset.prod_add,
    prod_map_sum_replicate', Multiset.map_replicate, Multiset.prod_replicate]
  congr 1
  · refine Finset.prod_congr rfl fun c _ => ?_
    simp [cfacZ]
  · simp [cfacZ]

lemma card_cShifts (p : ℕ) {m : ℕ} (L : Fin (m + 1) → ℕ) (a : Fin (m + 1)) (i : ℕ) :
    (cShifts p L a i).card = ∑ c ∈ Finset.univ.erase a, L c + i := by
  unfold cShifts
  simp [Multiset.card_sum]

/-! ### Local valuations of the pulled-back factors -/

section locsec
variable {p : ℕ} [hp : Fact p.Prime]

/-- the local substitution `x = m + p X`. -/
noncomputable def Gm (p : ℕ) (m : ℤ) : ℚ[X] := C (m : ℚ) + C (p : ℚ) * X

lemma GV_Gm (m : ℤ) : GV p (Gm p m) (if (m : ZMod p) = 0 then 1 else 0) := by
  unfold Gm
  split_ifs with h
  · have := GV_lin_comp_class (p := p) m 0 (by simpa using h.symm)
    simpa [sub_comp, X_comp, C_comp] using this
  · have := GV_lin_comp (p := p) m 0
    simpa [sub_comp, X_comp, C_comp] using this

lemma GV_pow' {f : ℚ[X]} {r : ℚ} (h : GV p f r) (k : ℕ) : GV p (f ^ k) (k * r) := by
  induction k with
  | zero => simpa using GV.C (p := p) (VG.one (p := p))
  | succ k ih =>
    rw [pow_succ]
    have := ih.mul h
    refine this.mono (le_of_eq ?_)
    push_cast; ring

/-- Local valuation of one pulled-back factor `-x² + γ² - γ δ`, `p ∣ δ`. -/
lemma GV_fac_pull (hp3 : 3 ≤ p) (γ δ m : ℤ) (hδ : (p : ℤ) ∣ δ) :
    GV p ((X + C ((γ : ℚ) ^ 2 - (γ : ℚ) * (δ : ℚ))).comp (-(Gm p m) ^ 2))
      ((if (γ : ZMod p) = m then 1 else 0) + (if (γ : ZMod p) = -m then 1 else 0)) := by
  set G := Gm p m with hG
  have hcomp : (X + C ((γ : ℚ) ^ 2 - (γ : ℚ) * (δ : ℚ))).comp (-G ^ 2) =
      (C (γ : ℚ) - G) * (C (γ : ℚ) + G) - C ((γ : ℚ) * δ) := by
    simp only [add_comp, X_comp, C_comp]
    simp only [C_sub, C_mul, C_pow]; ring
  rw [hcomp]
  have hA : GV p (C (γ : ℚ) - G) (if (γ : ZMod p) = m then 1 else 0) := by
    have h0 : C (γ : ℚ) - G = -((X - C (γ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) := by
      simp [hG, Gm, sub_comp, X_comp, C_comp]
    rw [h0]
    refine GV.neg ?_
    split_ifs with h
    · exact GV_lin_comp_class (p := p) m γ h
    · exact GV_lin_comp (p := p) m γ
  have hB : GV p (C (γ : ℚ) + G) (if (γ : ZMod p) = -m then 1 else 0) := by
    have h0 : C (γ : ℚ) + G = (X - C (((-γ : ℤ)) : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X) := by
      simp [hG, Gm, sub_comp, X_comp, C_comp]; ring
    rw [h0]
    split_ifs with h
    · refine GV_lin_comp_class (p := p) m (-γ) ?_
      push_cast; rw [h]; ring
    · exact GV_lin_comp (p := p) m (-γ)
  have hAB := hA.mul hB
  have hV : VG p ((γ : ℚ) * δ) ((if (γ : ZMod p) = m then 1 else 0) +
      (if (γ : ZMod p) = -m then 1 else 0)) := by
    have hδ1 : VG p (δ : ℚ) 1 := VG_int_one hδ
    have hγ0 : VG p (γ : ℚ) 0 := VG.intCast γ
    by_cases h1 : (γ : ZMod p) = m <;> by_cases h2 : (γ : ZMod p) = -m
    · have h2m : (2 : ZMod p) * (γ : ZMod p) = 0 := by
        have : (γ : ZMod p) + (γ : ZMod p) = 0 := by
          nth_rewrite 1 [h1]; rw [h2]; ring
        linear_combination this
      have h2ne : (2 : ZMod p) ≠ 0 := by
        intro h
        have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        rw [ZMod.natCast_eq_zero_iff] at this
        have := Nat.le_of_dvd (by norm_num) this
        omega
      have hγz : (γ : ZMod p) = 0 := by
        rcases mul_eq_zero.mp h2m with h | h
        · exact absurd h h2ne
        · exact h
      have hpγ : (p : ℤ) ∣ γ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγz
      have := (VG_int_one hpγ).mul hδ1
      rw [if_pos h1, if_pos h2]
      refine this.mono ?_
      push_cast; norm_num
    · rw [if_pos h1, if_neg h2]
      refine (hγ0.mul hδ1).mono ?_
      push_cast; norm_num
    · rw [if_neg h1, if_pos h2]
      refine (hγ0.mul hδ1).mono ?_
      push_cast; norm_num
    · rw [if_neg h1, if_neg h2]
      have : VG p ((γ : ℚ) * (δ : ℚ)) 0 := by exact_mod_cast VG.intCast (p := p) (γ * δ)
      refine this.mono ?_
      norm_num
  refine GV.sub ?_ (GV.C hV)
  refine hAB.mono (le_of_eq ?_)
  ring

lemma GV_multiset_prod {α : Type*} (s : Multiset α) (f : α → ℚ[X]) (b : α → ℚ)
    (h : ∀ x ∈ s, GV p (f x) (b x)) : GV p (s.map f).prod (s.map b).sum := by
  induction s using Multiset.induction_on with
  | empty => simpa using GV.C (p := p) (VG.one (p := p))
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    exact (h a (Multiset.mem_cons_self _ _)).mul
      (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))

lemma sum_cnt1 (S : Multiset (ℤ × ℤ)) (c : ZMod p) :
    (S.map fun x : ℤ × ℤ => ((if (x.1 : ZMod p) = c then (1 : ℚ) else 0) +
      (if (x.1 : ZMod p) = -c then (1 : ℚ) else 0))).sum =
      ((S.filter fun x => (x.1 : ZMod p) = c).card : ℚ) +
        ((S.filter fun x => (x.1 : ZMod p) = -c).card : ℚ) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    let P1 : ℤ × ℤ → Prop := fun x => (x.1 : ZMod p) = c
    let P2 : ℤ × ℤ → Prop := fun x => (x.1 : ZMod p) = -c
    by_cases h1 : P1 a <;> by_cases h2 : P2 a
    · rw [Multiset.filter_cons_of_pos (p := P1) S h1, Multiset.filter_cons_of_pos (p := P2) S h2]
      have e1 : (if (a.1 : ZMod p) = c then (1 : ℚ) else 0) = 1 := if_pos h1
      have e2 : (if (a.1 : ZMod p) = -c then (1 : ℚ) else 0) = 1 := if_pos h2
      rw [e1, e2]; simp only [Multiset.card_cons]; push_cast; ring
    · rw [Multiset.filter_cons_of_pos (p := P1) S h1, Multiset.filter_cons_of_neg (p := P2) S h2]
      have e1 : (if (a.1 : ZMod p) = c then (1 : ℚ) else 0) = 1 := if_pos h1
      have e2 : (if (a.1 : ZMod p) = -c then (1 : ℚ) else 0) = 0 := if_neg h2
      rw [e1, e2]; simp only [Multiset.card_cons]; push_cast; ring
    · rw [Multiset.filter_cons_of_neg (p := P1) S h1, Multiset.filter_cons_of_pos (p := P2) S h2]
      have e1 : (if (a.1 : ZMod p) = c then (1 : ℚ) else 0) = 0 := if_neg h1
      have e2 : (if (a.1 : ZMod p) = -c then (1 : ℚ) else 0) = 1 := if_pos h2
      rw [e1, e2]; simp only [Multiset.card_cons]; push_cast; ring
    · rw [Multiset.filter_cons_of_neg (p := P1) S h1, Multiset.filter_cons_of_neg (p := P2) S h2]
      have e1 : (if (a.1 : ZMod p) = c then (1 : ℚ) else 0) = 0 := if_neg h1
      have e2 : (if (a.1 : ZMod p) = -c then (1 : ℚ) else 0) = 0 := if_neg h2
      rw [e1, e2]; ring

/-- Local valuation of a product of pulled-back shifted factors. -/
lemma GV_tpolS_pull (hp3 : 3 ≤ p) (S : Multiset (ℤ × ℤ)) (hS : ∀ x ∈ S, (p : ℤ) ∣ x.2) (m : ℤ) :
    GV p ((tpolS S).comp (-(Gm p m) ^ 2))
      (((S.filter fun x => (x.1 : ZMod p) = (m : ZMod p)).card : ℚ) +
        ((S.filter fun x => (x.1 : ZMod p) = -(m : ZMod p)).card : ℚ)) := by
  unfold tpolS
  rw [Polynomial.multiset_prod_comp, Multiset.map_map]
  have hall : ∀ x ∈ S, GV p ((X + C ((x.1 : ℚ) ^ 2 - (x.1 : ℚ) * (x.2 : ℚ))).comp
      (-(Gm p m) ^ 2)) ((if (x.1 : ZMod p) = (m : ZMod p) then (1 : ℚ) else 0) +
        (if (x.1 : ZMod p) = -(m : ZMod p) then (1 : ℚ) else 0)) :=
    fun x hx => GV_fac_pull hp3 x.1 x.2 m (hS x hx)
  have := GV_multiset_prod S (fun x => (X + C ((x.1 : ℚ) ^ 2 - (x.1 : ℚ) * (x.2 : ℚ))).comp
      (-(Gm p m) ^ 2)) (fun x => (if (x.1 : ZMod p) = (m : ZMod p) then (1 : ℚ) else 0) +
        (if (x.1 : ZMod p) = -(m : ZMod p) then (1 : ℚ) else 0)) hall
  rw [sum_cnt1] at this
  exact this

end locsec

/-! ### The entry bound for centred rows -/

lemma natDegree_tpolS_le (S : Multiset (ℤ × ℤ)) : (tpolS S).natDegree ≤ S.card := by
  unfold tpolS
  refine (natDegree_multiset_prod_le _).trans ?_
  rw [Multiset.map_map]
  have : ∀ x ∈ S, (natDegree ∘ fun x : ℤ × ℤ => X + C ((x.1 : ℚ) ^ 2 - (x.1 : ℚ) * (x.2 : ℚ))) x
      = 1 := fun x _ => natDegree_X_add_C _
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

lemma natDegree_pull_le (K : ℕ) (P : ℚ[X]) : (pull K P).natDegree ≤ 5 + 2 * P.natDegree := by
  unfold pull
  refine natDegree_mul_le.trans ?_
  have h1 : (C ((-1 : ℚ) ^ K) * X ^ 5 : ℚ[X]).natDegree ≤ 5 := by
    refine natDegree_mul_le.trans ?_
    rw [natDegree_C]; simp
  have h2 : (P.comp (-X ^ 2)).natDegree ≤ 2 * P.natDegree := by
    refine natDegree_comp_le.trans ?_
    have : (-X ^ 2 : ℚ[X]).natDegree = 2 := by rw [natDegree_neg]; simp
    rw [this]; exact le_of_eq (mul_comm _ _)
  omega

lemma card_filter_fst {p : ℕ} (S : Multiset (ℤ × ℤ)) (c : ZMod p) :
    (S.filter fun x => (x.1 : ZMod p) = c).card =
      ((S.map Prod.fst).filter fun γ : ℤ => (γ : ZMod p) = c).card := by
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

/-- **ZC22, same weights.**  The entries of the centred class basis satisfy the same bounds as the
ordinary class basis (`class_entry`). -/
theorem centred_entry {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {m : ℕ} (n : ℕ)
    (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n))
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (w : (Σ a : Fin (m + 1), Fin (L a)) → ℚ)
    (hentry : ∀ s t : (Σ a : Fin (m + 1), Fin (L a)), ∀ c : ZMod p,
      w s + w t + 4 ≤ classCount p (40 * n) (entryRoots (3 * n) L s t) c)
    (k l : Fin (37 * n)) :
    GV p (μX (40 * n) (D (3 * n) ^ 6 * cclassF p L e k * cclassF p L e l))
      (w (e.symm k) + w (e.symm l)) := by
  classical
  set s := e.symm k with hs
  set t := e.symm l with ht
  set S : Multiset (ℤ × ℤ) := 6 • ((Icc 1 (3 * n)).val.map fun j : ℕ => (((j : ℕ) : ℤ), (0 : ℤ))) +
    cShifts p L s.1 s.2 + cShifts p L t.1 t.2 with hS
  have hP : D (3 * n) ^ 6 * cclassF p L e k * cclassF p L e l = tpolS S := by
    rw [cclassF_eq, cclassF_eq, D_eq_tpol, tpol_eq_tpolS, hS, tpolS_add, tpolS_add, tpolS_nsmul,
      Multiset.map_map]
    rfl
  have hfst : S.map Prod.fst = entryRoots (3 * n) L s t := by
    rw [hS, Multiset.map_add, Multiset.map_add, Multiset.map_nsmul, Multiset.map_map,
      cShifts_fst, cShifts_fst]
    unfold entryRoots
    congr 2
  have hScard : S.card ≤ 18 * n + 2 * (37 * n) := by
    rw [← Multiset.card_map Prod.fst S, hfst]
    simp only [entryRoots, Multiset.card_add, Multiset.card_nsmul, Multiset.card_map,
      Finset.card_val, Nat.card_Icc]
    have h1 : (classRoots L s.1 s.2).card < 37 * n := classRoots_card_lt L hL e k
    have h2 : (classRoots L t.1 t.2).card < 37 * n := classRoots_card_lt L hL e l
    omega
  have hSdvd : ∀ x ∈ S, (p : ℤ) ∣ x.2 := by
    intro x hx
    rw [hS, Multiset.mem_add, Multiset.mem_add] at hx
    rcases hx with (hx | hx) | hx
    · obtain ⟨y, _, rfl⟩ := Multiset.mem_of_mem_nsmul hx |> fun h => Multiset.mem_map.mp h
      exact dvd_zero _
    · exact cShifts_dvd p L _ _ x hx
    · exact cShifts_dvd p L _ _ x hx
  have hp3 : 3 ≤ p := by omega
  set eF : ZMod p → ℕ := fun c => (if c = 0 then 5 else 0) +
    (S.filter fun x => (x.1 : ZMod p) = c).card +
    (S.filter fun x => (x.1 : ZMod p) = -c).card with heF
  have hAloc : ∀ m : ℤ, GV p ((pull (40 * n) (tpolS S)).comp (C (m : ℚ) + C (p : ℚ) * X))
      (eF (m : ZMod p)) := by
    intro m
    have hcomp : (pull (40 * n) (tpolS S)).comp (C (m : ℚ) + C (p : ℚ) * X) =
        C ((-1 : ℚ) ^ (40 * n)) * (Gm p m) ^ 5 * (tpolS S).comp (-(Gm p m) ^ 2) := by
      simp only [pull, mul_comp, C_comp, pow_comp, X_comp, comp_assoc, neg_comp]
      rfl
    rw [hcomp]
    have h1 : VG p ((-1 : ℚ) ^ (40 * n)) 0 := by
      rcases neg_one_pow_eq_or ℚ (40 * n) with h | h <;> rw [h]
      · exact VG.one
      · exact VG.one.neg
    have h2 := GV_pow' (GV_Gm (p := p) m) 5
    have h3 := GV_tpolS_pull hp3 S hSdvd m
    have := ((GV.C h1).mul h2).mul h3
    refine this.mono (le_of_eq ?_)
    simp only [heF]
    push_cast
    split_ifs <;> ring
  have hβ : ∀ c : ZMod p, w s + w t + 4 ≤ (eF c : ℚ) - (plc p (PlK (40 * n)) c).card := by
    intro c
    have h := hentry s t c
    unfold classCount at h
    rw [← hfst] at h
    simp only [heF, card_filter_fst]
    exact h
  have hH : ∀ r ∈ PlK (40 * n), dd r < p ^ 2 := by
    intro r hr
    rw [PlK, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hr
    rcases hr with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [dd_nat]; have := (Finset.mem_Icc.mp hj).2; omega
    · rw [dd_neg (Finset.mem_Icc.mp hj).1]; have := (Finset.mem_Icc.mp hj).2; omega
  have hdeg' : (pull (40 * n) (tpolS S)).natDegree - (PlK (40 * n)).card + 1 < p ^ 2 := by
    have h1 := natDegree_pull_le (40 * n) (tpolS S)
    have h2 := natDegree_tpolS_le S
    rw [card_PlK]
    omega
  rw [hP, μX_eq_tauX]
  have := tauX_direct_gen hp5 (pull (40 * n) (tpolS S)) eF hAloc (PlK (40 * n)) hsep hH hdeg'
    (w s + w t + 4) hβ
  simpa using this

/-- **ZC22, the centred class-basis framework**: `v_p^G(Δ) ≥ 2 ∑ w`. -/
theorem class_frame_centred {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {m : ℕ} (hm : 2 * m + 1 = p)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (w : (Σ a : Fin (m + 1), Fin (L a)) → ℚ)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hentry : ∀ s t : (Σ a : Fin (m + 1), Fin (L a)), ∀ c : ZMod p,
      w s + w t + 4 ≤ classCount p (40 * n) (entryRoots (3 * n) L s t) c) :
    GV p (Δ n) (2 * ∑ s, w s) := by
  classical
  have hcard : Fintype.card (Σ a : Fin (m + 1), Fin (L a)) = 37 * n := by
    rw [Fintype.card_sigma]; simpa using hL
  set e : (Σ a : Fin (m + 1), Fin (L a)) ≃ Fin (37 * n) := Fintype.equivFinOfCardEq hcard
  have hunit := cclass_unimodular hm L hL e
  have hdegF : ∀ k, (cclassF p L e k).natDegree < 37 * n := fun k => by
    have := cclassZ_card_lt p L hL e k
    exact (natDegree_map_le).trans_lt this
  have hfin := zc10_delta (p := p) n (cclassF p L e) hdegF hunit.1 hunit.2
    (fun k => w (e.symm k))
    (fun k l => centred_entry hp5 n L hL e hsep hK hdeg w hentry k l)
  rwa [Equiv.sum_comp e.symm w] at hfin

/-- **ZC22, the inner allocation.**  The centred basis gives the same inner determinant bound as
the ordinary basis (`zc12_inner`). -/
theorem inner_bound_centred {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {m : ℕ} (hm : 2 * m + 1 = p)
    (hm1 : 1 ≤ m)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hP : ∀ a c : Fin (m + 1), a ≠ 0 → c ≠ 0 →
      topw L (Bse p (40 * n) (3 * n)) a - 1 ≤ topw L (Bse p (40 * n) (3 * n)) c)
    (hZ : ∀ a : Fin (m + 1), a ≠ 0 → topw L (Bse p (40 * n) (3 * n)) a - 1 ≤
      2 * L 0 + (Bse p (40 * n) (3 * n) 0 - 4) / 2) :
    GV p (Δ n) (2 * ∑ s, winner hm1 L (Bse p (40 * n) (3 * n)) s) := by
  refine class_frame_centred hp5 hm n L hL _ hsep hK hdeg fun s t c => ?_
  rw [classCount_eq hm]
  exact winner_ACI hm1 L _ hP hZ s t (ccls hm c)

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

/-- **ZC22.**  With the centred CRT basis the inner bound `v_p^G(Δ_K) ≥ γ_p^in` of ZC12 holds
unchanged (same weights `winner`, unimodular basis). -/
theorem zc22_inner [hp : Fact p.Prime] :
    GV p (Δ n) (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s) := by
  have hp5 : 5 ≤ p := by have := H.p200; have := H.hM; omega
  have hsq := H.p_sq
  have hn := H.n_pos
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  refine inner_bound_centred hp5 H.p_odd H.m_pos n (innerL p n L0) H.sum_innerL
    (Sep_PlK (by omega)) (by omega) (by omega) H.inner_P H.inner_Z

end InnerHyp

/-! ### The leading local monomials -/

/-- At `x = a + p r` the centred factor is `p (-2a z - p r²)`, `z = r + 1/2`. -/
theorem cfac_local_pos (p a : ℕ) :
    (X + C ((a : ℚ) ^ 2 - (a : ℚ) * (p : ℚ))).comp (-(Gm p (a : ℤ)) ^ 2) =
      C (p : ℚ) * (C (-2 * (a : ℚ)) * (X + C (1 / 2 : ℚ)) - C (p : ℚ) * X ^ 2) := by
  have hz : (C (-2 * (a : ℚ)) : ℚ[X]) * C (1 / 2 : ℚ) = C (-(a : ℚ)) := by
    rw [← C_mul]; congr 1; ring
  simp only [add_comp, X_comp, C_comp, Gm, Int.cast_natCast]
  simp only [C_sub, C_mul, C_pow, C_neg, C_ofNat] at hz ⊢
  linear_combination (-(C (p : ℚ))) * hz

/-- At `x = -a + p r` the centred factor is `p (2a (r - 1/2) - p r²)`. -/
theorem cfac_local_neg (p a : ℕ) :
    (X + C ((a : ℚ) ^ 2 - (a : ℚ) * (p : ℚ))).comp (-(Gm p (-(a : ℤ))) ^ 2) =
      C (p : ℚ) * (C (2 * (a : ℚ)) * (X - C (1 / 2 : ℚ)) - C (p : ℚ) * X ^ 2) := by
  have hz : (C (2 * (a : ℚ)) : ℚ[X]) * C (1 / 2 : ℚ) = C ((a : ℚ)) := by
    rw [← C_mul]; congr 1; ring
  simp only [add_comp, X_comp, C_comp, Gm, Int.cast_neg, Int.cast_natCast]
  simp only [C_sub, C_mul, C_pow, C_neg, C_ofNat] at hz ⊢
  linear_combination (C (p : ℚ)) * hz

end Apery
