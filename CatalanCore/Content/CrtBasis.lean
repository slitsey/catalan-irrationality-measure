module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# `CatalanCore.Content.CrtBasis`: the CRT basis
(generic: used by every outer-CRT content argument; no Lai numbers)

Linear independence over a field, and unimodularity of the coefficient matrix

For distinct roots `a_r` with multiplicities `m_r` and `Π = ∏ (X - a_r)^{m_r}`:

* `crtE r i = (X - a_r)^i · Π/(X - a_r)^{m_r}` (`i < m_r`) and `crtG j = X^j Π` (`j < d`)
  are linearly independent over a field (`crt_indep`);
* if the total count is `N` and all degrees are `< N`, the coefficient matrix is a unit
  (`crt_det_ne_zero`).

This is the outer CRT of the content notes (FAUZAN-REACH), over `ZMod p` and `ℚ`.
-/

open Finset Polynomial
open scoped BigOperators

namespace CatalanCore.Content

section Crt

variable {R : Type*} [CommRing R] {S : Type*} [Fintype S] [DecidableEq S]

/-- `(X - a_r)^i · ∏_{r' ≠ r} (X - a_{r'})^{m_{r'}}`. -/
noncomputable def crtE (a : S → R) (m : S → ℕ) (r : S) (i : ℕ) : R[X] :=
  (X - C (a r)) ^ i * ∏ r' ∈ univ.erase r, (X - C (a r')) ^ m r'

/-- `X^j · ∏_r (X - a_r)^{m_r}`. -/
noncomputable def crtG (a : S → R) (m : S → ℕ) (j : ℕ) : R[X] :=
  X ^ j * ∏ r, (X - C (a r)) ^ m r

lemma crtE_map {R' : Type*} [CommRing R'] (φ : R →+* R') (a : S → R) (m : S → ℕ) (r : S) (i : ℕ) :
    (crtE a m r i).map φ = crtE (fun s => φ (a s)) m r i := by
  simp [crtE, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub]

lemma crtG_map {R' : Type*} [CommRing R'] (φ : R →+* R') (a : S → R) (m : S → ℕ) (j : ℕ) :
    (crtG a m j).map φ = crtG (fun s => φ (a s)) m j := by
  simp [crtG, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub]

/-- The CRT family, indexed by `(Σ r, Fin (m r)) ⊕ Fin d`. -/
noncomputable def crtFam (a : S → R) (m : S → ℕ) (d : ℕ) : ((Σ r : S, Fin (m r)) ⊕ Fin d) → R[X] :=
  Sum.elim (fun x => crtE a m x.1 x.2) (fun j => crtG a m j)

lemma crtFam_map {R' : Type*} [CommRing R'] (φ : R →+* R') (a : S → R) (m : S → ℕ) (d : ℕ)
    (x : (Σ r : S, Fin (m r)) ⊕ Fin d) :
    (crtFam a m d x).map φ = crtFam (fun s => φ (a s)) m d x := by
  rcases x with ⟨r, i⟩ | j
  · exact crtE_map φ a m r i
  · exact crtG_map φ a m j

end Crt

section Indep

variable {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S]

lemma crtE_natDegree_lt (a : S → K) (m : S → ℕ) (r : S) (i : ℕ) (hi : i < m r) :
    (crtE a m r i).natDegree < ∑ r', m r' := by
  have hmonic : ((X - C (a r)) ^ i * ∏ r' ∈ univ.erase r, (X - C (a r')) ^ m r').Monic :=
    (((monic_X_sub_C _).pow _).mul (monic_prod_of_monic _ _ fun r' _ => (monic_X_sub_C _).pow _))
  unfold crtE
  rw [Polynomial.natDegree_mul' (by rw [(((monic_X_sub_C _).pow _).leadingCoeff), (monic_prod_of_monic _ _ fun r' _ => (monic_X_sub_C _).pow _).leadingCoeff]; simp),
    Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, Polynomial.natDegree_prod_of_monic _ _
      (fun r' _ => (monic_X_sub_C _).pow _)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  have : ∑ r' ∈ univ.erase r, m r' + m r = ∑ r', m r' := Finset.sum_erase_add _ _ (Finset.mem_univ r)
  omega

lemma crtG_natDegree_lt (a : S → K) (m : S → ℕ) (j d : ℕ) (hj : j < d) :
    (crtG a m j).natDegree < ∑ r', m r' + d := by
  unfold crtG
  have hm : (∏ r, (X - C (a r)) ^ m r).Monic := monic_prod_of_monic _ _ fun r' _ => (monic_X_sub_C _).pow _
  rw [Polynomial.natDegree_mul' (by rw [hm.leadingCoeff]; simp), Polynomial.natDegree_X_pow,
    Polynomial.natDegree_prod_of_monic _ _ (fun r' _ => (monic_X_sub_C _).pow _)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  omega

end Indep

section Indep2

variable {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S]

lemma sum_smul_X_pow_coeff {N : ℕ} (g : Fin N → K) (i : Fin N) :
    (∑ i' : Fin N, g i' • (X : K[X]) ^ (i' : ℕ)).coeff i = g i := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : (i : ℕ) ≠ (b : ℕ) := fun h => hb (Fin.ext h.symm)
    simp [this]
  · simp

/-- **CRT independence.** -/
theorem crt_indep (a : S → K) (ha : Function.Injective a) (m : S → ℕ) (d : ℕ) :
    LinearIndependent K (Sum.elim (fun x : Σ r : S, Fin (m r) => crtE a m x.1 x.2)
      (fun j : Fin d => crtG a m j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_sum_type] at hg
  simp only [Sum.elim_inl, Sum.elim_inr] at hg
  rw [Fintype.sum_sigma (fun x : Σ r : S, Fin (m r) => g (Sum.inl x) • crtE a m x.1 x.2)] at hg
  -- the E-part vanishes
  have hE : ∀ r0 : S, ∀ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) = 0 := by
    intro r0 i0
    set T : K[X] := (X - C (a r0)) ^ m r0 with hT
    set Q : K[X] := ∏ r' ∈ univ.erase r0, (X - C (a r')) ^ m r' with hQ
    have hdE : ∀ r, r ≠ r0 → ∀ i : Fin (m r), T ∣ crtE a m r i := by
      intro r hr i
      unfold crtE
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun r' => (X - C (a r')) ^ m r')
        (Finset.mem_erase.2 ⟨Ne.symm hr, Finset.mem_univ _⟩)) _
    have hdG : ∀ j : Fin d, T ∣ crtG a m j := by
      intro j
      unfold crtG
      exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun r' => (X - C (a r')) ^ m r')
        (Finset.mem_univ r0)) _
    have hsm : ∀ (c : K) (q : K[X]), T ∣ q → T ∣ c • q := by
      intro c q hq
      rw [Polynomial.smul_eq_C_mul]; exact Dvd.dvd.mul_left hq _
    set rest : K[X] := ∑ r ∈ univ.erase r0, ∑ i : Fin (m r), g (Sum.inl ⟨r, i⟩) • crtE a m r i +
      ∑ j : Fin d, g (Sum.inr j) • crtG a m j with hrest
    have hrd : T ∣ rest := by
      refine dvd_add (Finset.dvd_sum fun r hr => Finset.dvd_sum fun i _ =>
        hsm _ _ (hdE r (Finset.mem_erase.1 hr).1 i)) (Finset.dvd_sum fun j _ => hsm _ _ (hdG j))
    have hsplit : ∑ r, ∑ i : Fin (m r), g (Sum.inl ⟨r, i⟩) • crtE a m r i =
        ∑ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) • crtE a m r0 i +
          ∑ r ∈ univ.erase r0, ∑ i : Fin (m r), g (Sum.inl ⟨r, i⟩) • crtE a m r i :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ r0)).symm
    set W : K[X] := ∑ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) • (X - C (a r0)) ^ (i : ℕ) with hW
    have hWQ : ∑ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) • crtE a m r0 i = W * Q := by
      rw [hW, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold crtE; rw [smul_mul_assoc]
    have hpart : W * Q = -rest := by
      have : W * Q + rest = 0 := by rw [← hWQ, hrest, ← add_assoc, ← hsplit]; exact hg
      exact eq_neg_of_add_eq_zero_left this
    have hTWQ : T ∣ W * Q := by rw [hpart]; exact (dvd_neg).2 hrd
    have hcop : IsCoprime T Q := by
      rw [hT, hQ]
      refine IsCoprime.pow_left ?_
      exact IsCoprime.prod_right fun r' hr' =>
        ((pairwise_coprime_X_sub_C ha) (Ne.symm (Finset.mem_erase.1 hr').1)).pow_right
    have hTW : T ∣ W := hcop.dvd_of_dvd_mul_right hTWQ
    have hm0 : 0 < m r0 := lt_of_le_of_lt (Nat.zero_le _) i0.2
    have hdegW : W.natDegree < T.natDegree := by
      rw [hT, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := m r0 - 1) ?_) (by omega)
      intro i _
      refine (Polynomial.natDegree_smul_le _ _).trans ?_
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
      have := i.2; omega
    have hW0 : W = 0 := Polynomial.eq_zero_of_dvd_of_natDegree_lt hTW hdegW
    -- recover the coefficients
    have hV : ∑ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) • (X : K[X]) ^ (i : ℕ) = 0 := by
      have h1 : W.comp (X + C (a r0)) = ∑ i : Fin (m r0), g (Sum.inl ⟨r0, i⟩) • (X : K[X]) ^ (i : ℕ) := by
        rw [hW, Polynomial.sum_comp]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Polynomial.smul_eq_C_mul, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.smul_eq_C_mul]
        simp
      rw [← h1, hW0, Polynomial.zero_comp]
    have := sum_smul_X_pow_coeff (fun i : Fin (m r0) => g (Sum.inl ⟨r0, i⟩)) i0
    rw [hV] at this
    simpa using this.symm
  -- the G-part
  have hE0 : ∀ x : Σ r : S, Fin (m r), g (Sum.inl x) = 0 := fun x => hE x.1 x.2
  have hG : ∑ j : Fin d, g (Sum.inr j) • crtG a m j = 0 := by
    rw [← hg]
    have : ∑ x : Σ r : S, Fin (m r), g (Sum.inl x) • crtE a m x.1 x.2 = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [hE0 x, zero_smul]
    rw [Fintype.sum_sigma (fun x : Σ r : S, Fin (m r) => g (Sum.inl x) • crtE a m x.1 x.2)] at this
    rw [this, zero_add]
  have hPi : (∏ r, (X - C (a r)) ^ m r : K[X]) ≠ 0 :=
    (monic_prod_of_monic _ _ fun r' _ => (monic_X_sub_C _).pow _).ne_zero
  have hG' : (∑ j : Fin d, g (Sum.inr j) • (X : K[X]) ^ (j : ℕ)) * ∏ r, (X - C (a r)) ^ m r = 0 := by
    rw [← hG, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold crtG; rw [smul_mul_assoc]
  have hG0 := (mul_eq_zero.1 hG').resolve_right hPi
  intro x
  rcases x with ⟨r, i⟩ | j
  · exact hE r i
  · have := sum_smul_X_pow_coeff (fun j : Fin d => g (Sum.inr j)) j
    rw [hG0] at this
    simpa using this.symm

end Indep2

section Det

variable {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S]

lemma crtFam_natDegree_lt (a : S → K) (m : S → ℕ) (d N : ℕ) (hN : ∑ r, m r + d = N)
    (x : (Σ r : S, Fin (m r)) ⊕ Fin d) : (crtFam a m d x).natDegree < N := by
  rcases x with ⟨r, i⟩ | j
  · have := crtE_natDegree_lt a m r i i.2
    simp only [crtFam, Sum.elim_inl]; omega
  · have := crtG_natDegree_lt a m j d j.2
    simp only [crtFam, Sum.elim_inr]; omega

/-- The coefficient matrix of the CRT basis is nonsingular over a field. -/
theorem crt_det_ne_zero (a : S → K) (ha : Function.Injective a) (m : S → ℕ) (d N : ℕ)
    (hN : ∑ r, m r + d = N) (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin N) :
    (Matrix.of fun (z : Fin N) (i : Fin N) => (crtFam a m d (e.symm z)).coeff i).det ≠ 0 := by
  intro hdet
  have hli : LinearIndependent K (fun z : Fin N => (fun i : Fin N => (crtFam a m d (e.symm z)).coeff i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hind := crt_indep a ha m d
    rw [Fintype.linearIndependent_iff] at hind
    have h0 := hind (fun x => c (e x)) (by
      refine Polynomial.ext fun i => ?_
      rw [Polynomial.finset_sum_coeff, Polynomial.coeff_zero]
      by_cases hi : i < N
      · have := congrFun hc ⟨i, hi⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
        rw [← Equiv.sum_comp e.symm]
        simpa [Polynomial.coeff_smul, crtFam] using this
      · refine Finset.sum_eq_zero fun x _ => ?_
        rw [Polynomial.coeff_smul, Polynomial.coeff_eq_zero_of_natDegree_lt, smul_zero]
        have := crtFam_natDegree_lt a m d N hN x
        simp only [crtFam] at this
        omega)
    intro z
    simpa using h0 (e.symm z)
  have := (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of fun (z : Fin N) (i : Fin N) =>
    (crtFam a m d (e.symm z)).coeff i)).1 hli
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at this
  exact this hdet

end Det


section Unit

variable {S : Type*} [Fintype S] [DecidableEq S]

lemma det_intCast_zmod (p N : ℕ) (B : Matrix (Fin N) (Fin N) ℤ) :
    ((B.det : ℤ) : ZMod p) = (B.map (Int.castRingHom (ZMod p))).det := by
  have := RingHom.map_det (Int.castRingHom (ZMod p)) B
  simpa using this

/-- **Unimodularity.**  For integer roots `a_r` distinct mod `p`, the integer coefficient matrix of the
CRT basis has determinant prime to `p`. -/
theorem crt_det_not_dvd (p : ℕ) [Fact p.Prime] (a : S → ℤ) (ha : Function.Injective fun r => (Int.castRingHom (ZMod p)) (a r))
    (m : S → ℕ) (d N : ℕ) (hN : ∑ r, m r + d = N) (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin N) :
    ¬ (p : ℤ) ∣ (Matrix.of fun (z : Fin N) (i : Fin N) => (crtFam a m d (e.symm z)).coeff i).det := by
  intro h
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h
  have hmat : (Matrix.of fun (z : Fin N) (i : Fin N) => (crtFam a m d (e.symm z)).coeff i).map
      (Int.castRingHom (ZMod p)) = Matrix.of fun (z : Fin N) (i : Fin N) =>
        (crtFam (fun s => (Int.castRingHom (ZMod p)) (a s)) m d (e.symm z)).coeff i := by
    refine Matrix.ext fun z i => ?_
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [← Polynomial.coeff_map, crtFam_map]
  rw [det_intCast_zmod, hmat] at h1
  exact crt_det_ne_zero (fun s => (Int.castRingHom (ZMod p)) (a s)) ha m d N hN e h1

end Unit

#print axioms CatalanCore.Content.crt_indep
#print axioms CatalanCore.Content.crt_det_not_dvd
