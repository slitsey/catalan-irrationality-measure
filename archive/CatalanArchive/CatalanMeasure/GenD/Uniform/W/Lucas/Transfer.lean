module
public import CatalanMeasure.GenD.Uniform.W.MTGlue.Transfer
@[expose] public section
set_option Elab.async false

/-!
# From `ℚ` to `ZMod p`: source covectors of `T-` profiles, parametric table bounds (Lucas / Theorem A)

Same as `MTGlue.Transfer` / `TheoremC.Transfer`, with the table bounds as parameters:
`ZmB Ub Jb` is the common denominator of `α(u,J)`, `Z(u,J)`, `u < Ub`, `J < Jb` (and of `2`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.ZoneZ
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.MTGlue

/-- Common denominator of the moments `α(u,J)`, `Z(u,J)`, `u < 26`, `J < 21`, and of `2`. -/
def ZmB (Ub Jb : ℕ) : ℕ :=
  ((List.range Ub).flatMap fun u => (List.range Jb).flatMap fun J =>
    [(Q.alphaQ u J).den, (zetaRat u J).den]).foldl Nat.lcm 2

theorem foldl_lcm_dvd_self (l : List ℕ) (a : ℕ) : a ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => exact dvd_rfl
  | cons y l ih => exact (Nat.dvd_lcm_left a y).trans (ih _)

theorem two_dvd_ZmB (Ub Jb : ℕ) : 2 ∣ ZmB Ub Jb := foldl_lcm_dvd_self _ 2

theorem lcm_foldl_dvd (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x ∣ l.foldl Nat.lcm a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact (Nat.dvd_lcm_right a x).trans (foldl_lcm_dvd_self l (Nat.lcm a x))
    · exact ih _ h

theorem alphaB_den_dvd (Ub Jb : ℕ) : ∀ u < Ub, ∀ J < Jb, (Q.alphaQ u J).den ∣ ZmB Ub Jb := by
  intro u hu J hJ
  unfold ZmB
  apply lcm_foldl_dvd
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨u, hu, J, hJ, Or.inl rfl⟩

theorem zetaB_den_dvd (Ub Jb : ℕ) : ∀ u < Ub, ∀ J < Jb, (zetaRat u J).den ∣ ZmB Ub Jb := by
  intro u hu J hJ
  unfold ZmB
  apply lcm_foldl_dvd
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨u, hu, J, hJ, Or.inr rfl⟩

variable {p : ℕ} [Fact p.Prime]

/-- Unit hypotheses for the moment table with bounds `Ub`, `Jb`. -/
structure BUnits (Ub Jb : ℕ) (p : ℕ) [Fact p.Prime] : Prop where
  hp2 : p ≠ 2
  hZ : ¬ p ∣ ZmB Ub Jb

theorem BUnits.of_coprime {Ub Jb : ℕ} (h : Nat.Coprime p (ZmB Ub Jb)) : BUnits Ub Jb p where
  hp2 := by
    intro e
    have := two_dvd_ZmB Ub Jb
    rw [← e] at this
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl this)
  hZ := fun hd => (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes h dvd_rfl hd)

theorem alphaUB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) {u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    Q.alphaQ u J ∈ unitSub p := memU_of_dvd (alphaB_den_dvd Ub Jb u hu J hJ) hm.hZ

theorem zetaUB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) {u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    zetaRat u J ∈ unitSub p := memU_of_dvd (zetaB_den_dvd Ub Jb u hu J hJ) hm.hZ

theorem betaUB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) {u J : ℕ} (hu : u < Ub) (hJ : J < Jb) :
    Q.betaQ u J ∈ unitSub p := by
  unfold Q.betaQ
  exact Subring.mul_mem _ (Subring.neg_mem _ (half3U hm.hp2)) (zetaUB hm hu hJ)

theorem phiQ_mem {Ub Jb : ℕ} (hm : BUnits Ub Jb p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < Jb)
    (hσ : σ + 3 ≤ Ub) :
    Q.PhiQ a b J σ ∈ unitSub p := by
  unfold Q.PhiQ
  refine Subring.sum_mem _ fun u hu => ?_
  have hu' := Finset.mem_range.mp hu
  exact Subring.add_mem _
    (Subring.mul_mem _ (alphaUB hm (by omega) hJ) (intCast_mem _ _))
    (Subring.mul_mem _ (betaUB hm (by omega) hJ) (intCast_mem _ _))

/-- The residue of `PhiQ` is the finite digit sum with the residues of the moments. -/
theorem res_PhiQB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) (a b : ℕ → ℤ) {J σ : ℕ} (hJ : J < Jb)
    (hσ : σ + 3 ≤ Ub) :
    palindromicRatResidue p (Q.PhiQ a b J σ) =
      ∑ u ∈ Finset.range (σ + 3),
        (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf a ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf b ((σ : ℤ) - u) : ZMod p)) := by
  let f : ℕ → unitSub p := fun u =>
    if hu : u < σ + 3 then
      ⟨Q.alphaQ u J, alphaUB hm (by omega) hJ⟩ * ((Q.cf a ((σ : ℤ) + 1 - u) : ℤ) : unitSub p) +
        ⟨Q.betaQ u J, betaUB hm (by omega) hJ⟩ * ((Q.cf b ((σ : ℤ) - u) : ℤ) : unitSub p)
    else 0
  have hsum : (⟨Q.PhiQ a b J σ, phiQ_mem hm a b hJ hσ⟩ : unitSub p) =
      ∑ u ∈ Finset.range (σ + 3), f u := by
    apply Subtype.ext
    simp only [Q.PhiQ, AddSubmonoidClass.coe_finset_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu' := Finset.mem_range.mp hu
    simp [f, hu']
  have := congrArg (resHom p) hsum
  rw [map_sum] at this
  rw [resHom_apply] at this
  refine this.trans (Finset.sum_congr rfl fun u hu => ?_)
  have hu' := Finset.mem_range.mp hu
  simp [f, hu', map_add, map_mul, resHom_apply]

/-- `digitPhi` of polynomials with integer coefficients equals the residue of the rational form. -/
theorem digitPhi_eq_resB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) (af bf : ℕ → ℤ) (a b : (ZMod p)[X])
    (ha : ∀ n, a.coeff n = (af n : ZMod p)) (hb : ∀ n, b.coeff n = (bf n : ZMod p))
    {J σ H : ℕ} (hJ : J < Jb) (hσ : σ + 3 ≤ Ub) (hH : σ + 3 ≤ H) :
    digitPhi H (σ : ℤ) (sourceM (p := p) J) (sourceZ (p := p) J) a b (3 / 2) =
      palindromicRatResidue p (Q.PhiQ af bf J σ) := by
  rw [digitPhi_cutoff_signed H (σ + 3) _ hH (by push_cast; omega), res_PhiQB hm af bf hJ hσ]
  unfold digitPhi
  simp only [intrinsicCoeff_castG a af ha, intrinsicCoeff_castG b bf hb]
  rw [Finset.sum_range_succ]
  have hz : Q.cf af ((σ : ℤ) + 1 - ((σ + 3 : ℕ) : ℤ)) = 0 := by
    unfold Q.cf; rw [if_neg]; push_cast; omega
  rw [hz]
  simp only [Int.cast_zero, zero_mul, add_zero]
  have h32 := res_half3G hm.hp2
  have hneg : palindromicRatResidue p (-(3 / 2 : ℚ)) = -(3 / 2 : ZMod p) := by
    have := map_neg (resHom p) ⟨(3 / 2 : ℚ), half3U hm.hp2⟩
    simpa [resHom_apply, h32] using this
  have hβ : ∀ u ∈ Finset.range (σ + 3), palindromicRatResidue p (Q.betaQ u J) =
      -(3 / 2 : ZMod p) * sourceZ (p := p) J u := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    have := map_mul (resHom p) ⟨-(3 / 2 : ℚ), Subring.neg_mem _ (half3U hm.hp2)⟩
      ⟨zetaRat u J, zetaUB hm (by omega) hJ⟩
    simp only [resHom_apply, MulMemClass.coe_mul] at this
    unfold Q.betaQ sourceZ
    rw [this, hneg]
  have hα : ∀ u ∈ Finset.range (σ + 3), palindromicRatResidue p (Q.alphaQ u J) =
      sourceM (p := p) J u := fun u _ => rfl
  have hstep : ∀ u ∈ Finset.range (σ + 3),
      (palindromicRatResidue p (Q.alphaQ u J) * (Q.cf af ((σ : ℤ) + 1 - u) : ZMod p) +
          palindromicRatResidue p (Q.betaQ u J) * (Q.cf bf ((σ : ℤ) - u) : ZMod p)) =
      ((Q.cf af ((σ : ℤ) + 1 - u) : ℤ) : ZMod p) * sourceM (p := p) J u +
        (-(3 / 2 : ZMod p)) * (((Q.cf bf ((σ : ℤ) - u) : ℤ) : ZMod p) * sourceZ (p := p) J u) := by
    intro u hu
    rw [hα u hu, hβ u hu]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **`ψ` of the `T-` profile `z`** is the residue of the rational form of the combined polynomials
. -/
theorem psiY_eqB {Ub Jb : ℕ} (hm : BUnits Ub Jb p) (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) {J σ H : ℕ}
    (hJ : J < Jb) (hσ : σ + 3 ≤ Ub) (hH : σ + 3 ≤ H) :
    (profY p K k0).psi H J (σ : ℤ) (zprof p K z) =
      palindromicRatResidue p (Q.PhiQ (cmb z k0 K y2uI) (cmb z k0 K tI) J σ) :=
  digitPhi_eq_resB hm _ _ _ _ (gyMap_coeff K k0 z) (tyMap_coeff K k0 z) hJ hσ hH

end CatalanMeasure.GenD.Uniform.W.Lucas
end
