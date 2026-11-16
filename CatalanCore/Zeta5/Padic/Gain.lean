module

public import CatalanCore.Zeta5.Padic.Ident
public import CatalanCore.Zeta5.Parity.Gain

@[expose] public section

/-!
# ZC23 + ZC25 + ZC26: the parity gain (steps E5, E6)

`parity_gain : ParityGain`: in the inner range, `v_p^G(Δ_K) ≥ 2 ∑ w + k` with `k = kpar`.

Proof. The radical vectors of `𝓛` on the even group (`radical_T_odd/even`) span `V`. The rows of
the zero class impose at most `L₀` linear conditions `Φ` on `V` (border rank–nullity,
`finrank_ker_ge`). A basis `v_j` of `ker Φ`, rescaled by `λ⁻¹` and placed on the rows of the even
group (`ι`), gives vectors `u_j` that are left radical modulo `p` for the normalised Gram matrix:
against a zero-class row by `Φ = 0`, against an integral-weight row of a nonzero class (which lies in
the even group) by (H′) (`lead_entry`) and `𝓛(v, ·) = 0`. Then `parity_gain_delta`.
-/

open Finset Polynomial
open scoped Classical

namespace Apery

lemma card_filter_coe {α : Type*} (s : Finset α) (Q : α → Prop) (Q' : ↥s → Prop)
    {iQ : DecidablePred Q} {iQ' : DecidablePred Q'} (hQ : ∀ a, Q' a ↔ Q a.1) :
    ((Finset.univ : Finset ↥s).filter Q').card = (s.filter Q).card := by
  rw [← Finset.card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ⟨a.2, (hQ a).mp ha⟩
  · rintro ⟨hx, hq⟩; exact ⟨⟨x, hx⟩, (hQ _).mpr hq, rfl⟩

/-- border rank–nullity with an independent family in the kernel. -/
lemma exists_li_ker {F V J : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Fintype J] (g : V →ₗ[F] (J → F)) :
    ∃ (k : ℕ) (b : Fin k → V), Module.finrank F V - Fintype.card J ≤ k ∧
      LinearIndependent F b ∧ ∀ j, g (b j) = 0 := by
  refine ⟨Module.finrank F (LinearMap.ker g), fun j => (Module.finBasis F (LinearMap.ker g) j : V),
    ParityData.finrank_ker_ge g, ?_, fun j => (Module.finBasis F (LinearMap.ker g) j).2⟩
  exact (Module.finBasis F (LinearMap.ker g)).linearIndependent.map' (LinearMap.ker g).subtype
    (Submodule.ker_subtype _)

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0) [hp : Fact p.Prime]
include H

lemma toRow_inj : Function.Injective (H.toRow (p := p)) := by
  intro r r' h
  have h1 : r.1.1 = r'.1.1 := congrArg Sigma.fst h
  have h1' : r.1 = r'.1 := Subtype.ext h1
  have h2 : HEq r.2 r'.2 := (Sigma.mk.inj_iff.mp h).2
  exact Sigma.ext h1' h2

lemma lam_ne (r : (H.parityData (p := p)).Row) : H.lam r ≠ 0 :=
  pow_ne_zero _ (m2a_ne H.p_odd (H.mem_parS r.1.2).1)

/-- the even-group count of `ParityData` is the count of `kpar`. -/
lemma count_le_kpar {k0 : ℕ}
    (hodd : innerT p n L0 % 2 = 1 →
      (Finset.univ.filter fun a : (H.parityData (p := p)).S =>
        (H.parityData (p := p)).P a ∧ ¬ (H.parityData (p := p)).ext a).card -
      (Finset.univ.filter fun b : (H.parityData (p := p)).S =>
        ¬ (H.parityData (p := p)).P b ∧ (H.parityData (p := p)).active b).card ≤ k0)
    (hev : innerT p n L0 % 2 = 0 →
      (Finset.univ.filter fun a : (H.parityData (p := p)).S =>
        (H.parityData (p := p)).P a ∧ (H.parityData (p := p)).ext a).card -
      (Finset.univ.filter fun b : (H.parityData (p := p)).S =>
        ¬ (H.parityData (p := p)).P b ∧ ¬ (H.parityData (p := p)).ext b).card ≤ k0) :
    kpar p n L0 ≤ k0 - L0 := by
  unfold kpar
  split_ifs with hT
  · have h := hodd hT
    have e1 : (Finset.univ.filter fun a : (H.parityData (p := p)).S =>
        (H.parityData (p := p)).P a ∧ ¬ (H.parityData (p := p)).ext a).card =
        ((parS p n).filter fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∉ epsSet p n L0).card := by
      exact card_filter_coe _ _ _ fun a => Iff.rfl
    have e2 : (Finset.univ.filter fun b : (H.parityData (p := p)).S =>
        ¬ (H.parityData (p := p)).P b ∧ (H.parityData (p := p)).active b).card =
        ((parS p n).filter fun b : Fin (p / 2 + 1) => lN p n b % 2 = 1 ∧ b ∈ epsSet p n L0 ∧
          0 < innerL p n L0 b).card := by
      refine card_filter_coe _ _ _ fun b => ?_
      show (¬ (lN p n b.1 % 2 = 0) ∧ (b.1 ∈ epsSet p n L0 ∧ 0 < innerL p n L0 b.1)) ↔ _
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
    rw [e1, e2] at h
    omega
  · have hT' : innerT p n L0 % 2 = 0 := by omega
    have h := hev hT'
    have e1 : (Finset.univ.filter fun a : (H.parityData (p := p)).S =>
        (H.parityData (p := p)).P a ∧ (H.parityData (p := p)).ext a).card =
        ((parS p n).filter fun a : Fin (p / 2 + 1) => lN p n a % 2 = 0 ∧ a ∈ epsSet p n L0).card := by
      exact card_filter_coe _ _ _ fun a => Iff.rfl
    have e2 : (Finset.univ.filter fun b : (H.parityData (p := p)).S =>
        ¬ (H.parityData (p := p)).P b ∧ ¬ (H.parityData (p := p)).ext b).card =
        ((parS p n).filter fun b : Fin (p / 2 + 1) => lN p n b % 2 = 1 ∧ b ∉ epsSet p n L0).card := by
      refine card_filter_coe _ _ _ fun b => ?_
      show (¬ (lN p n b.1 % 2 = 0) ∧ ¬ (b.1 ∈ epsSet p n L0)) ↔ _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    rw [e1, e2] at h
    omega

/-- an integral-weight row of a nonzero class lies in the even group. -/
lemma mem_parS_of_int (a : Fin (p / 2 + 1)) (ha : a ≠ 0) (i : Fin (innerL p n L0 a))
    (h : Int.fract (winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨a, i⟩) = 0) :
    a ∈ parS p n := by
  unfold parS
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, ?_⟩
  set w := winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) ⟨a, i⟩ with hw
  have hwz : w = (⌊w⌋ : ℚ) := by
    have := Int.self_sub_floor w; rw [h] at this; linarith
  have h1 := H.winner_nz ⟨a, i⟩ ha
  have h2 := H.Bse_nz a ha
  rw [← hw] at h1
  simp only at h1
  by_cases hA : a ∈ epsSet p n L0
  · rw [if_pos hA] at h2
    have : ((lK p n a : ℤ) : ℚ) = ((2 * ((i : ℕ) + (innerT p n L0 : ℤ) + 1 -
        (innerL p n L0 a : ℤ) - 2 - ⌊w⌋) : ℤ) : ℚ) := by push_cast; linarith
    have := Int.cast_injective (α := ℚ) this
    omega
  · rw [if_neg hA] at h2
    have : ((lK p n a : ℤ) : ℚ) = ((2 * ((i : ℕ) + (innerT p n L0 : ℤ) + 0 -
        (innerL p n L0 a : ℤ) - 2 - ⌊w⌋) : ℤ) : ℚ) := by push_cast; linarith
    have := Int.cast_injective (α := ℚ) this
    omega

/-- **The parity gain in the inner range.** -/
theorem parity_gain_inner :
    GV p (Δ n) (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s + (kpar p n L0 : ℚ)) := by
  have hp5 := H.p5
  have hsq := H.p_sq
  have hn := H.n_pos
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  have hsep : Sep p (PlK (40 * n)) := Sep_PlK (by omega)
  have hK : 40 * n < p ^ 2 := by omega
  have hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2 := by omega
  have hL : ∑ c, innerL p n L0 c = 37 * n := H.sum_innerL
  have hcard : Fintype.card (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)) = 37 * n := by
    rw [Fintype.card_sigma]; simpa using hL
  set e : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)) ≃ Fin (37 * n) :=
    Fintype.equivFinOfCardEq hcard with he
  set w := winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) with hwdef
  have hunit := cclass_unimodular H.p_odd (innerL p n L0) hL e
  have hdegF : ∀ k, (cclassF p (innerL p n L0) e k).natDegree < 37 * n := fun k =>
    (natDegree_map_le).trans_lt (cclassZ_card_lt p (innerL p n L0) hL e k)
  have hwhalf : ∀ k, ∃ z : ℤ, w (e.symm k) = z / 2 := fun k =>
    winner_half H.m_pos (innerL p n L0) _ (fun a => Bse_int p (40 * n) (3 * n) a) _
  have hentry : ∀ s t : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)), ∀ c : ZMod p,
      w s + w t + 4 ≤ classCount p (40 * n) (entryRoots (3 * n) (innerL p n L0) s t) c :=
    fun s t c => by
      rw [classCount_eq H.p_odd]; exact winner_ACI H.m_pos _ _ H.inner_P H.inner_Z s t _
  have hG : ∀ k l, GV p (μX (40 * n) (D (3 * n) ^ 6 * cclassF p (innerL p n L0) e k *
      cclassF p (innerL p n L0) e l)) (w (e.symm k) + w (e.symm l)) :=
    fun k l => centred_entry hp5 n (innerL p n L0) hL e hsep hK hdeg w hentry k l
  -- the entries, theorem (A)
  have hβ : ∀ k l, ∀ c : ZMod p, ((⌊w (e.symm k)⌋ + ⌊w (e.symm l)⌋ + 4 : ℤ) : ℚ) ≤
      classCount p (40 * n) (entryRoots (3 * n) (innerL p n L0) (e.symm k) (e.symm l)) c := by
    intro k l c
    have h1 := Int.floor_le (w (e.symm k)); have h2 := Int.floor_le (w (e.symm l))
    have := hentry (e.symm k) (e.symm l) c
    push_cast; linarith
  choose z y hz using fun k l => entry_lead hp5 n (innerL p n L0) hL e hsep hK hdeg k l
    (⌊w (e.symm k)⌋ + ⌊w (e.symm l)⌋ + 4) (hβ k l)
  -- the radical vectors of the leading form
  obtain ⟨k0, u0, hk0, hli0, hrad0⟩ : ∃ (k0 : ℕ) (u0 : Fin k0 → (H.parityData (p := p)).Row → ZMod p),
      kpar p n L0 ≤ k0 - L0 ∧ LinearIndependent (ZMod p) u0 ∧
        ∀ i v, (H.parityData (p := p)).leadL (u0 i) v = 0 := by
    by_cases hT : innerT p n L0 % 2 = 1
    · obtain ⟨k0, u0, hc, hli, hr⟩ := (H.parityData (p := p)).radical_T_odd hT
      exact ⟨k0, u0, H.count_le_kpar (fun _ => hc) (fun h => absurd h (by omega)), hli, hr⟩
    · have hT' : innerT p n L0 % 2 = 0 := by omega
      obtain ⟨k0, u0, hc, hli, hr⟩ := (H.parityData (p := p)).radical_T_even hT'
      exact ⟨k0, u0, H.count_le_kpar (fun h => absurd h hT) (fun _ => hc), hli, hr⟩
  set V : Submodule (ZMod p) ((H.parityData (p := p)).Row → ZMod p) :=
    Submodule.span (ZMod p) (Set.range u0) with hV
  have hVrad : ∀ v ∈ V, ∀ x, (H.parityData (p := p)).leadL v x = 0 := by
    intro v hv
    have hle : V ≤ LinearMap.ker (H.parityData (p := p)).leadL := by
      rw [hV, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_ker.mpr (LinearMap.ext fun x => hrad0 i x)
    intro x
    rw [LinearMap.mem_ker.mp (hle hv)]
    rfl
  have hfinV : Module.finrank (ZMod p) V = k0 := by
    rw [hV, finrank_span_eq_card hli0]; simp
  -- the border conditions of the zero-class rows
  let ρ : (H.parityData (p := p)).Row → Fin (37 * n) → ZMod p :=
    fun r t => ((z (e (H.toRow r)) t : ℚ) : ZMod p)
  let Φ : V →ₗ[ZMod p] (Fin (innerL p n L0 0) → ZMod p) :=
    (LinearMap.pi fun i : Fin (innerL p n L0 0) =>
      ∑ r, ((H.lam r)⁻¹ * ρ r (e ⟨0, i⟩)) • LinearMap.proj r).comp V.subtype
  have hΦ : ∀ v : V, ∀ i, Φ v i = ∑ r, (v : (H.parityData (p := p)).Row → ZMod p) r *
      ((H.lam r)⁻¹ * ρ r (e ⟨0, i⟩)) := by
    intro v i
    simp only [Φ, LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, Submodule.coe_subtype,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun r _ => by ring
  obtain ⟨kk, bK, hker, hbli, hbΦ⟩ := exists_li_ker Φ
  simp only [Fintype.card_fin] at hker
  have h0L := H.innerL_zero
  let v : Fin kk → (H.parityData (p := p)).Row → ZMod p :=
    fun j => ((bK j : V) : (H.parityData (p := p)).Row → ZMod p)
  have hvli : LinearIndependent (ZMod p) v := hbli.map' V.subtype (Submodule.ker_subtype _)
  have hvrad : ∀ j x, (H.parityData (p := p)).leadL (v j) x = 0 :=
    fun j => hVrad _ (bK j).2
  have hvΦ : ∀ j i, ∑ r, v j r * ((H.lam r)⁻¹ * ρ r (e ⟨0, i⟩)) = 0 := by
    intro j i
    have := congrFun (hbΦ j) i
    rw [hΦ] at this
    exact this
  -- placing the vectors on the rows of `Fin (37 n)`
  let ι : ((H.parityData (p := p)).Row → ZMod p) →ₗ[ZMod p] (Fin (37 * n) → ZMod p) :=
    { toFun := fun x k => ∑ r, x r * (H.lam r)⁻¹ * (if e (H.toRow r) = k then 1 else 0)
      map_add' := fun x x' => by
        ext k
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        ext k
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring }
  have hι : ∀ x k, ι x k = ∑ r, x r * (H.lam r)⁻¹ * (if e (H.toRow r) = k then 1 else 0) :=
    fun x k => rfl
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext r0
    have h := congrFun hx (e (H.toRow r0))
    rw [hι, Finset.sum_eq_single r0] at h
    · rw [if_pos rfl, mul_one] at h
      exact (mul_eq_zero.mp h).resolve_right (inv_ne_zero (H.lam_ne r0))
    · intro r _ hr
      rw [if_neg (fun h' => hr (H.toRow_inj (e.injective h'))), mul_zero]
    · simp
  let u : Fin kk → Fin (37 * n) → ZMod p := fun j => ι (v j)
  have hu : LinearIndependent (ZMod p) u := hvli.map' ι (LinearMap.ker_eq_bot.mpr hιinj)
  have hsupp : ∀ j k, u j k ≠ 0 → Int.fract (w (e.symm k)) = 0 := by
    intro j k hk
    by_contra hfr
    apply hk
    show ι (v j) k = 0
    rw [hι]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg, mul_zero]
    intro hrk
    apply hfr
    obtain ⟨zz, hzz⟩ := H.winner_int (H.toRow r) r.1.2
    rw [← hrk, Equiv.symm_apply_apply, hwdef, hzz]
    exact Int.fract_intCast zz
  -- the radical condition
  have hrad : ∀ j t, Int.fract (w (e.symm t)) = 0 → GV p
      (∑ s, C ((((u j s).val : ℕ) : ℤ) : ℚ) * normGram (p := p) (fun i => ⌊w (e.symm i)⌋)
        (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * cclassF p (innerL p n L0) e a *
          cclassF p (innerL p n L0) e b)) s t) 1 := by
    intro j t ht
    have hent : ∀ s, normGram (p := p) (fun i => ⌊w (e.symm i)⌋)
        (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 * cclassF p (innerL p n L0) e a *
          cclassF p (innerL p n L0) e b)) s t = C (z s t) - C (y s t) * X := by
      intro s
      rw [normGram, Matrix.of_apply, Matrix.of_apply, ← (hz s t).1]
      congr 3
      ring
    have hsplit : ∑ s, C ((((u j s).val : ℕ) : ℤ) : ℚ) * normGram (p := p)
        (fun i => ⌊w (e.symm i)⌋) (Matrix.of fun a b => μX (40 * n) (D (3 * n) ^ 6 *
          cclassF p (innerL p n L0) e a * cclassF p (innerL p n L0) e b)) s t =
        C (∑ s, (((u j s).val : ℕ) : ℤ) * z s t) - C (∑ s, (((u j s).val : ℕ) : ℤ) * y s t) * X := by
      simp only [hent, map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, C_mul]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hsplit]
    have hy1 : VG p (∑ s, ((((u j s).val : ℕ) : ℤ) : ℚ) * y s t) 1 :=
      VG.sum _ fun s _ => ((VG.intCast _).mul (hz s t).2.2.2).mono (by norm_num)
    have hz0 : VG p (∑ s, ((((u j s).val : ℕ) : ℤ) : ℚ) * z s t) 0 :=
      VG.sum _ fun s _ => ((VG.intCast _).mul (hz s t).2.1).mono (by norm_num)
    have hred : ((∑ s, ((((u j s).val : ℕ) : ℤ) : ℚ) * z s t : ℚ) : ZMod p) =
        ∑ r, v j r * ((H.lam r)⁻¹ * ρ r t) := by
      rw [red_sum _ _ fun s _ => ((VG.intCast _).mul (hz s t).2.1).mono (by norm_num)]
      have e1 : ∀ s, (((((u j s).val : ℕ) : ℤ) : ℚ) * z s t : ℚ) =
          (u j s : ZMod p) * ((z s t : ℚ) : ZMod p) := by
        intro s
        rw [red_mul (VG.intCast _) (hz s t).2.1, red_intCast]
        push_cast
        rw [ZMod.natCast_zmod_val]
      simp only [e1]
      show ∑ s, ι (v j) s * ((z s t : ℚ) : ZMod p) = _
      simp only [hι, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [Finset.mem_univ, if_true, ρ]
    have hz1 : VG p (∑ s, ((((u j s).val : ℕ) : ℤ) : ℚ) * z s t) 1 := by
      refine VG_one_of_red hz0 ?_
      rw [hred]
      -- the column `t`
      obtain ⟨⟨a, i⟩, hx⟩ : ∃ x, e.symm t = x := ⟨_, rfl⟩
      have ht' : t = e ⟨a, i⟩ := by rw [← hx, Equiv.apply_symm_apply]
      subst ht'
      rw [Equiv.symm_apply_apply] at ht
      by_cases ha : a = 0
      · subst ha
        exact hvΦ j i
      · have haS := H.mem_parS_of_int a ha i ht
        set r2 : (H.parityData (p := p)).Row := ⟨⟨a, haS⟩, i⟩ with hr2
        have hr2' : (⟨a, i⟩ : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) = H.toRow r2 := rfl
        rw [hr2']
        have hlead : ∀ r, ρ r (e (H.toRow r2)) =
            H.lam r * H.lam r2 * (H.parityData (p := p)).leadL ((H.parityData (p := p)).e r)
              ((H.parityData (p := p)).e r2) := by
          intro r
          obtain ⟨zr, hzr⟩ := H.winner_int (H.toRow r) r.1.2
          obtain ⟨z2, hz2⟩ := H.winner_int (H.toRow r2) r2.1.2
          have h3 := (hz (e (H.toRow r)) (e (H.toRow r2))).2.2.1
          simp only [Equiv.symm_apply_apply] at h3
          show ((z (e (H.toRow r)) (e (H.toRow r2)) : ℚ) : ZMod p) = _
          rw [h3]
          refine H.lead_entry r r2 _ ?_
          rw [hwdef, hzr, hz2]
          push_cast
          rw [Int.floor_intCast, Int.floor_intCast]
        simp only [hlead]
        have hsum : ∑ r, v j r * ((H.lam r)⁻¹ * (H.lam r * H.lam r2 *
            (H.parityData (p := p)).leadL ((H.parityData (p := p)).e r)
              ((H.parityData (p := p)).e r2))) =
            H.lam r2 * (H.parityData (p := p)).leadL (v j) ((H.parityData (p := p)).e r2) := by
          have hvj : v j = ∑ r, v j r • (H.parityData (p := p)).e r := by
            funext x
            simp only [ParityData.e, Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
              mul_ite, mul_one, mul_zero]
            simp
          conv_rhs => rw [hvj]
          rw [map_sum, LinearMap.sum_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
          have := H.lam_ne r
          field_simp
        rw [hsum, hvrad, mul_zero]
    exact (GV.C hz1).sub (((GV.C hy1).mul GV.X).mono (by norm_num))
  have hfin := parity_gain_delta n (cclassF p (innerL p n L0) e) hdegF hunit.1 hunit.2
    (fun k => w (e.symm k)) hwhalf hG u hu hsupp hrad
  rw [Equiv.sum_comp e.symm w] at hfin
  refine hfin.mono ?_
  have hkk : kpar p n L0 ≤ kk := by omega
  have : (kpar p n L0 : ℚ) ≤ kk := by exact_mod_cast hkk
  linarith

end InnerHyp

/-- **The parity gain** (hypothesis `hpar` of ZC32). -/
theorem parity_gain : ParityGain := fun p n M H _ => by
  haveI : Fact p.Prime := ⟨H.prime⟩
  exact H.parity_gain_inner

end Apery
