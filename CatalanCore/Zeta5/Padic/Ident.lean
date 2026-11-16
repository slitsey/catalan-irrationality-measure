module

public import CatalanCore.Zeta5.Padic.Classify
public import CatalanCore.Zeta5.Parity.Radical

@[expose] public section

/-!
# ZC23 = (H′): the leading entries of the even group (step E4)

In the inner range, the classes of the even group `S = parS` carry the parity data `parityData`:
`L = innerL`, `P a ⇔ ℓ_N(a)` even, `ext = epsSet`, `T = innerT`, `Bn a = B_{I^N_a}³`,
`cc a b = (b² - a²)⁻¹ (-2a)^{L_a} ((-2b)^{L_b - 1})⁻¹`, `δ_a = 2 ū_K(a)⁻¹ κ_a U_a²`,
`Cf a = fullSym (I^K_a)`.

* `lead_entry`: for rows `r₁, r₂` of `S` and `β = w_{r₁} + w_{r₂} + 4`,
  `∑_{c<p} locSymb(c) = λ_{r₁} λ_{r₂} 𝓛(e_{r₁}, e_{r₂})`, `λ_{a,i} = (-2a)^i`.
-/

open Finset Polynomial
open scoped Classical

namespace Apery

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0) [hp : Fact p.Prime]
include H

/-- `b² - a²` in `𝔽_p`. -/
noncomputable def wsq (p : ℕ) {m : ℕ} (a b : Fin (m + 1)) : ZMod p :=
  ((b : ℕ) : ZMod p) ^ 2 - ((a : ℕ) : ZMod p) ^ 2

omit H in
lemma wsq_ne {m : ℕ} (hm : 2 * m + 1 = p) {a b : Fin (m + 1)} (h : a ≠ b) : wsq p a b ≠ 0 := by
  intro h0
  apply h
  apply sq_injective hm
  simp only
  unfold wsq at h0
  linear_combination h0

omit H in
lemma natCast_fin_ne {m : ℕ} (hm : 2 * m + 1 = p) {a : Fin (m + 1)} (ha : a ≠ 0) :
    ((a : ℕ) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have h1 : (a : ℕ) ≠ 0 := fun h' => ha (Fin.ext h')
  have := Nat.le_of_dvd (Nat.pos_of_ne_zero h1) h
  have := a.isLt
  omega

omit H in
lemma m2a_ne {m : ℕ} (hm : 2 * m + 1 = p) {a : Fin (m + 1)} (ha : a ≠ 0) :
    (-2 * ((a : ℕ) : ZMod p)) ≠ 0 := by
  have h2 := two_ne_zero_zmod (p := p) hm
  have := natCast_fin_ne hm ha
  intro h0
  have : (2 : ZMod p) * ((a : ℕ) : ZMod p) = 0 := by linear_combination -h0
  rcases mul_eq_zero.mp this with h | h
  · exact h2 h
  · exact natCast_fin_ne hm ha h

/-- `U_a = ∏_{b ≠ a} (b² - a²)^{L_b}`. -/
noncomputable def Ua (a : Fin (p / 2 + 1)) : ZMod p :=
  ∏ b ∈ Finset.univ.erase a, wsq p a b ^ innerL p n L0 b

/-- `κ_a = (-1)^K a⁵ ū_N(a)⁶`. -/
noncomputable def kap (a : Fin (p / 2 + 1)) : ZMod p :=
  (-1 : ZMod p) ^ (40 * n) * ((a : ℕ) : ZMod p) ^ 5 * locU p (PlK (3 * n)) a ^ 6

lemma mem_parS {a : Fin (p / 2 + 1)} (ha : a ∈ parS p n) : a ≠ 0 ∧ lK p n a % 2 = 0 :=
  (Finset.mem_filter.mp ha).2

lemma class_bounds {a : Fin (p / 2 + 1)} (ha : a ≠ 0) : 1 ≤ (a : ℕ) ∧ 2 * (a : ℕ) < p := by
  have h1 : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  have := a.isLt
  have := H.p_odd
  omega

/-- the local pole set of `D_N` at an even-`ℓ_N` class is centred. -/
lemma locIN_sym {a : Fin (p / 2 + 1)} (ha : a ≠ 0) (hP : lN p n a % 2 = 0) :
    (locI p (PlK (3 * n)) a).image refl = locI p (PlK (3 * n)) a ∧
      Even (locI p (PlK (3 * n)) a).card := by
  have hcard : (locI p (PlK (3 * n)) a).card = lN p n a := by
    rw [card_locI, card_plc_PlK]; unfold lN; simp
  have hev : Even (locI p (PlK (3 * n)) a).card := by rw [hcard]; exact Nat.even_iff.mpr hP
  obtain ⟨h1, h2⟩ := H.class_bounds ha
  exact ⟨locI_PlK_refl h1 h2 hev, hev⟩

/-- the local pole set of `D_K` at a class of the even group is centred. -/
lemma locIK_sym {a : Fin (p / 2 + 1)} (ha : a ∈ parS p n) :
    (locI p (PlK (40 * n)) a).image refl = locI p (PlK (40 * n)) a ∧
      Even (locI p (PlK (40 * n)) a).card := by
  obtain ⟨ha0, hP⟩ := H.mem_parS ha
  have hcard : (locI p (PlK (40 * n)) a).card = lK p n a := by
    rw [card_locI, card_plc_PlK]; unfold lK; simp
  have hev : Even (locI p (PlK (40 * n)) a).card := by rw [hcard]; exact Nat.even_iff.mpr hP
  obtain ⟨h1, h2⟩ := H.class_bounds ha0
  exact ⟨locI_PlK_refl h1 h2 hev, hev⟩

/-- **The parity data of the even group.** -/
noncomputable def parityData : ParityData (ZMod p) where
  S := ↥(parS p n)
  L a := innerL p n L0 a.1
  P a := lN p n a.1 % 2 = 0
  ext a := a.1 ∈ epsSet p n L0
  T := innerT p n L0
  Bn a := piF (locI p (PlK (3 * n)) a.1) ^ 3
  cc a b := (wsq p a.1 b.1)⁻¹ * (-2 * ((a.1 : ℕ) : ZMod p)) ^ innerL p n L0 a.1 *
    ((-2 * ((b.1 : ℕ) : ZMod p)) ^ (innerL p n L0 b.1 - 1))⁻¹
  δ a := 2 * (locU p (PlK (40 * n)) a.1)⁻¹ * kap (p := p) (n := n) a.1 *
    Ua (p := p) (n := n) (L0 := L0) a.1 ^ 2
  Cf a := fullSym p (locI p (PlK (40 * n)) a.1)
  hL a hP := by
    have h := H.innerL_spec a.1 (H.mem_parS a.2).1
    split_ifs at h ⊢ <;> omega
  hB a hP := by
    obtain ⟨hs, hev⟩ := H.locIN_sym (H.mem_parS a.2).1 hP
    simp only [Jr, pow_comp]
    have := piF_Jr (F := ZMod p) hs hev
    unfold Jr at this
    rw [this]
  hodd a U V := by
    obtain ⟨hs, hev⟩ := H.locIK_sym a.2
    exact fullSym_odd (H.p5) hs hev U V
  h2 := two_ne_zero_zmod H.p_odd

/-- the row scalars `λ_{a,i} = (-2a)^i`. -/
noncomputable def lam (r : (H.parityData (p := p)).Row) : ZMod p :=
  (-2 * ((r.1.1 : ℕ) : ZMod p)) ^ (r.2 : ℕ)

/-- the row of `Fin (p/2+1)`-classes underlying a row of the group. -/
def toRow (r : (H.parityData (p := p)).Row) : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b) :=
  ⟨r.1.1, r.2⟩

/-- `Π_u(a) = ∏_{b ≠ a} (b² - a²)^{ν_u(b)}`. -/
noncomputable def Piu (a : Fin (p / 2 + 1)) (u : Σ b : Fin (p / 2 + 1), Fin (innerL p n L0 b)) :
    ZMod p :=
  ∏ b ∈ Finset.univ.erase a, wsq p a b ^ nu (innerL p n L0) u b

/-- **The local image of a unit row** under a tight condition. -/
lemma Psi_tight (a : (H.parityData (p := p)).S) (r : (H.parityData (p := p)).Row)
    (hc : tcond p n L0 a.1 (H.toRow r)) :
    C (Piu (n := n) (L0 := L0) a.1 (H.toRow r)) *
        (C (-2 * ((a.1 : ℕ) : ZMod p)) * zv) ^ nu (innerL p n L0) (H.toRow r) a.1 *
        piF (locI p (PlK (3 * n)) a.1) ^ 3 =
      C (Ua (p := p) (n := n) (L0 := L0) a.1 * H.lam r) *
        (H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r) := by
  obtain ⟨c, j⟩ := r
  rw [ParityData.Psi_e]
  have hm := H.p_odd
  rcases hc with h | ⟨hA, hC, hj⟩
  · -- own row
    have hca : c = a := Subtype.ext h
    subst hca
    have hnu : nu (innerL p n L0) (H.toRow ⟨c, j⟩) c.1 = (j : ℕ) := by
      simp [nu, toRow]
    have hPi : Piu (n := n) (L0 := L0) c.1 (H.toRow ⟨c, j⟩) = Ua (p := p) (n := n) (L0 := L0) c.1 := by
      unfold Piu Ua
      refine Finset.prod_congr rfl fun b hb => ?_
      have hb' : b ≠ c.1 := Finset.ne_of_mem_erase hb
      simp [nu, toRow, hb']
    have hsc : (if (H.parityData (p := p)).ext c then (0 : (ZMod p)[X]) else
        (if ((H.parityData (p := p)).active c ∧ (H.parityData (p := p)).L c - 1 = j.val) then
          (H.parityData (p := p)).cc c c else 0) • (zv : (ZMod p)[X]) ^ (H.parityData (p := p)).L c)
        = 0 := by
      by_cases he : (H.parityData (p := p)).ext c
      · rw [if_pos he]
      · rw [if_neg he, if_neg (fun h => he h.1.1), zero_smul]
    rw [hsc, if_pos rfl, add_zero, hnu, hPi]
    simp only [lam, parityData, mul_pow, C_mul, C_pow]
    ring
  · -- the top row of an active extra class at a nonextra class
    have hC' : c.1 ∈ epsSet p n L0 := hC
    have hca : c ≠ a := fun h' => hA (h' ▸ hC')
    have hca' : c.1 ≠ a.1 := fun h' => hca (Subtype.ext h')
    have hnu : nu (innerL p n L0) (H.toRow ⟨c, j⟩) a.1 = innerL p n L0 a.1 := by
      simp [nu, toRow, Ne.symm hca']
    have hjl : (j : ℕ) < innerL p n L0 c.1 := j.isLt
    have hj2 : (j : ℕ) + 1 = innerL p n L0 c.1 := hj
    have hj' : innerL p n L0 c.1 - 1 = (j : ℕ) := by omega
    have hPi : Piu (n := n) (L0 := L0) a.1 (H.toRow ⟨c, j⟩) * wsq p a.1 c.1 =
        Ua (p := p) (n := n) (L0 := L0) a.1 := by
      unfold Piu Ua
      have hmem : c.1 ∈ Finset.univ.erase a.1 := Finset.mem_erase.mpr ⟨hca', Finset.mem_univ _⟩
      rw [← Finset.mul_prod_erase _ _ hmem, ← Finset.mul_prod_erase _ _ hmem]
      have e1 : nu (innerL p n L0) (H.toRow ⟨c, j⟩) c.1 = (j : ℕ) := by simp [nu, toRow]
      have e2 : ∏ x ∈ (Finset.univ.erase a.1).erase c.1,
            wsq p a.1 x ^ nu (innerL p n L0) (H.toRow ⟨c, j⟩) x
          = ∏ x ∈ (Finset.univ.erase a.1).erase c.1, wsq p a.1 x ^ innerL p n L0 x := by
        refine Finset.prod_congr rfl fun b hb => ?_
        have hb' : b ≠ c.1 := Finset.ne_of_mem_erase hb
        simp [nu, toRow, hb']
      rw [e1, e2, ← hj2, pow_succ]
      ring
    have hact : (H.parityData (p := p)).active c ∧ (H.parityData (p := p)).L c - 1 = j.val :=
      ⟨⟨hC', by show 0 < innerL p n L0 c.1; omega⟩, hj'⟩
    have hne : ¬ (H.parityData (p := p)).ext a := hA
    rw [if_neg hca.symm, if_neg hne, if_pos hact, hnu, zero_add]
    have hw := wsq_ne (p := p) hm (Ne.symm hca')
    have hc0 := m2a_ne (p := p) hm (H.mem_parS c.2).1
    have hcc : (H.parityData (p := p)).cc a c = (wsq p a.1 c.1)⁻¹ *
        (-2 * ((a.1 : ℕ) : ZMod p)) ^ innerL p n L0 a.1 *
        ((-2 * ((c.1 : ℕ) : ZMod p)) ^ (innerL p n L0 c.1 - 1))⁻¹ := rfl
    rw [hj'] at hcc
    have hlam : H.lam ⟨c, j⟩ = (-2 * ((c.1 : ℕ) : ZMod p)) ^ (j : ℕ) := rfl
    have hBn : (H.parityData (p := p)).Bn a = piF (locI p (PlK (3 * n)) a.1) ^ 3 := rfl
    have hscal : Ua (p := p) (n := n) (L0 := L0) a.1 * H.lam ⟨c, j⟩ *
        (H.parityData (p := p)).cc a c =
        Piu (n := n) (L0 := L0) a.1 (H.toRow ⟨c, j⟩) *
          (-2 * ((a.1 : ℕ) : ZMod p)) ^ innerL p n L0 a.1 := by
      rw [hcc, hlam, ← hPi]
      have hpw : ((-2 * ((c.1 : ℕ) : ZMod p)) ^ (j : ℕ)) ≠ 0 := pow_ne_zero _ hc0
      calc _ = Piu (n := n) (L0 := L0) a.1 (H.toRow ⟨c, j⟩) *
            (-2 * ((a.1 : ℕ) : ZMod p)) ^ innerL p n L0 a.1 *
            (wsq p a.1 c.1 * (wsq p a.1 c.1)⁻¹) *
            ((-2 * ((c.1 : ℕ) : ZMod p)) ^ (j : ℕ) * ((-2 * ((c.1 : ℕ) : ZMod p)) ^ (j : ℕ))⁻¹) := by
            ring
        _ = _ := by rw [mul_inv_cancel₀ hw, mul_inv_cancel₀ hpw]; ring
    rw [smul_eq_C_mul, hBn]
    calc C (Piu (n := n) (L0 := L0) a.1 (H.toRow ⟨c, j⟩)) *
          (C (-2 * ((a.1 : ℕ) : ZMod p)) * zv) ^ innerL p n L0 a.1 *
          piF (locI p (PlK (3 * n)) a.1) ^ 3
        = C (Piu (n := n) (L0 := L0) a.1 (H.toRow ⟨c, j⟩) *
            (-2 * ((a.1 : ℕ) : ZMod p)) ^ innerL p n L0 a.1) *
            (zv ^ innerL p n L0 a.1 * piF (locI p (PlK (3 * n)) a.1) ^ 3) := by
          simp only [mul_pow, C_mul, C_pow]; ring
      _ = C (Ua (p := p) (n := n) (L0 := L0) a.1 * H.lam ⟨c, j⟩ *
            (H.parityData (p := p)).cc a c) *
            (zv ^ innerL p n L0 a.1 * piF (locI p (PlK (3 * n)) a.1) ^ 3) := by rw [hscal]
      _ = _ := by
          have hL : (H.parityData (p := p)).L a = innerL p n L0 a.1 := rfl
          simp only [C_mul, hL]; ring

/-- **The local image of a unit row vanishes off the tight condition.** -/
lemma Psi_zero (a : (H.parityData (p := p)).S) (r : (H.parityData (p := p)).Row)
    (hc : ¬ tcond p n L0 a.1 (H.toRow r)) :
    (H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r) = 0 := by
  obtain ⟨c, j⟩ := r
  rw [ParityData.Psi_e]
  have hca : a ≠ c := fun h => hc (Or.inl (by rw [h]; rfl))
  rw [if_neg hca, zero_add]
  by_cases he : (H.parityData (p := p)).ext a
  · rw [if_pos he, mul_zero]
  · rw [if_neg he, if_neg, zero_smul, mul_zero]
    rintro ⟨⟨hC, _⟩, hj⟩
    apply hc
    refine Or.inr ⟨he, hC, ?_⟩
    have := j.isLt
    simp only [parityData, toRow] at this hj ⊢
    omega

/-- **ZC23 = (H′): the leading entry.** -/
theorem lead_entry (r₁ r₂ : (H.parityData (p := p)).Row) (β : ℤ)
    (hβ : (β : ℚ) = winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) (H.toRow r₁) +
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) (H.toRow r₂) + 4) :
    ∑ c ∈ range p, locSymb p (entA p (40 * n) (3 * n) (innerL p n L0) (H.toRow r₁) (H.toRow r₂))
        (entF p (3 * n) (innerL p n L0) (H.toRow r₁) (H.toRow r₂)) (PlK (40 * n)) β c =
      H.lam r₁ * H.lam r₂ *
        (H.parityData (p := p)).leadL ((H.parityData (p := p)).e r₁) ((H.parityData (p := p)).e r₂) := by
  have hs : (H.toRow r₁).1 ∈ parS p n := r₁.1.2
  have ht : (H.toRow r₂).1 ∈ parS p n := r₂.1.2
  rw [H.sum_locSymb_entry _ _ hs ht β hβ, ParityData.lead_apply, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_coe_sort (parS p n)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha0 := (H.mem_parS a.2).1
  by_cases hc : tcond p n L0 a.1 (H.toRow r₁) ∧ tcond p n L0 a.1 (H.toRow r₂)
  · rw [if_pos hc]
    rw [locN_entry H.p5 H.p_odd (40 * n) (3 * n) (innerL p n L0) _ _ a.1 ha0]
    have h1 := H.Psi_tight a r₁ hc.1
    have h2 := H.Psi_tight a r₂ hc.2
    have hW : C ((-1 : ZMod p) ^ (40 * n) * ((a.1 : ℕ) : ZMod p) ^ 5 *
          locU p (PlK (3 * n)) a.1 ^ 6 *
          (∏ b ∈ Finset.univ.erase a.1, (((b : ℕ) : ZMod p) ^ 2 - ((a.1 : ℕ) : ZMod p) ^ 2) ^
            nu (innerL p n L0) (H.toRow r₁) b) *
          (∏ b ∈ Finset.univ.erase a.1, (((b : ℕ) : ZMod p) ^ 2 - ((a.1 : ℕ) : ZMod p) ^ 2) ^
            nu (innerL p n L0) (H.toRow r₂) b)) *
        piF (locI p (PlK (3 * n)) a.1) ^ 6 *
        (C (-2 * ((a.1 : ℕ) : ZMod p)) * zv) ^
          (nu (innerL p n L0) (H.toRow r₁) a.1 + nu (innerL p n L0) (H.toRow r₂) a.1) =
        (kap (p := p) (n := n) a.1 * (Ua (p := p) (n := n) (L0 := L0) a.1 * H.lam r₁) *
          (Ua (p := p) (n := n) (L0 := L0) a.1 * H.lam r₂)) •
          ((H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₁) * (H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₂)) := by
      calc _ = C (kap (p := p) (n := n) a.1) *
            (C (Piu (n := n) (L0 := L0) a.1 (H.toRow r₁)) *
              (C (-2 * ((a.1 : ℕ) : ZMod p)) * zv) ^ nu (innerL p n L0) (H.toRow r₁) a.1 *
              piF (locI p (PlK (3 * n)) a.1) ^ 3) *
            (C (Piu (n := n) (L0 := L0) a.1 (H.toRow r₂)) *
              (C (-2 * ((a.1 : ℕ) : ZMod p)) * zv) ^ nu (innerL p n L0) (H.toRow r₂) a.1 *
              piF (locI p (PlK (3 * n)) a.1) ^ 3) := by
            unfold kap Piu wsq
            simp only [C_mul]
            ring
        _ = _ := by
            rw [h1, h2, smul_eq_C_mul]
            simp only [C_mul]
            ring
    rw [hW, locSym_smul]
    have hδ : (H.parityData (p := p)).δ a = 2 * (locU p (PlK (40 * n)) a.1)⁻¹ * kap (p := p) (n := n) a.1 *
        Ua (p := p) (n := n) (L0 := L0) a.1 ^ 2 := rfl
    have hCf : (H.parityData (p := p)).Cf a ((H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₁)) ((H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₂)) =
        locSym p (locI p (PlK (40 * n)) a.1) ((H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₁) * (H.parityData (p := p)).PsiL a ((H.parityData (p := p)).e r₂)) := rfl
    rw [hδ, hCf]
    ring
  · rw [if_neg hc, mul_zero]
    rcases not_and_or.mp hc with h | h
    · rw [H.Psi_zero a r₁ h, map_zero, LinearMap.zero_apply, mul_zero, mul_zero]
    · rw [H.Psi_zero a r₂ h, map_zero, mul_zero, mul_zero]

end InnerHyp

end Apery
