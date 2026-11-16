module

public import CatalanCore.Zeta5.Padic.Lead

@[expose] public section

/-!
# ZC06(b), part 4: the residue part and the leading term of `τ_X`

`red_local_res`: for a pole `r = c + p k` the scaled residue term `p^{4-β} res_r H⁽⁵⁾_{d(r)}` is
integral and reduces to `[tight] ū_c⁻¹ ā_c(k) / ∏_{k' ≠ k} (k - k') · H⁽⁵⁾_{d(k)}`.

`tauX_lead`: **the leading term of `τ_X` modulo `p`** (theorem (A) of the notes).
-/

open Finset Polynomial

namespace Apery

section tlead
variable {p : ℕ} [hp : Fact p.Prime]

lemma eval_Gc (c : ℕ) (k : ℤ) : (Gc p c).eval (k : ℚ) = (((c : ℤ) + p * k : ℤ) : ℚ) := by
  simp [Gc]

/-- the regrouping of the poles by residue classes. -/
lemma sum_Pl_classes {M : Type*} [AddCommMonoid M] (Pl : Finset ℤ) (f : ℤ → M) :
    ∑ r ∈ Pl, f r = ∑ c ∈ range p, ∑ r ∈ plc p Pl (c : ZMod p), f r := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun r : ℤ => (r : ZMod p).val) (t := range p)
    (fun r _ => Finset.mem_range.mpr (ZMod.val_lt _))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc' := Finset.mem_range.mp hc
  unfold plc
  refine Finset.sum_congr (Finset.filter_congr fun r _ => ?_) fun _ _ => rfl
  constructor
  · intro h; rw [← h, ZMod.natCast_zmod_val]
  · intro h; rw [h, ZMod.val_cast_of_lt hc']

/-- **The residue terms at a residue.** -/
theorem red_local_res (A : ℚ[X]) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (Pl : Finset ℤ) (hsep : Sep p Pl) (β : ℤ)
    (hβ : ∀ c : ZMod p, (β : ℚ) ≤ (eF c : ℚ) - (plc p Pl c).card) (c : ℕ) (hc : c < p)
    {r : ℤ} (hr : r ∈ plc p Pl (c : ZMod p)) (hH : dd r < p ^ 2) :
    VG p ((p : ℚ) ^ (4 - β) * (resP A Pl r * H5 (dd r))) 0 ∧
      (((p : ℚ) ^ (4 - β) * (resP A Pl r * H5 (dd r)) : ℚ) : ZMod p) =
        tind p eF Pl β c * (locU p Pl c)⁻¹ *
          ((locN p A (eF (c : ZMod p)) c).eval ((kloc p c r : ℤ) : ZMod p) /
            (∏ s ∈ (locI p Pl c).erase (kloc p c r), (((kloc p c r : ℤ) : ZMod p) - (s : ZMod p))) *
              H5w (ZMod p) (kloc p c r)) := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hr' := mem_plc_spec (p := p) hr
  set k := kloc p c r with hk
  have hrk : (r : ℚ) = (((c : ℤ) + p * k : ℤ) : ℚ) := by exact_mod_cast hr'.2.2
  have hℓ1 : 1 ≤ (plc p Pl (c : ZMod p)).card := Finset.card_pos.mpr ⟨r, hr⟩
  set ℓ := (plc p Pl (c : ZMod p)).card with hℓ
  set e := eF (c : ZMod p) with he
  -- the denominator of the residue
  have hden : ∏ s ∈ Pl.erase r, ((r : ℚ) - s) = (p : ℚ) ^ (ℓ - 1) *
      (piF ((locI p Pl c).erase k) : ℚ[X]).eval (k : ℚ) * (farP p Pl c).eval (k : ℚ) := by
    have h1 := congrArg (fun F => F.eval (k : ℚ)) (prod_comp_Gc (p := p) (Pl.erase r) c)
    simp only [eval_comp, eval_mul, eval_C] at h1
    rw [eval_Gc, ← hrk, eval_prod] at h1
    simp only [eval_sub, eval_X, eval_C] at h1
    rw [h1, plc_erase, Finset.card_erase_of_mem hr, image_erase_kloc hr]
    unfold farP
    rw [plo_erase_of_plc hr]
  -- the numerator
  set N := C ((p : ℚ) ^ (-(e : ℤ))) * A.comp (Gc p c) with hN
  have hNi : GV p N 0 := GV_locNum (hAloc_nat hAloc c)
  have hAr : A.eval (r : ℚ) = (p : ℚ) ^ (e : ℤ) * N.eval (k : ℚ) := by
    rw [hN, eval_mul, eval_C, eval_comp, eval_Gc, ← hrk, ← mul_assoc, ← zpow_add₀ hp0]; simp
  set D1 := (piF ((locI p Pl c).erase k) : ℚ[X]).eval (k : ℚ) with hD1
  set D2 := (farP p Pl c).eval (k : ℚ) with hD2
  set H := (p : ℚ) ^ 5 * H5 (dd r) with hHd
  have hdd : dd r = dd ((c : ℤ) + p * k) := congrArg dd hr'.2.2
  -- the factorisation
  have hfac : (p : ℚ) ^ (4 - β) * (resP A Pl r * H5 (dd r)) =
      (p : ℚ) ^ ((e : ℤ) - ℓ - β) * N.eval (k : ℚ) * D1⁻¹ * D2⁻¹ * H := by
    rw [resP, hden, hAr, hHd]
    have hpow : (p : ℚ) ^ (4 - β) * ((p : ℚ) ^ (ℓ - 1))⁻¹ * (p : ℚ) ^ (e : ℤ) =
        (p : ℚ) ^ ((e : ℤ) - ℓ - β) * (p : ℚ) ^ 5 := by
      rw [← zpow_natCast, ← zpow_neg, ← zpow_add₀ hp0, ← zpow_add₀ hp0, ← zpow_natCast,
        ← zpow_add₀ hp0]
      congr 1; push_cast [hℓ1]; ring
    rw [div_eq_mul_inv, mul_inv, mul_inv]
    linear_combination (N.eval (k : ℚ) * D1⁻¹ * D2⁻¹ * H5 (dd r)) * hpow
  -- the valuations of the factors
  have hβc := hβ (c : ZMod p)
  have hd0 : 0 ≤ (e : ℤ) - ℓ - β := by
    have h' : β ≤ (e : ℤ) - ℓ := by exact_mod_cast (show (β : ℚ) ≤ (e : ℚ) - ℓ from hβc)
    omega
  have hPw : VG p ((p : ℚ) ^ ((e : ℤ) - ℓ - β)) 0 :=
    (VG.primePow (p := p) _).mono (by exact_mod_cast hd0)
  have hPr : (((p : ℚ) ^ ((e : ℤ) - ℓ - β) : ℚ) : ZMod p) = tind p eF Pl β c := by
    unfold tind
    rw [← he, ← hℓ]
    by_cases h : (e : ℤ) - ℓ = β
    · rw [if_pos h, show (e : ℤ) - ℓ - β = 0 by omega]; simp
    · rw [if_neg h]
      exact red_zero_of_VG_one ((VG.primePow (p := p) _).mono (by
        have : (1 : ℤ) ≤ (e : ℤ) - ℓ - β := by omega
        exact_mod_cast this))
  have hNk : VG p (N.eval (k : ℚ)) 0 := VG_eval_int hNi k
  have hNr : ((N.eval (k : ℚ) : ℚ) : ZMod p) = (locN p A e c).eval ((k : ℤ) : ZMod p) := by
    rw [redP_eval hNi (VG.intCast k)]; simp [locN, hN]
  -- `D1`
  have hunit1 : ∀ s ∈ (locI p Pl c).erase k, ¬ (p : ℤ) ∣ k - s := by
    intro s hs
    obtain ⟨hsk, hs⟩ := Finset.mem_erase.mp hs
    obtain ⟨r', hr'', rfl⟩ := Finset.mem_image.mp hs
    exact locI_sub_unit hsep hr hr'' (fun h => hsk (by rw [hk, h]))
  have hD1e : D1 = ∏ s ∈ (locI p Pl c).erase k, (((k - s : ℤ)) : ℚ) := by
    rw [hD1, piF, eval_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp
  have hD1i : VG p D1⁻¹ 0 := by
    rw [hD1e, ← Finset.prod_inv_distrib]
    have := VG.prod (p := p) ((locI p Pl c).erase k) (r := fun _ => (0 : ℚ))
      (fun s hs => VG_inv_int_unit (hunit1 s hs))
    simpa using this
  have hD1r : ((D1⁻¹ : ℚ) : ZMod p) =
      (∏ s ∈ (locI p Pl c).erase k, (((k : ℤ) : ZMod p) - (s : ZMod p)))⁻¹ := by
    rw [hD1e, ← Finset.prod_inv_distrib, red_prod _ _ fun s hs => VG_inv_int_unit (hunit1 s hs),
      ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [red_inv (by simpa using VG.intCast (p := p) (k - s)) (VG_inv_int_unit (hunit1 s hs)),
      red_intCast]
    push_cast; ring
  -- `D2`
  have hD2e : D2 = ∏ s ∈ plo p Pl c, ((((c : ℤ) - s + p * k : ℤ)) : ℚ) := by
    rw [hD2, farP, eval_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp
  have hD2i : VG p D2⁻¹ 0 := by
    rw [hD2e, ← Finset.prod_inv_distrib]
    have := VG.prod (p := p) (plo p Pl c) (r := fun _ => (0 : ℚ))
      (fun s hs => VG_inv_int_unit (plo_unit hs k))
    simpa using this
  have hD2r : ((D2⁻¹ : ℚ) : ZMod p) = (locU p Pl c)⁻¹ := by
    rw [hD2e, ← Finset.prod_inv_distrib, red_prod _ _ fun s hs => VG_inv_int_unit (plo_unit hs k),
      locU, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun s hs => ?_
    rw [red_inv (by simpa using VG.intCast (p := p) ((c : ℤ) - s + p * k))
      (VG_inv_int_unit (plo_unit hs k)), red_intCast]
    push_cast; rw [ZMod.natCast_self]; ring
  -- `H`
  obtain ⟨hHi, hHr⟩ := H5_local (p := p) hc (k := k) (by rw [← hdd]; exact hH)
  rw [← hdd] at hHi hHr
  -- assemble
  have h12 := hPw.mul hNk
  have h123 := h12.mul hD1i
  have h1234 := h123.mul hD2i
  refine ⟨?_, ?_⟩
  · rw [hfac]; simpa using h1234.mul hHi
  · rw [hfac, red_mul (by simpa using h1234) hHi, red_mul (by simpa using h123) hD2i,
      red_mul (by simpa using h12) hD1i, red_mul hPw hNk, hPr, hNr, hD1r, hD2r, ← hHd, hHr]
    ring

/-- `τ_X(A/Π) = C(τ(Q) + ∑ res_r H⁽⁵⁾_{d(r)}) - C(∑ res_r) X`. -/
lemma tauX_eq (A : ℚ[X]) (Pl : Finset ℤ) :
    tauX A Pl = C (tau (polyPart A Pl) + ∑ r ∈ Pl, resP A Pl r * H5 (dd r)) -
      C (∑ r ∈ Pl, resP A Pl r) * X := by
  rw [tauX, C_add, map_sum, map_sum, Finset.sum_mul]
  simp only [C_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Theorem (A): the leading term of `τ_X` modulo `p`.** -/
theorem tauX_lead (hp5 : 5 ≤ p) (A : ℚ[X]) (eF : ZMod p → ℕ)
    (hAloc : ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (eF (m : ZMod p)))
    (Pl : Finset ℤ) (hsep : Sep p Pl) (hH : ∀ r ∈ Pl, dd r < p ^ 2)
    (hdeg : A.natDegree - Pl.card + 1 < p ^ 2)
    (β : ℤ) (hβ : ∀ c : ZMod p, (β : ℚ) ≤ (eF c : ℚ) - (plc p Pl c).card) :
    VG p ((p : ℚ) ^ (4 - β) * (tau (polyPart A Pl) + ∑ r ∈ Pl, resP A Pl r * H5 (dd r))) 0 ∧
      ((((p : ℚ) ^ (4 - β) * (tau (polyPart A Pl) + ∑ r ∈ Pl, resP A Pl r * H5 (dd r)) : ℚ))
        : ZMod p) = ∑ c ∈ range p, locSymb p A eF Pl β c ∧
      VG p (∑ r ∈ Pl, resP A Pl r) (β + 1) := by
  classical
  -- the polynomial part
  have hQdeg : (polyPart A Pl).natDegree < p ^ 2 :=
    lt_of_le_of_lt (natDegree_polyPart_le A Pl) (by omega)
  have hv : ∀ m : ℕ, VG p ((polyPart A Pl).eval (m : ℚ)) β := fun m => by
    have := VG_polyPart_eval_gen A eF hAloc Pl hsep (β : ℚ) hβ (m : ℤ)
    simpa using this
  obtain ⟨hP0, hPr⟩ := tau_lead_poly hp5 hQdeg hv
    (fun c => C ((locU p Pl c)⁻¹ * tind p eF Pl β c) *
      (locN p A (eF (c : ZMod p)) c /ₘ piF (locI p Pl c)))
    (fun c hc => (redP_local_polyPart A eF hAloc Pl hsep hdeg β hβ c hc).2)
  -- the residue part
  have hR : (p : ℚ) ^ (4 - β) * ∑ r ∈ Pl, resP A Pl r * H5 (dd r) =
      ∑ c ∈ range p, ∑ r ∈ plc p Pl (c : ZMod p), (p : ℚ) ^ (4 - β) * (resP A Pl r * H5 (dd r)) := by
    rw [Finset.mul_sum, sum_Pl_classes (p := p)]
  have hloc := fun c (hc : c ∈ range p) r (hr : r ∈ plc p Pl (c : ZMod p)) =>
    red_local_res A eF hAloc Pl hsep β hβ c (Finset.mem_range.mp hc) hr
      (hH r (mem_plc_spec hr).1)
  have hR0 : VG p ((p : ℚ) ^ (4 - β) * ∑ r ∈ Pl, resP A Pl r * H5 (dd r)) 0 := by
    rw [hR]; exact VG.sum _ fun c hc => VG.sum _ fun r hr => (hloc c hc r hr).1
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_add]; exact hP0.add hR0
  · rw [mul_add, red_add hP0 hR0, hPr, hR,
      red_sum _ _ fun c hc => VG.sum _ fun r hr => (hloc c hc r hr).1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [red_sum _ _ fun r hr => (hloc c hc r hr).1,
      Finset.sum_congr rfl fun r hr => (hloc c hc r hr).2]
    unfold locSymb locSym resSym
    rw [← smul_eq_C_mul, polySym_smul, locI,
      Finset.sum_image (fun a ha b hb h => kloc_injOn Pl c ha hb h)]
    rw [mul_add, Finset.mul_sum]
    congr 1
    ring
  · refine VG.sum _ fun r hr => ?_
    have h1 := VG_res_gen A eF hAloc Pl hsep hr
    refine h1.mono ?_
    have := hβ (r : ZMod p)
    push_cast; linarith

end tlead

end Apery
