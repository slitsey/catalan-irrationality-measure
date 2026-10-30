module

public import CatalanCore.Uniform.Bank.Chi3Rank.Pair

@[expose] public section
set_option Elab.async false

/-! # Paired row-kill / column-kill certificates: the member (lane H, H16) -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer

open scoped Classical

/-- **Paired certificates give price `2h - 2|YE|`.** -/
theorem pair_member {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (Fr : Frame) (u q : Fin Fr.d → ℕ) (common : ι → ℕ) (xs ys : κ → ℕ) (T : Finset ι)
    (p : ℕ) [Fact p.Prime] (B : ℕ)
    (hcoef : ∀ j, (frameDigamma Fr u q).c j ∈ S p) (hpq : ∀ j, ¬ p ∣ (frameDigamma Fr u q).q j)
    (hp3 : 3 ≤ p) (hbd : ∀ j, (frameDigamma Fr u q).q j * B + (frameDigamma Fr u q).u j ≤ p ^ 2)
    (hB : B < p ^ 2) (ha : ∀ i, memberRows common xs T i ≤ B)
    (hb : ∀ j, memberCols common ys T j ≤ B)
    (hia : Function.Injective (memberRows common xs T))
    (hib : Function.Injective (memberCols common ys T))
    (Ec Oc : FibreCert) (YE YO : Finset (ZMod p))
    (hEok : Ec.Ok) (hOok : Oc.Ok) (hEint : Ec.Integral p) (hOint : Oc.Integral p)
    (hEkr : Ec.kr = {0}) (hEkc : Ec.kc = ∅) (hOkr : Oc.kr = ∅) (hOkc : Oc.kc = {0})
    (hdisj : Disjoint YE YO) (hcardEO : YE.card = YO.card)
    (hEreal : ∀ x ∈ YE, Realizes ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) x Ec)
    (hOreal : ∀ x ∈ YO, Realizes ((frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd)
      (memberRows common xs T) (memberCols common ys T) x Oc)
    (hload : Ec.rload 0 = Oc.cload 0) (hnz : castV p (Oc.cload 0) ≠ 0) :
    ∃ M : RankMember Fr u q common xs ys T p,
      M.price + 2 * YE.card ≤ 2 * Fintype.card (T ⊕ κ) := by
  classical
  set PS := (frameDigamma Fr u q).poleSplit B hcoef hpq hp3 hbd with hPS
  set a := memberRows common xs T with ha_
  set b := memberCols common ys T with hb_
  have hd : DigitHyp p B a b := digitHyp_of_lt ha hb hB
  set cert := pairCert PS a b Ec Oc YE YO with hcert
  have h0E : 0 ∈ Ec.R := hEok.kr_sub (by rw [hEkr]; simp)
  have h0O : 0 ∈ Oc.C := hOok.kc_sub (by rw [hOkc]; simp)
  have hcE : ∀ x ∈ YE, cert x = Ec := fun x hx => pairCert_E PS a b Ec Oc YE YO hx
  have hcO : ∀ x ∈ YO, cert x = Oc := fun x hx => pairCert_O PS a b Ec Oc YE YO hdisj hx
  have hcT : ∀ x, x ∉ YE → x ∉ YO → cert x = trivCert PS a b x :=
    fun x h1 h2 => pairCert_T PS a b Ec Oc YE YO h1 h2
  have hOk : ∀ x, (cert x).Ok := by
    intro x
    by_cases h1 : x ∈ YE
    · rw [hcE x h1]; exact hEok
    by_cases h2 : x ∈ YO
    · rw [hcO x h2]; exact hOok
    rw [hcT x h1 h2]; exact FibreCert.triv_ok _ _ _ _
  have hInt : ∀ x, (cert x).Integral p := by
    intro x
    by_cases h1 : x ∈ YE
    · rw [hcE x h1]; exact hEint
    by_cases h2 : x ∈ YO
    · rw [hcO x h2]; exact hOint
    rw [hcT x h1 h2]; exact FibreCert.triv_integral _ _ _ _
  have hReal : ∀ x, Realizes PS a b x (cert x) := by
    intro x
    by_cases h1 : x ∈ YE
    · rw [hcE x h1]; exact hEreal x h1
    by_cases h2 : x ∈ YO
    · rw [hcO x h2]; exact hOreal x h2
    rw [hcT x h1 h2]; exact trivCert_realizes PS a b x
  have hKR : (killRows (p := p) a cert).card = YE.card := by
    refine Finset.card_bij (fun i _ => (a i : ZMod p)) ?_ ?_ ?_
    · intro i hi
      exact (pairCert_kr PS a b Ec Oc YE YO hEkr hOkr _ _ (Finset.mem_filter.1 hi).2).1
    · intro i1 hi1 i2 hi2 h
      have k1 := (pairCert_kr PS a b Ec Oc YE YO hEkr hOkr _ _ (Finset.mem_filter.1 hi1).2).2
      have k2 := (pairCert_kr PS a b Ec Oc YE YO hEkr hOkr _ _ (Finset.mem_filter.1 hi2).2).2
      exact hia (node_eq_of_digit h (k1.trans k2.symm))
    · intro x hx
      obtain ⟨i, hi, hd0⟩ := (hEreal x hx).r_cov 0 h0E
      refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hi⟩
      show a i / p ∈ (cert (a i : ZMod p)).kr
      rw [hi, hcE x hx, hEkr, hd0]; simp
  have hKC : (killCols (p := p) b cert).card = YO.card := by
    refine Finset.card_bij (fun i _ => (b i : ZMod p)) ?_ ?_ ?_
    · intro i hi
      exact (pairCert_kc PS a b Ec Oc YE YO hEkc hOkc _ _ (Finset.mem_filter.1 hi).2).1
    · intro i1 hi1 i2 hi2 h
      have k1 := (pairCert_kc PS a b Ec Oc YE YO hEkc hOkc _ _ (Finset.mem_filter.1 hi1).2).2
      have k2 := (pairCert_kc PS a b Ec Oc YE YO hEkc hOkc _ _ (Finset.mem_filter.1 hi2).2).2
      exact hib (node_eq_of_digit h (k1.trans k2.symm))
    · intro x hx
      obtain ⟨i, hi, hd0⟩ := (hOreal x hx).c_cov 0 h0O
      refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, hi⟩
      show b i / p ∈ (cert (b i : ZMod p)).kc
      rw [hi, hcO x hx, hOkc, hd0]; simp
  have hcard : (killRows (p := p) a cert).card = (killCols (p := p) b cert).card := by
    rw [hKR, hKC, hcardEO]
  set BK := BKc PS a b hd hia hib cert hOk hInt hReal hcard with hBK
  have hs : BK.s = killRows (p := p) a cert := by
    ext i
    simp only [hBK, BKc, blockKernelOfCerts, BlockKernel.s, Finset.mem_filter, Finset.mem_univ,
      true_and, killRows]
    exact Iff.rfl
  set Vs : Submodule (RatFunc (ZMod p)) (RatFunc (ZMod p) × RatFunc (ZMod p)) :=
    Submodule.span _ {castV p (Oc.cload 0)} with hVs
  have hfin : finrank (RatFunc (ZMod p)) Vs = 1 := finrank_span_singleton hnz
  have hUc : Ucol p Oc = Vs := by simp [Ucol, hOkc, hVs]
  have hUr : Vs ≤ Urow p Ec := by
    unfold Urow
    simp only [hEkr, Finset.mem_singleton, iInf_iInf_eq_left]
    intro v hv
    rw [hVs, Submodule.mem_span_singleton] at hv
    obtain ⟨c, rfl⟩ := hv
    rw [LinearMap.mem_ker, hload, omegaL_apply]
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  have hcolsub : ∀ x ∈ colFib PS a b hd hia hib cert hOk hInt hReal hcard, x ∈ YO := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hx
    have hsc : BK.perm j.1 ∈ BK.sc := (BK.perm_mem j.1).2 j.2
    have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 hsc).2).2
    exact (pairCert_kc PS a b Ec Oc YE YO hEkc hOkc _ _ h1).1
  have hrowsub : ∀ x ∈ rowFib PS a b hd hia hib cert hOk hInt hReal hcard, x ∈ YE := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 i.2).2).2
    exact (pairCert_kr PS a b Ec Oc YE YO hEkr hOkr _ _ h1).1
  have hYOsub : YO ⊆ colFib PS a b hd hia hib cert hOk hInt hReal hcard := by
    intro x hx
    obtain ⟨l0, hl0, hl0d⟩ := (hOreal x hx).c_cov 0 h0O
    have hsc : l0 ∈ BK.sc := by
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩
      show b l0 / p ∈ (cert (b l0 : ZMod p)).kc
      rw [hl0, hcO x hx, hOkc, hl0d]; simp
    have hjs : BK.perm.symm l0 ∈ BK.s :=
      (BK.perm_mem _).1 (by rw [Equiv.apply_symm_apply]; exact hsc)
    refine Finset.mem_image.2 ⟨⟨_, hjs⟩, Finset.mem_univ _, ?_⟩
    show (erOf b p (BK.perm (BK.perm.symm l0))).1 = x
    rw [Equiv.apply_symm_apply]
    exact hl0
  refine ⟨⟨B, hcoef, hpq, hp3, hbd, hB, ha, hb, hia, hib, cert, hOk, hInt, hReal, hcard, Vs,
    fun _ => 1, fun _ => 1, fun x => by rw [hfin], fun x => by rw [hfin], ?_, ?_⟩, ?_⟩
  · intro x hx
    have hx' := hcolsub x hx
    show 1 ≤ _
    rw [hcO x hx', hUc, inf_idem, hfin]
  · intro x hx
    have hx' := hrowsub x hx
    show 1 ≤ _
    rw [hcE x hx', inf_eq_left.2 hUr, hfin]
  · unfold RankMember.price
    refine price_arith _ _ _ _ _ _ ?_ ?_ ?_ ?_
    · exact hs ▸ hKR
    · rw [← hKR]; exact Finset.card_le_univ _
    · have := Finset.card_le_card hYOsub
      simpa [hcardEO] using this
    · exact Finset.sum_eq_zero fun x _ => by simp [hfin]

end CatalanCore.Uniform.Bank.Chi3Rank
