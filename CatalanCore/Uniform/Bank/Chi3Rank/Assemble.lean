import CatalanCore.Uniform.Bank.Chi3Rank.Count
import CatalanCore.Uniform.Bank.Chi3Rank.Certs
set_option Elab.async false

/-! # Assembling the chi3 rank member from an interval of typed fibres (lane H, H16) -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer CatalanFrames.P6

theorem mem_S_of_den (p : ℕ) [Fact p.Prime] (v : ℚ) (hv : v.den ∣ N0) (hp : N0 < p) :
    v ∈ S p := by
  intro hd
  have : p ≤ N0 := Nat.le_of_dvd (by norm_num [N0]) (hd.trans hv)
  omega

theorem parity_ge' (lo hi pe : ℕ) (hpe : pe < 2) :
    (hi - lo) / 2 ≤ ((Ico lo hi).filter (fun x => x % 2 = pe)).card ∧
    (hi - lo) / 2 ≤ ((Ico lo hi).filter (fun x => x % 2 ≠ pe)).card := by
  obtain ⟨h1, h0⟩ := parity_ge lo hi
  interval_cases pe
  · refine ⟨h0, ?_⟩
    have : (Ico lo hi).filter (fun x => x % 2 ≠ 0) = (Ico lo hi).filter (fun x => x % 2 = 1) :=
      Finset.filter_congr (fun x _ => by omega)
    rw [this]; exact h1
  · refine ⟨h1, ?_⟩
    have : (Ico lo hi).filter (fun x => x % 2 ≠ 1) = (Ico lo hi).filter (fun x => x % 2 = 0) :=
      Finset.filter_congr (fun x _ => by omega)
    rw [this]; exact h0

theorem natCast_inj_of_lt {p x y : ℕ} [Fact p.Prime] (hx : x < p) (hy : y < p)
    (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  have := natCast_eq_of_mod h
  rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

open Classical in
theorem assemble (r m p : ℕ) [hp : Fact p.Prime] (s : Finset (Fin r)) (Ec Oc : FibreCert)
    (lo hi pe : ℕ) (P : ℕ → Prop) (hpe : pe < 2)
    (hp6 : p % 6 = 1 ∨ p % 6 = 5) (hN : N0 < p) (hbig : 3 * (r + 2 * m) + 1 ≤ p ^ 2)
    (hhi : hi ≤ p)
    (hP : ∀ x, lo ≤ x → x < hi → ¬ P x → ∃ v, v < r ∧ ¬ keptN r s v ∧ v % p = x)
    (hEok : Ec.Ok) (hOok : Oc.Ok) (hEden : DenOk Ec) (hOden : DenOk Oc)
    (hEkr : Ec.kr = {0}) (hEkc : Ec.kc = ∅) (hOkr : Oc.kr = ∅) (hOkc : Oc.kc = {0})
    (hEr : ∀ x0, lo ≤ x0 → x0 < hi → x0 % 2 = pe → P x0 →
      ∀ PS : PoleSplit p (r + 2 * m) Dchi.f Dchi.e, PS.Lf = Dchi.Lf p → PS.E = Dchi.E p →
        Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) Ec)
    (hOr : ∀ x0, lo ≤ x0 → x0 < hi → x0 % 2 ≠ pe → P x0 →
      ∀ PS : PoleSplit p (r + 2 * m) Dchi.f Dchi.e, PS.Lf = Dchi.Lf p → PS.E = Dchi.E p →
        Realizes PS (rowsOf r m s) (colsOf r m s) (x0 : ZMod p) Oc)
    (hload : Ec.rload 0 = Oc.cload 0) (hnz : castV p (Oc.cload 0) ≠ 0) :
    ∃ M : RankMember p6Frame u3 q3 (fun c : Fin r => (c : ℕ))
        (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      M.price + (hi - lo) ≤ 2 * r + 2 * m + 1 := by
  obtain ⟨h2, h3⟩ := not_dvd_of_mod6 p hp6
  have hc0 : Dchi.c 0 ∈ S p := by
    rw [Dchi_c0]; exact mem_S_of_den p _ (by decide +kernel) hN
  have hc1 : Dchi.c 1 ∈ S p := by
    rw [Dchi_c1]; exact mem_S_of_den p _ (by decide +kernel) hN
  have hc2 : Dchi.c 2 ∈ S p := by
    rw [Dchi_c2]; exact mem_S_of_den p _ (by decide +kernel) hN
  have hcoef : ∀ j, (frameDigamma p6Frame u3 q3).c j ∈ S p := by
    intro j
    fin_cases j
    · exact hc0
    · exact hc1
    · exact hc2
  have hpq : ∀ j, ¬ p ∣ (frameDigamma p6Frame u3 q3).q j := by
    intro j
    fin_cases j
    · exact hp.out.not_dvd_one
    · exact h3
    · exact h2
  have hp3 : 3 ≤ p := by unfold N0 at hN; omega
  have hbd : ∀ j, (frameDigamma p6Frame u3 q3).q j * (r + 2 * m) +
      (frameDigamma p6Frame u3 q3).u j ≤ p ^ 2 := by
    intro j
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = p ^ 2 := ⟨_, rfl⟩
    rw [← hQ] at hbig ⊢
    fin_cases j
    · show 1 * (r + 2 * m) + 1 ≤ Q
      omega
    · show 3 * (r + 2 * m) + 1 ≤ Q
      omega
    · show 2 * (r + 2 * m) + 1 ≤ Q
      omega
  have hB : r + 2 * m < p ^ 2 := by omega
  have ha : ∀ i, memberRows (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ)) s i
      ≤ r + 2 * m := rows_le r m s
  have hb : ∀ i, memberCols (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s i
      ≤ r + 2 * m := cols_le r m s
  -- the fibre sets
  set A := Ico lo hi with hA
  set AE := A.filter (fun x => x % 2 = pe) with hAE
  set AO := A.filter (fun x => x % 2 ≠ pe) with hAO
  set IE := AE.filter P with hIE
  set IO := AO.filter P with hIO
  have hcE : AE.card ≤ IE.card + (r - s.card) :=
    card_good r p s AE P (fun x hx hnp => hP x (Finset.mem_Ico.1 (Finset.mem_filter.1 hx).1).1
      (Finset.mem_Ico.1 (Finset.mem_filter.1 hx).1).2 hnp)
  have hcO : AO.card ≤ IO.card + (r - s.card) :=
    card_good r p s AO P (fun x hx hnp => hP x (Finset.mem_Ico.1 (Finset.mem_filter.1 hx).1).1
      (Finset.mem_Ico.1 (Finset.mem_filter.1 hx).1).2 hnp)
  have hpE : (hi - lo) / 2 ≤ AE.card := (parity_ge' lo hi pe hpe).1
  have hpO : (hi - lo) / 2 ≤ AO.card := (parity_ge' lo hi pe hpe).2
  obtain ⟨IE', hIE'sub, hIE'card⟩ := Finset.exists_subset_card_eq (s := IE)
    (n := min IE.card IO.card) (min_le_left _ _)
  obtain ⟨IO', hIO'sub, hIO'card⟩ := Finset.exists_subset_card_eq (s := IO)
    (n := min IE.card IO.card) (min_le_right _ _)
  have hbnd : ∀ x ∈ IE' ∪ IO', lo ≤ x ∧ x < hi := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h
    · exact Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_filter.1 (hIE'sub h)).1).1
    · exact Finset.mem_Ico.1 (Finset.mem_filter.1 (Finset.mem_filter.1 (hIO'sub h)).1).1
  set YE : Finset (ZMod p) := IE'.image (fun x : ℕ => (x : ZMod p)) with hYE
  set YO : Finset (ZMod p) := IO'.image (fun x : ℕ => (x : ZMod p)) with hYO
  have hinj : ∀ x ∈ IE' ∪ IO', ∀ y ∈ IE' ∪ IO', (x : ZMod p) = (y : ZMod p) → x = y := by
    intro x hx y hy h
    exact natCast_inj_of_lt (lt_of_lt_of_le (hbnd x hx).2 hhi) (lt_of_lt_of_le (hbnd y hy).2 hhi) h
  have hYEcard : YE.card = min IE.card IO.card := by
    rw [hYE, Finset.card_image_of_injOn (fun x hx y hy h => hinj x (Finset.mem_union_left _ hx) y
      (Finset.mem_union_left _ hy) h), hIE'card]
  have hYOcard : YO.card = min IE.card IO.card := by
    rw [hYO, Finset.card_image_of_injOn (fun x hx y hy h => hinj x (Finset.mem_union_right _ hx) y
      (Finset.mem_union_right _ hy) h), hIO'card]
  have hdisj : Disjoint YE YO := by
    rw [Finset.disjoint_left]
    intro z hzE hzO
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hzE
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hzO
    have := hinj y (Finset.mem_union_right _ hy) x (Finset.mem_union_left _ hx) hxy
    subst this
    have h1 := (Finset.mem_filter.1 (Finset.mem_filter.1 (hIE'sub hx)).1).2
    have h2' := (Finset.mem_filter.1 (Finset.mem_filter.1 (hIO'sub hy)).1).2
    exact h2' h1
  have hEreal : ∀ x ∈ YE, Realizes ((frameDigamma p6Frame u3 q3).poleSplit (r + 2 * m) hcoef hpq
      hp3 hbd) (memberRows (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ)) s)
      (memberCols (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s) x Ec := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    have h := Finset.mem_filter.1 (hIE'sub hx)
    have h' := Finset.mem_filter.1 h.1
    have hb' := Finset.mem_Ico.1 h'.1
    exact hEr x hb'.1 hb'.2 h'.2 h.2 _ rfl rfl
  have hOreal : ∀ x ∈ YO, Realizes ((frameDigamma p6Frame u3 q3).poleSplit (r + 2 * m) hcoef hpq
      hp3 hbd) (memberRows (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ)) s)
      (memberCols (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s) x Oc := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
    have h := Finset.mem_filter.1 (hIO'sub hx)
    have h' := Finset.mem_filter.1 h.1
    have hb' := Finset.mem_Ico.1 h'.1
    exact hOr x hb'.1 hb'.2 h'.2 h.2 _ rfl rfl
  obtain ⟨M, hM⟩ := pair_member p6Frame u3 q3 (fun c : Fin r => (c : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p (r + 2 * m)
    hcoef hpq hp3 hbd hB ha hb (rows_inj r m s) (cols_inj r m s) Ec Oc YE YO hEok hOok
    (integral_of_denOk p Ec hEden hN) (integral_of_denOk p Oc hOden hN) hEkr hEkc hOkr hOkc hdisj
    (hYEcard.trans hYOcard.symm) hEreal hOreal hload hnz
  refine ⟨M, ?_⟩
  have hcs : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hcard : Fintype.card (s ⊕ Fin m) = s.card + m := by simp
  rw [hcard, hYEcard] at hM
  omega

end CatalanCore.Uniform.Bank.Chi3Rank
