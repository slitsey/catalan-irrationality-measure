module

public import CatalanCore.Uniform.Content.RankProducer.Triv

@[expose] public section
set_option Elab.async false

/-! # Paired row-kill / column-kill certificates (lane H, H16)

Two certificates `Ec` (kills the row of digit `0`) and `Oc` (kills the column of digit `0`) with the
same load, placed on fibre sets `YE`, `YO` of equal size, all other fibres trivial.  With `V` the
line spanned by the common load, the rank-layer price of the member is at most `2h - 2|YE|`. -/

namespace CatalanCore.Uniform.Bank.Chi3Rank
open Polynomial Finset Module Matrix CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.RankProducer

open scoped Classical

theorem price_arith (H S F C D n : ℕ) (hS : S = n) (hnH : n ≤ H) (hC : n ≤ C) (hD : D = 0) :
    H + (H - S) - (F + (C - D)) + 2 * n ≤ 2 * H := by omega

variable {p : ℕ} [hp : Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] {B : ℕ} {f e : ℕ → ℚ}

/-- The paired certificate assignment. -/
noncomputable def pairCert (PS : PoleSplit p B f e) (a b : ι → ℕ) (Ec Oc : FibreCert)
    (YE YO : Finset (ZMod p)) : ZMod p → FibreCert := fun x =>
  if x ∈ YE then Ec else if x ∈ YO then Oc else trivCert PS a b x

section
variable (PS : PoleSplit p B f e) (a b : ι → ℕ) (Ec Oc : FibreCert) (YE YO : Finset (ZMod p))

theorem pairCert_E {x} (hx : x ∈ YE) : pairCert PS a b Ec Oc YE YO x = Ec := if_pos hx

theorem pairCert_O (hdisj : Disjoint YE YO) {x} (hx : x ∈ YO) :
    pairCert PS a b Ec Oc YE YO x = Oc := by
  have : x ∉ YE := Finset.disjoint_right.1 hdisj hx
  simp [pairCert, this, hx]

theorem pairCert_T {x} (h1 : x ∉ YE) (h2 : x ∉ YO) :
    pairCert PS a b Ec Oc YE YO x = trivCert PS a b x := by simp [pairCert, h1, h2]

theorem pairCert_kr (hEkr : Ec.kr = {0}) (hOkr : Oc.kr = ∅) (x : ZMod p) (d : ℕ)
    (h : d ∈ (pairCert PS a b Ec Oc YE YO x).kr) : x ∈ YE ∧ d = 0 := by
  by_cases h1 : x ∈ YE
  · rw [pairCert_E PS a b Ec Oc YE YO h1, hEkr] at h
    exact ⟨h1, by simpa using h⟩
  · exfalso
    by_cases h2 : x ∈ YO
    · unfold pairCert at h; rw [if_neg h1, if_pos h2, hOkr] at h; simp at h
    · unfold pairCert at h; rw [if_neg h1, if_neg h2] at h
      simp [trivCert, FibreCert.triv] at h

theorem pairCert_kc (hEkc : Ec.kc = ∅) (hOkc : Oc.kc = {0}) (x : ZMod p) (d : ℕ)
    (h : d ∈ (pairCert PS a b Ec Oc YE YO x).kc) : x ∈ YO ∧ d = 0 := by
  by_cases h1 : x ∈ YE
  · exfalso
    rw [pairCert_E PS a b Ec Oc YE YO h1, hEkc] at h; simp at h
  · by_cases h2 : x ∈ YO
    · unfold pairCert at h; rw [if_neg h1, if_pos h2, hOkc] at h
      exact ⟨h2, by simpa using h⟩
    · exfalso
      unfold pairCert at h; rw [if_neg h1, if_neg h2] at h
      simp [trivCert, FibreCert.triv] at h

end

end CatalanCore.Uniform.Bank.Chi3Rank
