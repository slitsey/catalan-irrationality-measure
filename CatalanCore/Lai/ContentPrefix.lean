module

public import CatalanCore.Lai.ContentFinal

@[expose] public section

/-!
# `CatalanCore.Lai.ContentPrefix`: the C01 prefix datum `(Ŝ, hS, hR)` of `lai_content_cert`

`partialS e23 d23 1000 ≤ Ŝ` with `Ŝ = T/2^81`.  No literal table: the grid numerators
`Q(m, i) = ⌈2^80/(m + e_i)⌉` (weight `d_i < 0`) or `⌊2^80/(m + e_i)⌋` (`d_i > 0`) are *computed* in the
kernel by two natural-number operations each (`pq`), the 999 rows are summed in chunks, one chunk per
declaration, and `T` is the exact integer total (`w_i = -2 d_i`).  The generic step is
`partialS_le_of_grid`.  Grid error ≤ 22,977 · 30 · 2^-80 ≈ 6·10⁻¹⁹ is inside the sum itself (the sum is
of upper bounds), so the single rational comparison `Ŝ + Φ(1000) ≤ 3573565641/700000000` has margin 4.1·10⁻⁹.
-/

open CatalanCore.Content.PartialSums CatalanCore.Lai

namespace CatalanCore.Lai.ContentPrefix

def pa : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 3
  | 8 => 2
  | 9 => 3
  | 10 => 4
  | 11 => 1
  | 12 => 5
  | 13 => 4
  | 14 => 3
  | 15 => 5
  | 16 => 2
  | 17 => 5
  | 18 => 3
  | 19 => 5
  | 20 => 6
  | 21 => 7
  | 22 => 1
  | _ => 0

def pb : ℕ → ℕ
  | 0 => 1
  | 1 => 8
  | 2 => 7
  | 3 => 6
  | 4 => 4
  | 5 => 7
  | 6 => 3
  | 7 => 8
  | 8 => 5
  | 9 => 7
  | 10 => 9
  | 11 => 2
  | 12 => 9
  | 13 => 7
  | 14 => 5
  | 15 => 8
  | 16 => 3
  | 17 => 7
  | 18 => 4
  | 19 => 6
  | 20 => 7
  | 21 => 8
  | 22 => 1
  | _ => 1

def pw : ℕ → ℤ
  | 0 => 24
  | 1 => -16
  | 2 => -14
  | 3 => 24
  | 4 => -16
  | 5 => -14
  | 6 => 27
  | 7 => -8
  | 8 => -5
  | 9 => -14
  | 10 => -9
  | 11 => 60
  | 12 => -9
  | 13 => -14
  | 14 => -5
  | 15 => -8
  | 16 => 27
  | 17 => -14
  | 18 => -16
  | 19 => 24
  | 20 => -14
  | 21 => -16
  | 22 => 6
  | _ => 0

/-- grid numerator: ceiling of `2^80 / (m + e_i)` when the term is positive (`pw i > 0`), floor otherwise. -/
def pq (m i : ℕ) : ℕ :=
  if 0 < pw i then (2 ^ 80 * pb i + (m * pb i + pa i) - 1) / (m * pb i + pa i)
  else (2 ^ 80 * pb i) / (m * pb i + pa i)

/-- one row of the grid sum: `Σ_i w_i Q(m, i)`, with `w_i = -2 d_i`. -/
def rowT (m : ℕ) : ℤ := ∑ i ∈ Finset.range 23, pw i * (pq m i : ℤ)



theorem chunk0 : ∑ m ∈ Finset.Ico 1 51, rowT m = 12129455274299988371223712 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk1 : ∑ m ∈ Finset.Ico 51 101, rowT m = 106034136195844807579630 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk2 : ∑ m ∈ Finset.Ico 101 151, rowT m = 35750379193098734067285 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk3 : ∑ m ∈ Finset.Ico 151 201, rowT m = 17952212344765377494061 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk4 : ∑ m ∈ Finset.Ico 201 251, rowT m = 10796099186839184573145 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk5 : ∑ m ∈ Finset.Ico 251 301, rowT m = 7207750008746404076094 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk6 : ∑ m ∈ Finset.Ico 301 351, rowT m = 5153471672821573093486 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk7 : ∑ m ∈ Finset.Ico 351 401, rowT m = 3867884739100426218733 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk8 : ∑ m ∈ Finset.Ico 401 451, rowT m = 3010004331106565994637 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk9 : ∑ m ∈ Finset.Ico 451 501, rowT m = 2409043422143332942428 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk10 : ∑ m ∈ Finset.Ico 501 551, rowT m = 1971723497460336576821 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk11 : ∑ m ∈ Finset.Ico 551 601, rowT m = 1643576115637055297821 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk12 : ∑ m ∈ Finset.Ico 601 651, rowT m = 1391054383221774137379 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk13 : ∑ m ∈ Finset.Ico 651 701, rowT m = 1192577647864759266572 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk14 : ∑ m ∈ Finset.Ico 701 751, rowT m = 1033750518115790887920 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk15 : ∑ m ∈ Finset.Ico 751 801, rowT m = 904671301926288666212 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk16 : ∑ m ∈ Finset.Ico 801 851, rowT m = 798347608029738258144 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk17 : ∑ m ∈ Finset.Ico 851 901, rowT m = 709727510491359590434 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk18 : ∑ m ∈ Finset.Ico 901 951, rowT m = 635087327809052596883 := by decide +kernel -- kcost: 0.19 s measured

theorem chunk19 : ∑ m ∈ Finset.Ico 951 1000, rowT m = 560761100554296881335 := by decide +kernel -- kcost: 0.19 s measured

theorem tail19 : ∑ m ∈ Finset.Ico 951 1000, rowT m = 560761100554296881335 := chunk19

theorem tail18 : ∑ m ∈ Finset.Ico 901 1000, rowT m = 1195848428363349478218 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 901 ≤ 951) (by norm_num : 951 ≤ 1000), chunk18, tail19]
  norm_num

theorem tail17 : ∑ m ∈ Finset.Ico 851 1000, rowT m = 1905575938854709068652 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 851 ≤ 901) (by norm_num : 901 ≤ 1000), chunk17, tail18]
  norm_num

theorem tail16 : ∑ m ∈ Finset.Ico 801 1000, rowT m = 2703923546884447326796 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 801 ≤ 851) (by norm_num : 851 ≤ 1000), chunk16, tail17]
  norm_num

theorem tail15 : ∑ m ∈ Finset.Ico 751 1000, rowT m = 3608594848810735993008 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 751 ≤ 801) (by norm_num : 801 ≤ 1000), chunk15, tail16]
  norm_num

theorem tail14 : ∑ m ∈ Finset.Ico 701 1000, rowT m = 4642345366926526880928 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 701 ≤ 751) (by norm_num : 751 ≤ 1000), chunk14, tail15]
  norm_num

theorem tail13 : ∑ m ∈ Finset.Ico 651 1000, rowT m = 5834923014791286147500 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 651 ≤ 701) (by norm_num : 701 ≤ 1000), chunk13, tail14]
  norm_num

theorem tail12 : ∑ m ∈ Finset.Ico 601 1000, rowT m = 7225977398013060284879 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 601 ≤ 651) (by norm_num : 651 ≤ 1000), chunk12, tail13]
  norm_num

theorem tail11 : ∑ m ∈ Finset.Ico 551 1000, rowT m = 8869553513650115582700 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 551 ≤ 601) (by norm_num : 601 ≤ 1000), chunk11, tail12]
  norm_num

theorem tail10 : ∑ m ∈ Finset.Ico 501 1000, rowT m = 10841277011110452159521 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 501 ≤ 551) (by norm_num : 551 ≤ 1000), chunk10, tail11]
  norm_num

theorem tail9 : ∑ m ∈ Finset.Ico 451 1000, rowT m = 13250320433253785101949 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 451 ≤ 501) (by norm_num : 501 ≤ 1000), chunk9, tail10]
  norm_num

theorem tail8 : ∑ m ∈ Finset.Ico 401 1000, rowT m = 16260324764360351096586 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 401 ≤ 451) (by norm_num : 451 ≤ 1000), chunk8, tail9]
  norm_num

theorem tail7 : ∑ m ∈ Finset.Ico 351 1000, rowT m = 20128209503460777315319 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 351 ≤ 401) (by norm_num : 401 ≤ 1000), chunk7, tail8]
  norm_num

theorem tail6 : ∑ m ∈ Finset.Ico 301 1000, rowT m = 25281681176282350408805 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 301 ≤ 351) (by norm_num : 351 ≤ 1000), chunk6, tail7]
  norm_num

theorem tail5 : ∑ m ∈ Finset.Ico 251 1000, rowT m = 32489431185028754484899 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 251 ≤ 301) (by norm_num : 301 ≤ 1000), chunk5, tail6]
  norm_num

theorem tail4 : ∑ m ∈ Finset.Ico 201 1000, rowT m = 43285530371867939058044 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 201 ≤ 251) (by norm_num : 251 ≤ 1000), chunk4, tail5]
  norm_num

theorem tail3 : ∑ m ∈ Finset.Ico 151 1000, rowT m = 61237742716633316552105 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 151 ≤ 201) (by norm_num : 201 ≤ 1000), chunk3, tail4]
  norm_num

theorem tail2 : ∑ m ∈ Finset.Ico 101 1000, rowT m = 96988121909732050619390 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 101 ≤ 151) (by norm_num : 151 ≤ 1000), chunk2, tail3]
  norm_num

theorem tail1 : ∑ m ∈ Finset.Ico 51 1000, rowT m = 203022258105576858199020 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 51 ≤ 101) (by norm_num : 101 ≤ 1000), chunk1, tail2]
  norm_num

theorem tail0 : ∑ m ∈ Finset.Ico 1 1000, rowT m = 12332477532405565229422732 := by
  rw [← Finset.sum_Ico_consecutive _ (by norm_num : 1 ≤ 51) (by norm_num : 51 ≤ 1000), chunk0, tail1]
  norm_num

theorem total_eq : ∑ m ∈ Finset.Ico 1 1000, rowT m = 12332477532405565229422732 := tail0

/-! ### Glue (theorem side) -/

/-- node facts at `Fin 23`. -/
theorem node_facts (i : Fin 23) :
    e23 i = (pa i : ℚ) / (pb i : ℚ) ∧ d23 i = -((pw i : ℤ) : ℚ) / 2 ∧ 0 < pb i := by
  fin_cases i <;> simp [e23, d23, c01Eq, c01Dq, pa, pb, pw] <;> norm_num

theorem term_bound (a b : ℕ) (hb : 0 < b) (w : ℤ) (hw : w ≠ 0) (m : ℕ) (hm : 1 ≤ m) (e d : ℚ)
    (he : e = (a : ℚ) / b) (hd : d = -(w : ℚ) / 2)
    (q : ℕ) (hq : (0 < w → 2 ^ 80 * b ≤ q * (m * b + a)) ∧ (w < 0 → q * (m * b + a) ≤ 2 ^ 80 * b)) :
    -d / ((m : ℚ) + e) ≤ -d * (q : ℚ) / 2 ^ 80 := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hY : (0 : ℚ) < (m : ℚ) * b + a := by
    have : (0 : ℚ) < m := by exact_mod_cast hm
    positivity
  have hme : (m : ℚ) + e = ((m : ℚ) * b + a) / b := by rw [he]; field_simp
  have hnd : -d = (w : ℚ) / 2 := by rw [hd]; ring
  rw [hme, hnd]
  rw [div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h := hq.2 hneg
    have h' : (q : ℚ) * ((m : ℚ) * b + a) ≤ 2 ^ 80 * b := by exact_mod_cast h
    have hw' : (w : ℚ) < 0 := by exact_mod_cast hneg
    nlinarith [mul_le_mul_of_nonpos_left h' hw'.le]
  · have h := hq.1 hpos
    have h' : (2 : ℚ) ^ 80 * b ≤ q * ((m : ℚ) * b + a) := by exact_mod_cast h
    have hw' : (0 : ℚ) < w := by exact_mod_cast hpos
    nlinarith [mul_le_mul_of_nonneg_left h' hw'.le]

theorem pw_ne (i : ℕ) (hi : i < 23) : pw i ≠ 0 := by
  interval_cases i <;> simp [pw]

theorem pq_spec (m i : ℕ) (hm : 1 ≤ m) (hb : 0 < pb i) :
    (0 < pw i → 2 ^ 80 * pb i ≤ pq m i * (m * pb i + pa i)) ∧
    (pw i < 0 → pq m i * (m * pb i + pa i) ≤ 2 ^ 80 * pb i) := by
  have hY : 0 < m * pb i + pa i := Nat.add_pos_left (Nat.mul_pos hm hb) _
  constructor
  · intro hw
    simp only [pq, if_pos hw]
    have := Nat.lt_mul_div_succ (2 ^ 80 * pb i + (m * pb i + pa i) - 1) hY
    have h2 : 0 < 2 ^ 80 * pb i := by positivity
    generalize (2 ^ 80 * pb i + (m * pb i + pa i) - 1) / (m * pb i + pa i) = q at this ⊢
    generalize 2 ^ 80 * pb i = X at this h2 ⊢
    generalize m * pb i + pa i = Y at this hY ⊢
    rw [Nat.mul_succ] at this
    have e := Nat.mul_comm q Y
    omega
  · intro hw
    have hn : ¬ 0 < pw i := by omega
    simp only [pq, if_neg hn]
    rw [Nat.mul_comm]
    exact Nat.mul_div_le _ _

/-- the generic grid hypothesis of `partialS_le_of_grid` for `Q = pq`. -/
theorem hterm (m : ℕ) (hm1 : 1 ≤ m) (_hm : m < 1000) (i : Fin 23) :
    -(d23 i) / ((m : ℚ) + e23 i) ≤ -(d23 i) * (((pq m i : ℕ) : ℤ) : ℚ) / 2 ^ 80 := by
  obtain ⟨he, hd, hb⟩ := node_facts i
  have hq := pq_spec m i hm1 hb
  have := term_bound (pa i) (pb i) hb (pw i) (pw_ne i i.2) m hm1 (e23 i) (d23 i) he hd (pq m i) hq
  simpa using this

theorem sum_row (m : ℕ) :
    ∑ i : Fin 23, -(d23 i) * (((pq m i : ℕ) : ℤ) : ℚ) / 2 ^ 80 = (rowT m : ℚ) / 2 ^ 81 := by
  have h : ∀ i : Fin 23, -(d23 i) * (((pq m i : ℕ) : ℤ) : ℚ) / 2 ^ 80 =
      ((pw i * (pq m i : ℤ) : ℤ) : ℚ) / 2 ^ 81 := by
    intro i
    rw [(node_facts i).2.1]; push_cast; ring
  simp only [h]
  rw [← Finset.sum_div, rowT, Fin.sum_univ_eq_sum_range (fun i => ((pw i * (pq m i : ℤ) : ℤ) : ℚ)) 23]
  push_cast; rfl

/-- **the prefix bound.** -/
theorem prefix_le : partialS e23 d23 1000 ≤ ((12332477532405565229422732 : ℤ) : ℚ) / 2 ^ 81 := by
  have h := partialS_le_of_grid (fun m i => ((pq m i : ℕ) : ℤ)) hterm
  refine h.trans (le_of_eq ?_)
  simp only [sum_row]
  rw [← Finset.sum_div, ← Int.cast_sum, total_eq]

/-- the datum `Ŝ`. -/
def Shat : ℚ := ((12332477532405565229422732 : ℤ) : ℚ) / 2 ^ 81

theorem hS : partialS e23 d23 1000 ≤ Shat := prefix_le

set_option maxRecDepth 100000 in
theorem hR : Shat + Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000 := by
  simp only [Shat, Phi, absmom, a2, a3, a4, a5, a6, mom, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [e23, d23, c01Eq, c01Dq]
  norm_num

end CatalanCore.Lai.ContentPrefix

#print axioms CatalanCore.Lai.ContentPrefix.hS
#print axioms CatalanCore.Lai.ContentPrefix.hR
