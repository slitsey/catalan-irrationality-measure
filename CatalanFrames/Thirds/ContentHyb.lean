module

public import CatalanFrames.Thirds.Instance
public import CatalanFrames.Thirds.CoversLow
public import CatalanFrames.Thirds.CoversHigh
public import CatalanFrames.Thirds.Tables
public import CatalanFrames.HybGen.TableSum
public import CatalanFrames.HybGen.D1Prefix

@[expose] public section

/-!
# Hybrid content of the thirds frames (M6)

`thirds_log_content`: for `r ≤ 8m ≤ r + 9`, eventually uniformly in `m`,
`log Dhyb ≤ (32313/10000 + ε) r²`, for `T : ThirdsData Fr e` whose two classes mod 6 are one low
and one high (`Band`).  The realised rational constant is `Clow + Chigh = 3.2312582…`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen

namespace CatalanFrames.Thirds

variable {Fr : Frame} {e : ℕ}

lemma floor_four (r : ℕ) : ⌊(4 : ℝ) * r⌋₊ = 4 * r := by
  have : (4 : ℝ) * r = ((4 * r : ℕ) : ℝ) := by push_cast; ring
  rw [this, Nat.floor_natCast]

lemma tot6 : ((Nat.totient 6 : ℕ) : ℝ) = 2 := by
  rw [show Nat.totient 6 = 2 by decide]; norm_num

lemma hc2_of_band {I : HybInst Fr} {c : ZMod 6} {d j u v : ℕ} (hb : Band I 6 c d j u v) :
    ∀ p : ℕ, p.Prime → (p : ZMod 6) = c → p ≠ 2 := by
  intro p hp hpc
  have := (hb p hp hpc).1
  omega

theorem thirds_class_low (T : ThirdsData Fr e) {c : ZMod 6} (hc : IsUnit c)
    (hb : Band (thirdsInst T) 6 c 3 1 1 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      clsSum 6 c (WGm (thirdsInst T) r m) 0 (4 * r) ≤ (r : ℝ) ^ 2 * (Clow + ε) := by
  have h := class_sum_of_tables (c := c) hc (thirdsInst T) (ld1 ++ tlow) llow_chain (by
    intro r m h1 h2 h3 P hP
    rw [List.mem_append] at hP
    rcases hP with hP | hP
    · exact ld1_covers (thirdsInst T) (hc2_of_band hb) h1 h2 P hP
    · simp only [tlow, List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [tlow_1 hb h1 h2 h3, tlow_2 (thirds_levels T) hb h1 h2 h3,
        tlow_3 (thirds_levels T) hb h1 h2 h3, tlow_4 (thirds_levels T) hb h1 h2 h3,
        tlow_5 (thirds_levels T) hb h1 h2 h3, tlow_6 (thirds_levels T) hb h1 h2 h3,
        tlow_7 (thirds_levels T) hb h1 h2 h3]) hε
  filter_upwards [h] with r hr m h1 h2
  have := hr m h1 h2
  rw [llow_end, floor_four, tot6] at this
  simpa [Clow] using this

theorem thirds_class_high (T : ThirdsData Fr e) {c : ZMod 6} (hc : IsUnit c)
    (hb : Band (thirdsInst T) 6 c 3 2 1 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      clsSum 6 c (WGm (thirdsInst T) r m) 0 (4 * r) ≤ (r : ℝ) ^ 2 * (Chigh + ε) := by
  have h := class_sum_of_tables (c := c) hc (thirdsInst T) (ld1 ++ thigh) lhigh_chain (by
    intro r m h1 h2 h3 P hP
    rw [List.mem_append] at hP
    rcases hP with hP | hP
    · exact ld1_covers (thirdsInst T) (hc2_of_band hb) h1 h2 P hP
    · simp only [thigh, List.mem_cons, List.not_mem_nil, or_false] at hP
      rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      exacts [thigh_1 hb h1 h2 h3, thigh_2 (thirds_levels T) hb h1 h2 h3,
        thigh_3 (thirds_levels T) hb h1 h2 h3, thigh_4 (thirds_levels T) hb h1 h2 h3,
        thigh_5 (thirds_levels T) hb h1 h2 h3, thigh_6 (thirds_levels T) hb h1 h2 h3,
        thigh_7 (thirds_levels T) hb h1 h2 h3]) hε
  filter_upwards [h] with r hr m h1 h2
  have := hr m h1 h2
  rw [lhigh_end, floor_four, tot6] at this
  simpa [Chigh] using this

/-- Beyond `4r` the weight vanishes (both classes: `3 kq ≥ p + 1`). -/
lemma thirds_tail (T : ThirdsData Fr e) {r m p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hk : p + 1 ≤ 3 * (thirdsInst T).cd.kq p) (hr : 400 ≤ r) (h1 : r ≤ 8 * m)
    (h2 : 8 * m ≤ r + 9) (hcut : 4 * r < p) : WGm (thirdsInst T) r m p = 0 := by
  have h6 := XGm_D6 (thirds_levels T) r m p hp h5 (by omega) (by omega)
  have h0 : XGm (thirdsInst T) r m p = 0 := by omega
  simp [WGm, h0]

/-- Use any separately verified upper bound for the two class constants. -/
theorem thirds_log_content_of_le (T : ThirdsData Fr e)
    (C : ℝ) (hC : Clow + Chigh ≤ C)
    (hbands : (Band (thirdsInst T) 6 1 3 1 1 2 ∧ Band (thirdsInst T) 6 5 3 2 1 2) ∨
      (Band (thirdsInst T) 6 1 3 2 1 2 ∧ Band (thirdsInst T) 6 5 3 1 1 2)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      Real.log (Dhyb (thirdsInst T) r m) ≤ (C + ε) * (r : ℝ) ^ 2 := by
  have hu1 : IsUnit (1 : ZMod 6) := isUnit_one
  have hu5 : IsUnit (5 : ZMod 6) := by decide
  have hcl : ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      clsSum 6 1 (WGm (thirdsInst T) r m) 0 (4 * r) + clsSum 6 5 (WGm (thirdsInst T) r m) 0 (4 * r) ≤
        (r : ℝ) ^ 2 * (Clow + Chigh + ε / 2) := by
    rcases hbands with ⟨h1, h5⟩ | ⟨h1, h5⟩
    · filter_upwards [thirds_class_low T hu1 h1 (ε := ε / 4) (by positivity),
        thirds_class_high T hu5 h5 (ε := ε / 4) (by positivity)] with r ha hb m hm1 hm2
      have := ha m hm1 hm2
      have := hb m hm1 hm2
      nlinarith
    · filter_upwards [thirds_class_high T hu1 h1 (ε := ε / 4) (by positivity),
        thirds_class_low T hu5 h5 (ε := ε / 4) (by positivity)] with r ha hb m hm1 hm2
      have := ha m hm1 hm2
      have := hb m hm1 hm2
      nlinarith
  have hx := (thirds_badInfo T).extra_small (ε / 2) (by positivity)
  filter_upwards [hcl, hx, eventually_ge_atTop 400] with r hcl hx hr m h1 h2
  have hall : ∀ p : ℕ, p.Prime → ((p : ZMod 6) = 1 ∨ (p : ZMod 6) = 5) →
      5 ≤ p ∧ p + 1 ≤ 3 * (thirdsInst T).cd.kq p := by
    intro p hp hpc
    rcases hbands with ⟨b1, b5⟩ | ⟨b1, b5⟩ <;> rcases hpc with hpc | hpc
    · have := b1 p hp hpc; unfold BandP at this; omega
    · have := b5 p hp hpc; unfold BandP at this; omega
    · have := b1 p hp hpc; unfold BandP at this; omega
    · have := b5 p hp hpc; unfold BandP at this; omega
  have hD := log_Dhyb_le_gen (thirds_badInfo T) (M := 6) ({1, 5} : Finset (ZMod 6))
    (fun _ => 4 * r) r m (by omega) (WGm (thirdsInst T) r m) (fun p => Nat.cast_nonneg _)
    (fun p _ => le_rfl) (fun p hp hb => cls_mem_of_bad hp hb) (by
      intro c hc b hb hbc
      have hb' : b ∈ ({2, 3} : Finset ℕ) := hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb' hc
      rcases hb' with rfl | rfl <;> rcases hc with rfl | rfl <;> exact absurd hbc (by decide)) (by
      intro c hc p hp hb hpc hcut
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      have hh := hall p hp (by rcases hc with rfl | rfl <;> simp [hpc])
      exact thirds_tail T hp hh.1 hh.2 hr h1 h2 hcut)
  rw [Finset.sum_pair (by decide : (1 : ZMod 6) ≠ 5)] at hD
  have hm : m ≤ r := by omega
  have hE := hx m hm
  have hq := hcl m h1 h2
  have hCC' := mul_le_mul_of_nonneg_right hC (sq_nonneg (r : ℝ))
  nlinarith

theorem thirds_log_content_of (T : ThirdsData Fr e)
    (hbands : (Band (thirdsInst T) 6 1 3 1 1 2 ∧ Band (thirdsInst T) 6 5 3 2 1 2) ∨
      (Band (thirdsInst T) 6 1 3 2 1 2 ∧ Band (thirdsInst T) 6 5 3 1 1 2)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m : ℕ, r ≤ 8 * m → 8 * m ≤ r + 9 →
      Real.log (Dhyb (thirdsInst T) r m) ≤ (32313 / 10000 + ε) * (r : ℝ) ^ 2 := by
  exact thirds_log_content_of_le T (32313 / 10000) Clow_add_Chigh_le hbands hε

end CatalanFrames.Thirds

#print axioms CatalanFrames.Thirds.thirds_log_content_of
