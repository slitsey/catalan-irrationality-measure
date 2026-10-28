module

public import CatalanCore.Uniform.Content.UFFamily3.Cell3
public import CatalanCore.Uniform.Content.UFFamily.SevELayer

@[expose] public section

/-!
# UF families: the generic window cell `cell3Gen` and its price (lane H, H12)

A family supplies, as affine-with-floor functions of `(r, p)` proved by `omega` (`Win3`):
the border size `m`, the window `[t₀, t_v]` (a run of the border between consecutive singular
indices, extended to the next singular index), the bound `N = r + p`, and

* `hsing`: `NoSingWin` of the window,
* `kill`: for every border node `v` outside `[t₀, t_v]` and not a multiple of `p`, a kill
  certificate against `t₀` (`Nonempty (AltKill ..)`, e.g. from `altKillRun`).

`cell3Gen` is the cell, `cell3Gen_bound` its price
`base3 m r p t₀ t_v = 2 (r + m) - (m + σ + (σ - (p - u)))`, `σ = (min (t_v+1) (r+2m) - t₀) - m`,
`u = (t_v + 1 - t₀) + (2m - (min (t_v+1) (r+2m) - t₀) - 1)`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ}

/-- Two natural numbers of `[a, a + p)` congruent mod `p` are equal. -/
theorem eq_of_modEq_Ico {p a b x : ℕ} (ha1 : x ≤ a) (ha2 : a < x + p) (hb1 : x ≤ b)
    (hb2 : b < x + p) (h : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p)) : a = b := by
  have h1 := (ZMod.natCast_eq_natCast_iff' a b p).1 h
  rcases le_total a b with hle | hle
  · have hd := (Nat.modEq_iff_dvd' hle).1 h1
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd := (Nat.modEq_iff_dvd' hle).1 h1.symm
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

/-- The arithmetic of a window cell. -/
structure Win3 (c : ℚ) (hc : 0 < c) (q o r p N t0 tv m : ℕ) : Prop where
  hr2 : r % 2 = 0
  hr0 : 0 < r
  hbs : (altGeom c hc).borderSize r = m
  hrN : r + 2 * m ≤ N
  hNp : N < p * p
  hpm : 2 * m ≤ p
  hp2 : 2 < p
  hq0 : 0 < q
  hqp : q < p
  ho0 : 0 < o
  hop : o < p
  hqo : o ≤ q
  ht0r : r ≤ t0
  ht0b : t0 < r + 2 * m
  ht0tv : t0 ≤ tv
  htvp : tv < r + p
  htvN : tv < N
  hdiv : tv / p = t0 / p
  hnt0 : ¬ p ∣ t0

/-- The border size. -/
theorem alt_k_eq {r m : ℕ} (hr2 : r % 2 = 0) (hbs : (altGeom c hc).borderSize r = m) :
    ((altGeom c hc).geometry r).k = m := by
  have hf : Function.Injective (fun i : ℕ => r + 2 * i) := fun a b h => by simp at h; omega
  show ((altGeom c hc).geometry r).X'.card = _
  rw [altGeom_X c hc hr2, Finset.card_image_of_injective _ hf, Finset.card_range, hbs]

/-- The price of a window cell. -/
def base3 (m r p t0 tv : ℕ) : ℕ :=
  2 * (r + m) - (m + ((min (tv + 1) (r + 2 * m) - t0) - m) +
    (((min (tv + 1) (r + 2 * m) - t0) - m) -
      (p - ((tv + 1 - t0) + (2 * m - (min (tv + 1) (r + 2 * m) - t0) - 1)))))

set_option maxHeartbeats 1600000 in
/-- **The generic window cell.** -/
noncomputable def cell3Gen (T : TwoTermData Fr q o) {r p N t0 tv m : ℕ} [Fact p.Prime]
    (W : Win3 c hc q o r p N t0 tv m)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0)
    (hsing : NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) t0 (tv - t0))
    (kill : ∀ v, r ≤ v → v < r + 2 * m → (v < t0 ∨ tv < v) → ¬ p ∣ v →
      Nonempty (AltKill c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) t0 v)) :
    Cell3 c hc Fr q o T r p :=
  have hrN : r + 2 * (altGeom c hc).borderSize r ≤ N := W.hbs ▸ W.hrN
  have hk : ((altGeom c hc).geometry r).k = m := alt_k_eq W.hr2 W.hbs
  have hs := altGeom_hybShape c hc W.hr2
  { hr := W.hr2
    N := N
    hNp := W.hNp
    hsq := hsq
    hnorm := hnorm
    hnorm0 := hnorm0
    hrN := hrN
    hp := by have := W.hpm; have := W.hbs; omega
    hp2 := by have := W.hp2; omega
    ho := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd W.ho0 hd; have := W.hop; omega
    hq := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd => by have := Nat.le_of_dvd W.hq0 hd; have := W.hqp; omega
    t0 := t0
    tv := tv
    ht0N := by have := W.ht0b; have := W.hrN; omega
    hrt := W.ht0r
    htv0 := W.ht0tv
    htv := W.htvp
    htvN := W.htvN
    hdiv := W.hdiv
    hw := hsing
    TC := Finset.univ.filter fun j => (((altGeom c hc).geometry r).ys j < t0 ∨
      tv < ((altGeom c hc).geometry r).ys j) ∧ ¬ p ∣ ((altGeom c hc).geometry r).ys j
    TR := Finset.univ.filter fun j => (((altGeom c hc).geometry r).xs j < t0 ∨
      tv < ((altGeom c hc).geometry r).xs j) ∧ ¬ p ∣ ((altGeom c hc).geometry r).xs j
    hwC := fun t ht => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 ht).2
      have hy := hs.ys_eq t
      have ht' := t.2
      obtain ⟨K⟩ := kill _ (by omega) (by omega) h1 h2
      exact K.wedgeC_ne t (tt_regRed (p := p) T W.hNp.le hsq hnorm hnorm0)
        (by have := W.ht0b; have := W.hrN; omega)
    hwR := fun t ht => by
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 ht).2
      have hy := hs.xs_eq t
      have ht' := t.2
      obtain ⟨K⟩ := kill _ (by omega) (by omega) h1 h2
      exact K.wedgeR_ne t (tt_regRed (p := p) T W.hNp.le hsq hnorm hnorm0)
        (by have := W.ht0b; have := W.hrN; omega)
    u := (tv + 1 - t0) + (2 * m - (min (tv + 1) (r + 2 * m) - t0) - 1)
    hu := by
      classical
      have hS := card_S0 r m p t0 tv W.hpm W.ht0r
      have hinj : Set.InjOn (fun t : ℕ => ((t : ℕ) : ZMod p))
          ((Finset.Icc t0 tv ∪
            (Finset.Ico r (r + 2 * m)).filter (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v) : Finset ℕ) :
            Set ℕ) := by
        intro a ha b hb hab
        simp only [Finset.coe_union, Finset.coe_Icc, Finset.coe_filter, Finset.mem_coe,
          Set.mem_union, Set.mem_Icc, Finset.mem_Ico, Set.mem_setOf_eq] at ha hb
        have := W.ht0r; have := W.htvp; have := W.hpm
        exact eq_of_modEq_Ico (x := r) (by omega) (by omega) (by omega) (by omega) hab
      have hcard := Finset.card_image_of_injOn hinj
      have hsub : (Finset.Icc t0 tv ∪
            (Finset.Ico r (r + 2 * m)).filter (fun v => (v < t0 ∨ tv < v) ∧ ¬ p ∣ v)).image
            (fun t : ℕ => ((t : ℕ) : ZMod p)) ⊆
          (((Finset.Icc t0 tv).image (fun t : ℕ => ((t : ℕ) : ZMod p))) ∪
            ((Finset.univ.filter (fun j => (((altGeom c hc).geometry r).ys j < t0 ∨
                tv < ((altGeom c hc).geometry r).ys j) ∧ ¬ p ∣ ((altGeom c hc).geometry r).ys j)).image
                (fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
              (Finset.univ.filter (fun j => (((altGeom c hc).geometry r).xs j < t0 ∨
                tv < ((altGeom c hc).geometry r).xs j) ∧ ¬ p ∣ ((altGeom c hc).geometry r).xs j)).image
                (fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p)))) := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
        rcases Finset.mem_union.1 hx with hx | hx
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
        · obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
          obtain ⟨hxa, hxb⟩ := Finset.mem_Ico.1 hx1
          apply Finset.mem_union_right
          by_cases hpar : (x - r) % 2 = 0
          · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨(x - r) / 2, by omega⟩, ?_, ?_⟩)
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs.xs_eq]
              refine ⟨?_, ?_⟩
              · rcases hx2.1 with h | h
                · left; show r + 2 * ((x - r) / 2) < t0; omega
                · right; show tv < r + 2 * ((x - r) / 2); omega
              · show ¬ p ∣ r + 2 * ((x - r) / 2)
                have : r + 2 * ((x - r) / 2) = x := by omega
                rw [this]; exact hx2.2
            · show ((((altGeom c hc).geometry r).xs ⟨(x - r) / 2, _⟩ : ℕ) : ZMod p) = _
              rw [hs.xs_eq]
              congr 2
              show r + 2 * ((x - r) / 2) = x
              omega
          · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨(x - r) / 2, by omega⟩, ?_, ?_⟩)
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs.ys_eq]
              refine ⟨?_, ?_⟩
              · rcases hx2.1 with h | h
                · left; show r + 2 * ((x - r) / 2) + 1 < t0; omega
                · right; show tv < r + 2 * ((x - r) / 2) + 1; omega
              · show ¬ p ∣ r + 2 * ((x - r) / 2) + 1
                have : r + 2 * ((x - r) / 2) + 1 = x := by omega
                rw [this]; exact hx2.2
            · show ((((altGeom c hc).geometry r).ys ⟨(x - r) / 2, _⟩ : ℕ) : ZMod p) = _
              rw [hs.ys_eq]
              congr 2
              show r + 2 * ((x - r) / 2) + 1 = x
              omega
      have := Finset.card_le_card hsub
      omega }

set_option maxHeartbeats 1600000 in
/-- The price of the generic window cell. -/
theorem cell3Gen_bound (T : TwoTermData Fr q o) {r p N t0 tv m : ℕ} [Fact p.Prime]
    (W : Win3 c hc q o r p N t0 tv m) (hsq) (hnorm) (hnorm0) (hsing) (kill) :
    (cell3Gen T W hsq hnorm hnorm0 hsing kill).bound = base3 m r p t0 tv := by
  have hr2 := W.hr2
  have hs := altGeom_hybShape c hc hr2
  have hk : ((altGeom c hc).geometry r).k = m := alt_k_eq W.hr2 W.hbs
  have hC : Fintype.card ((altGeom c hc).geometry r).C = r := by
    rw [Fintype.card_coe, hs.C_eq, Finset.card_range]
  have hRows : (winRows (r := r) c hc t0 tv).card =
      ((Finset.range m).filter (fun i => t0 ≤ r + 2 * i ∧ r + 2 * i ≤ tv)).card := by
    unfold winRows
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      t0 ≤ r + 2 * (i : ℕ) ∧ r + 2 * (i : ℕ) ≤ tv) (fun i _ => by rw [hs.xs_eq]),
      card_fin_filter _ (fun n => t0 ≤ r + 2 * n ∧ r + 2 * n ≤ tv), hk]
  have hCols : (winCols (r := r) c hc t0 tv).card =
      ((Finset.range m).filter (fun i => t0 ≤ r + 2 * i + 1 ∧ r + 2 * i + 1 ≤ tv)).card := by
    unfold winCols
    rw [Finset.filter_congr (q := fun i : Fin ((altGeom c hc).geometry r).k =>
      t0 ≤ r + 2 * (i : ℕ) + 1 ∧ r + 2 * (i : ℕ) + 1 ≤ tv) (fun i _ => by rw [hs.ys_eq]),
      card_fin_filter _ (fun n => t0 ≤ r + 2 * n + 1 ∧ r + 2 * n + 1 ≤ tv), hk]
  have hsum := card_win_sum r m t0 tv W.ht0r
  unfold Cell3.bound Cell3.sigma
  have e : (cell3Gen T W hsq hnorm hnorm0 hsing kill).u =
      (tv + 1 - t0) + (2 * m - (min (tv + 1) (r + 2 * m) - t0) - 1) := rfl
  have e1 : (cell3Gen T W hsq hnorm hnorm0 hsing kill).t0 = t0 := rfl
  have e2 : (cell3Gen T W hsq hnorm hnorm0 hsing kill).tv = tv := rfl
  rw [e, e1, e2, hRows, hCols, hk, Fintype.card_sum, hC, Fintype.card_fin, base3]
  omega

end CatalanCore.Uniform.Content.UFFamily3
