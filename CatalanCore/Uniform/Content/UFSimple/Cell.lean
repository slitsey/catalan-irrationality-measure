module

public import CatalanCore.Uniform.Content.UFSimple.Kill
public import CatalanCore.Uniform.Content.UFSimple.Count
public import CatalanCore.Uniform.Content.UFFamily3.Gen3

@[expose] public section

/-!
# UF simplification (H18): the two generic closed cells

A UF cell of the alternating geometry of a two-term frame is determined by four numbers:
the selected window `[t₀, t_v]` (`J` = the border nodes in it), and the credited residue window
`[w₀, t_v]` (`w₀ = t₀`, no extension, or `t₀ = r` and `w₀ < r`, the top extension `[w₀, r - 1]`).
Every border node outside `[t₀, t_v]` is killed with NO certificate: `WinC.hsepL/hsepR` give a
separating singular index and `altWedgeC/R_ne_of_sep` (lemmas W0 + S) the wedge.

* `cellNo` (a `Cell3`) and `cellExt` (a `UFCellF`);
* `cellNo_bound`, `cellExt_bound`: both prices equal `closedBound m r p t₀ t_v w₀`
  `= 2(r+m) - (m + σ + (σ - (p - u)))`, `σ = (min (t_v+1) (r+2m) - t₀) - m`,
  `u = (t_v + 1 - w₀) + (2m - β)`, `β` the three-translate overlap of `[w₀, t_v]` with the border.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.UFFamily3
  CatalanCore.Uniform.Content.UFFamily.SevE

namespace CatalanCore.Uniform.Content.UFSimple

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o : ℕ}

/-- The overlap `β` of the credited window with the border (three translates). -/
def beta3 (m r p w0 w1 : ℕ) : ℕ :=
  ovl r (r + 2 * m) w0 w1 + ovl r (r + 2 * m) (w0 + p) (w1 + p) + ovl r (r + 2 * m) (w0 - p) (w1 - p)

/-- **The closed UF price of a cell.** -/
def closedBound (m r p t0 tv w0 : ℕ) : ℕ :=
  2 * (r + m) - (m + ((min (tv + 1) (r + 2 * m) - t0) - m) +
    (((min (tv + 1) (r + 2 * m) - t0) - m) - (p - ((tv + 1 - w0) + (2 * m - beta3 m r p w0 tv)))))

/-- The arithmetic of a closed cell (all linear, plus the two separation facts). -/
structure WinC (c : ℚ) (hc : 0 < c) (q o r p N t0 tv w0 m : ℕ) : Prop where
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
  hw0 : w0 ≤ t0
  ht0r : r ≤ t0
  ht0b : t0 < r + 2 * m
  ht0tv : t0 ≤ tv
  htvp : tv < r + p
  htvN : tv < N
  hdiv : tv / p = t0 / p
  hwin : tv < w0 + p
  hR : r + 2 * m ≤ w0 + 2 * p
  hsepL : ∀ v, r ≤ v → v < t0 → ∃ k, v < k ∧ k ≤ t0 ∧ (p ∣ k ∨ p ∣ q * k - o)
  hsepR : ∀ v, tv < v → v < r + 2 * m → ∃ k, t0 < k ∧ k ≤ v ∧ (p ∣ k ∨ p ∣ q * k - o)

section Kills

variable {r p N t0 tv w0 m : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
theorem WinC.killC (W : WinC c hc q o r p N t0 tv w0 m) (T : TwoTermData Fr q o)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ t ∈ Finset.univ.filter (fun j : Fin ((altGeom c hc).geometry r).k =>
        ((altGeom c hc).geometry r).ys j < t0 ∨ tv < ((altGeom c hc).geometry r).ys j),
      wedgeC (altLift c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN)) Fr
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys
        (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
          (altLift c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN)).toBlocks₁₁ t0
          (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0 := by
  intro t ht
  have hs := altGeom_hybShape c hc W.hr2
  have hk : ((altGeom c hc).geometry r).k = m := alt_k_eq W.hr2 W.hbs
  have hy := hs.ys_eq t
  have ht' := t.2
  have h1 := (Finset.mem_filter.1 ht).2
  have := W.hpm; have := W.ht0b; have := W.ht0r; have := W.ht0tv
  refine altWedgeC_ne_of_sep W.hr2 T W.hqp W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) t0
    (by have := W.hrN; omega) t ?_
  rw [hy] at h1 ⊢
  rcases h1 with h1 | h1
  · right
    obtain ⟨k, hk1, hk2, hk3⟩ := W.hsepL _ (by omega) h1
    exact ⟨h1, by omega, k, hk1, hk2, hk3⟩
  · left
    obtain ⟨k, hk1, hk2, hk3⟩ := W.hsepR _ h1 (by omega)
    exact ⟨by omega, by omega, k, hk1, hk2, hk3⟩

set_option maxHeartbeats 1600000 in
theorem WinC.killR (W : WinC c hc q o r p N t0 tv w0 m) (T : TwoTermData Fr q o)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ t ∈ Finset.univ.filter (fun j : Fin ((altGeom c hc).geometry r).k =>
        ((altGeom c hc).geometry r).xs j < t0 ∨ tv < ((altGeom c hc).geometry r).xs j),
      wedgeR (altLift c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN)) Fr
        (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
        (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
          (altLift c hc W.hr2 T W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN)).toBlocks₁₁ t0
          (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0 := by
  intro t ht
  have hs := altGeom_hybShape c hc W.hr2
  have hk : ((altGeom c hc).geometry r).k = m := alt_k_eq W.hr2 W.hbs
  have hx := hs.xs_eq t
  have ht' := t.2
  have h1 := (Finset.mem_filter.1 ht).2
  have := W.hpm; have := W.ht0b; have := W.ht0r; have := W.ht0tv
  refine altWedgeR_ne_of_sep W.hr2 T W.hqp W.hNp hsq hnorm hnorm0 (W.hbs ▸ W.hrN) t0
    (by have := W.hrN; omega) t ?_
  rw [hx] at h1 ⊢
  rcases h1 with h1 | h1
  · right
    obtain ⟨k, hk1, hk2, hk3⟩ := W.hsepL _ (by omega) h1
    exact ⟨h1, by omega, k, hk1, hk2, hk3⟩
  · left
    obtain ⟨k, hk1, hk2, hk3⟩ := W.hsepR _ h1 (by omega)
    exact ⟨by omega, by omega, k, hk1, hk2, hk3⟩

set_option maxHeartbeats 1600000 in
/-- The outside border nodes (residue not in `[w₀, t_v]`) are killed columns or rows. -/
theorem WinC.out_sub (W : WinC c hc q o r p N t0 tv w0 m) :
    (outNodes p r m w0 tv).image (fun t : ℕ => ((t : ℕ) : ZMod p)) ⊆
      ((Finset.univ.filter (fun j : Fin ((altGeom c hc).geometry r).k =>
          ((altGeom c hc).geometry r).ys j < t0 ∨ tv < ((altGeom c hc).geometry r).ys j)).image
          (fun t => ((((altGeom c hc).geometry r).ys t : ℕ) : ZMod p)) ∪
        (Finset.univ.filter (fun j : Fin ((altGeom c hc).geometry r).k =>
          ((altGeom c hc).geometry r).xs j < t0 ∨ tv < ((altGeom c hc).geometry r).xs j)).image
          (fun t => ((((altGeom c hc).geometry r).xs t : ℕ) : ZMod p))) := by
  have hs := altGeom_hybShape c hc W.hr2
  have hk : ((altGeom c hc).geometry r).k = m := alt_k_eq W.hr2 W.hbs
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
  obtain ⟨⟨hxa, hxb⟩, hxn⟩ := mem_outNodes.1 hx
  have hout : x < t0 ∨ tv < x := by
    by_contra hcon
    exact hxn ⟨x, Finset.mem_Icc.2 ⟨by have := W.hw0; omega, by omega⟩, rfl⟩
  by_cases hpar : (x - r) % 2 = 0
  · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨(x - r) / 2, by omega⟩, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs.xs_eq]
      show r + 2 * ((x - r) / 2) < t0 ∨ tv < r + 2 * ((x - r) / 2)
      omega
    · show ((((altGeom c hc).geometry r).xs ⟨(x - r) / 2, _⟩ : ℕ) : ZMod p) = _
      rw [hs.xs_eq]
      congr 2
      show r + 2 * ((x - r) / 2) = x
      omega
  · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨⟨(x - r) / 2, by omega⟩, ?_, ?_⟩)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hs.ys_eq]
      show r + 2 * ((x - r) / 2) + 1 < t0 ∨ tv < r + 2 * ((x - r) / 2) + 1
      omega
    · show ((((altGeom c hc).geometry r).ys ⟨(x - r) / 2, _⟩ : ℕ) : ZMod p) = _
      rw [hs.ys_eq]
      congr 2
      show r + 2 * ((x - r) / 2) + 1 = x
      omega

end Kills

section Cells

variable {r p N t0 tv w0 m : ℕ} [Fact p.Prime]

set_option maxHeartbeats 1600000 in
/-- **The generic closed cell without top extension** (`w₀ = t₀`). -/
noncomputable def cellNo (T : TwoTermData Fr q o) (W : WinC c hc q o r p N t0 tv w0 m)
    (hw : w0 = t0) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0)
    (hsing : NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) t0 (tv - t0)) :
    Cell3 c hc Fr q o T r p where
  hr := W.hr2
  N := N
  hNp := W.hNp
  hsq := hsq
  hnorm := hnorm
  hnorm0 := hnorm0
  hrN := W.hbs ▸ W.hrN
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
  TC := Finset.univ.filter fun j => ((altGeom c hc).geometry r).ys j < t0 ∨
    tv < ((altGeom c hc).geometry r).ys j
  TR := Finset.univ.filter fun j => ((altGeom c hc).geometry r).xs j < t0 ∨
    tv < ((altGeom c hc).geometry r).xs j
  hwC := W.killC T hsq hnorm hnorm0
  hwR := W.killR T hsq hnorm hnorm0
  u := (tv + 1 - w0) + (2 * m - beta3 m r p w0 tv)
  hu := by
    have h1 := card_union_window (p := p) (r := r) (m := m) (w0 := w0) (w1 := tv)
      (by have := W.hp2; omega) W.hwin W.hpm W.hR (by have := W.htvp; omega)
    have h2 := W.out_sub
    subst hw
    refine h1.trans (Finset.card_le_card (Finset.union_subset_union (subset_refl _) h2))

set_option maxHeartbeats 1600000 in
theorem cellNo_bound (T : TwoTermData Fr q o) (W : WinC c hc q o r p N t0 tv w0 m)
    (hw : w0 = t0) (hsq) (hnorm) (hnorm0) (hsing) :
    (cellNo T W hw hsq hnorm hnorm0 hsing).bound = closedBound m r p t0 tv w0 := by
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
  have e : (cellNo T W hw hsq hnorm hnorm0 hsing).u =
      (tv + 1 - w0) + (2 * m - beta3 m r p w0 tv) := rfl
  have e1 : (cellNo T W hw hsq hnorm hnorm0 hsing).t0 = t0 := rfl
  have e2 : (cellNo T W hw hsq hnorm hnorm0 hsing).tv = tv := rfl
  rw [e, e1, e2, hRows, hCols, hk, Fintype.card_sum, hC, Fintype.card_fin, closedBound]
  omega

set_option maxHeartbeats 1600000 in
/-- **The generic closed cell with top extension** (`t₀ = r`, credited window `[w₀, t_v]`). -/
noncomputable def cellExt (T : TwoTermData Fr q o) (W : WinC c hc q o r p N t0 tv w0 m)
    (ht0 : t0 = r) (hwr : w0 < r) (hqd : w0 / p = r / p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0)
    (hsing : NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) t0 (tv - t0))
    (hwd : NoSingWin (twoTermPoleData T W.hNp.le hsq hnorm hnorm0) w0 (r - w0)) :
    UFCellF c hc Fr q o T r p where
  hr := W.hr2
  N := N
  hNp := W.hNp
  hsq := hsq
  hnorm := hnorm
  hnorm0 := hnorm0
  hrN := W.hbs ▸ W.hrN
  hp := by have := W.hpm; have := W.hbs; omega
  hp2 := by have := W.hp2; omega
  ho := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd W.ho0 hd; have := W.hop; omega
  hq := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd W.hq0 hd; have := W.hqp; omega
  t0 := t0
  tmax := tv
  ht0N := by have := W.ht0b; have := W.hrN; omega
  hrt := W.ht0r
  htm := W.htvp
  hdiv := W.hdiv
  hw := hsing
  TC := Finset.univ.filter fun j => ((altGeom c hc).geometry r).ys j < t0 ∨
    tv < ((altGeom c hc).geometry r).ys j
  TR := Finset.univ.filter fun j => ((altGeom c hc).geometry r).xs j < t0 ∨
    tv < ((altGeom c hc).geometry r).xs j
  hwC := W.killC T hsq hnorm hnorm0
  hwR := W.killR T hsq hnorm hnorm0
  tv := tv
  htv0 := W.ht0tv
  htv := W.htvp
  htvN := W.htvN
  htvd := W.hdiv
  hwv := hsing
  δ₁ := 1
  δ₂ := r - w0
  hδ12 := by omega
  hδ2 := by omega
  hlt := by have := W.hr0; omega
  hr3 := by have := W.hwin; have := W.ht0tv; omega
  hqd := by
    have e : t0 - (r - w0) = w0 := by omega
    rw [e, hqd, ht0]
  hwd := by
    have e : t0 - (r - w0) = w0 := by omega
    rw [e]; exact hwd
  u := (tv + 1 - w0) + (2 * m - beta3 m r p w0 tv)
  hu := by
    have h1 := card_union_window (p := p) (r := r) (m := m) (w0 := w0) (w1 := tv)
      (by have := W.hp2; omega) W.hwin W.hpm W.hR (by have := W.htvp; omega)
    have h2 := W.out_sub
    have e : Finset.Icc t0 tv ∪ Finset.Icc (t0 - (r - w0)) (t0 - 1) = Finset.Icc w0 tv := by
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; have := W.ht0tv; omega
    rw [e]
    exact h1.trans (Finset.card_le_card (Finset.union_subset_union (subset_refl _) h2))

set_option maxHeartbeats 1600000 in
theorem cellExt_bound (T : TwoTermData Fr q o) (W : WinC c hc q o r p N t0 tv w0 m)
    (ht0 : t0 = r) (hwr : w0 < r) (hqd) (hsq) (hnorm) (hnorm0) (hsing) (hwd) :
    (cellExt T W ht0 hwr hqd hsq hnorm hnorm0 hsing hwd).bound = closedBound m r p t0 tv w0 := by
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
  unfold UFCellF.bound UFCellF.sigma
  have e : (cellExt T W ht0 hwr hqd hsq hnorm hnorm0 hsing hwd).u =
      (tv + 1 - w0) + (2 * m - beta3 m r p w0 tv) := rfl
  have e1 : (cellExt T W ht0 hwr hqd hsq hnorm hnorm0 hsing hwd).t0 = t0 := rfl
  have e2 : (cellExt T W ht0 hwr hqd hsq hnorm hnorm0 hsing hwd).tmax = tv := rfl
  rw [e, e1, e2, hRows, hCols, hk, Fintype.card_sum, hC, Fintype.card_fin, closedBound]
  omega

end Cells

end CatalanCore.Uniform.Content.UFSimple
