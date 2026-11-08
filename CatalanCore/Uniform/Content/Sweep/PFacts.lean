module

public import CatalanCore.Uniform.Content.Sweep.CellAction

@[expose] public section

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support

/-!
# Arithmetic facts of the sweep: F1, F2, the halves, the step of `σ` (lane H, wave H2b; ledger P204)

Everything is over any commutative `ℤ_(p)`-algebra `R` (`toR` of `CellAction`).  `Qent ξ s t` is the entry of
`p³ H = ξ·Id + p³ M` of the plane 2 datum.  With `σ(c) = p² S(c)` (`sigR`), `g(c) = p³ G(c)` (`ggR`) and the
period matrix `Bm ξ h l j` (the matrix of the cell operator on the half `h`):

* **F1** (`F1`): for congruent nodes `s ≡ t`, `Qent s t ≡ Bm (half s) (s/p) (t/p)  (mod p²)`.
* **F2** (`F2`): for non-congruent `n, t`, `Qent n t ≡ p (σ(c_t) - σ(c_n)) (t - n)⁻¹  (mod p²)`.
* `sigR_halves`, `ggR_halves`, `Bm_halves`: the two halves agree modulo `p`.
* `sig_step`: `p² (S(j+1,h) - S(j,h)) ≡ -v/(j+1)²  (mod p)`, the hypothesis of Theorem ND.
-/
namespace CatalanCore.Uniform.Content.Sweep

section Facts

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R]

/-- `p² S(c)` and `p³ G(c)` of a cell, as elements of `R`. -/
noncomputable def sigR (c : ℕ × ℕ) : R := toR p ((p : ℚ) ^ 2 * Scell v u p c)
noncomputable def ggR (c : ℕ × ℕ) : R := toR p ((p : ℚ) ^ 3 * Gcell v u p c)

/-- The period matrix `B^h(l, j)` of the sweep (entry of the cell operator `𝐁` on half `h`):
`ξ + p³ G(l,h)` on the diagonal, `p² (S(l,h) - S(j,h))/(l - j)` off it. -/
noncomputable def Bm (ξ : R) (h l j : ℕ) : R :=
  if l = j then ξ + ggR (p := p) v u (l, h) else
    toR p ((p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j))

theorem sig_cell_mem (hodd : p % 2 = 1) (hN : 2 * N < p * p) {t : ℕ} (ht : t < N) :
    (p : ℚ) ^ 2 * Scell v u p (cell p u t) ∈ LocRing p := by
  have h := PF_diff_period v u hN (Nat.zero_le t) ht
  have h0 : PF v u p 0 = 0 := by simp [PF]
  rw [h0, sub_zero] at h
  rw [← PF_eq_Scell v u hodd t]
  exact h

/-- **F1** (congruent nodes): the entry of `p³ H` is the period matrix modulo `p²`. -/
theorem F1 (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (ξ : R) {s t : ℕ}
    (hs : s < N) (ht : t < N) (hm : s % p = t % p) :
    (p : R) ^ 2 ∣ Qent (p := p) v u ξ s t - Bm (p := p) v u ξ (half p u s) (s / p) (t / p) := by
  have hp0 : 0 < p := hp.out.pos
  have hhalf : half p u t = half p u s := by unfold half; rw [hm]
  by_cases hst : s = t
  · subst hst
    unfold Qent Bm
    rw [if_pos rfl, if_pos rfl]
    have hq := q_mem v u hN hs hs
    have hG := G_mem v u hodd hN hs
    have e1 : (p : ℚ) ^ 3 * Lm v u s s - (p : ℚ) ^ 3 * Gcell v u p (cell p u s) =
        (p : ℚ) ^ 3 * (-RE v u p s) := by
      unfold Lm lw
      rw [if_pos rfl, e_eq v u (p := p), ← PE_eq_Gcell v u hodd s]
      ring
    have hd : Dv p 3 ((p : ℚ) ^ 3 * Lm v u s s - (p : ℚ) ^ 3 * Gcell v u p (cell p u s)) := by
      rw [e1]; exact Dv.intro ((LocRing p).neg_mem (RE_mem v u s))
    have key : (p : R) ^ 3 ∣ toR p ((p : ℚ) ^ 3 * Lm v u s s) - toR p ((p : ℚ) ^ 3 * Gcell v u p (cell p u s)) := by
      rw [← toR_sub hq hG]; exact toR_dvd hd
    have hc : cell p u s = (s / p, half p u s) := rfl
    have e : ξ + toR p ((p : ℚ) ^ 3 * Lm v u s s) - (ξ + ggR (p := p) v u (s / p, half p u s)) =
        toR p ((p : ℚ) ^ 3 * Lm v u s s) - toR p ((p : ℚ) ^ 3 * Gcell v u p (cell p u s)) := by
      unfold ggR; rw [← hc]; ring
    rw [e]
    exact (pow_dvd_pow (p : R) (by norm_num : 2 ≤ 3)).trans key
  · -- distinct congruent nodes
    have hne : s ≠ t := hst
    have hls : s / p ≠ t / p := by
      intro h
      apply hne
      have h1 := Nat.div_add_mod s p
      have h2 := Nat.div_add_mod t p
      rw [h, hm] at h1
      omega
    unfold Qent Bm
    rw [if_neg hne, if_neg hls, zero_add]
    set h := half p u s with hh
    have hPFt : PF v u p t = Scell v u p (t / p, h) := by
      rw [PF_eq_Scell v u hodd t]; unfold cell; rw [hhalf]
    have hPFs : PF v u p s = Scell v u p (s / p, h) := by
      rw [PF_eq_Scell v u hodd s]; rfl
    have hD : ((t : ℚ) - s) = (((t / p : ℕ) : ℚ) - ((s / p : ℕ) : ℚ)) * p := by
      have h1 := Nat.div_add_mod s p
      have h2 := Nat.div_add_mod t p
      rw [hm] at h1
      have : (t : ℚ) = ((t / p : ℕ) : ℚ) * p + (t % p : ℕ) := by
        exact_mod_cast (by rw [mul_comm]; exact h2.symm : t = (t / p) * p + t % p)
      have h1' : (s : ℚ) = ((s / p : ℕ) : ℚ) * p + (t % p : ℕ) := by
        exact_mod_cast (by rw [mul_comm]; exact h1.symm : s = (s / p) * p + t % p)
      linarith
    have hlsq : (((t / p : ℕ) : ℚ) - ((s / p : ℕ) : ℚ)) ≠ 0 :=
      sub_ne_zero.2 (by exact_mod_cast (Ne.symm hls))
    have hlsq' : (((s / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ)) ≠ 0 :=
      sub_ne_zero.2 (by exact_mod_cast hls)
    have hp0q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hDne : ((t : ℚ) - s) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hne))
    have hLm : Lm v u s t = ((PF v u p t - PF v u p s) + (RF v u p t - RF v u p s)) / ((t : ℚ) - s) := by
      unfold Lm lw
      rw [if_neg hne, f_eq v u (p := p), f_eq v u (p := p)]
      congr 1; ring
    set T : ℚ := (p : ℚ) ^ 2 * (Scell v u p (s / p, h) - Scell v u p (t / p, h)) /
      (((s / p : ℕ) : ℚ) - ((t / p : ℕ) : ℚ)) with hT
    have hkey : (p : ℚ) ^ 3 * Lm v u s t - T =
        (p : ℚ) ^ 3 * ((RF v u p t - RF v u p s) / ((t : ℚ) - s)) := by
      rw [hLm, hPFt, hPFs, hT, hD]
      field_simp
      ring
    have hRd := RF_div_mem v u hp5 hN hs ht hne
    have hd : Dv p 3 ((p : ℚ) ^ 3 * Lm v u s t - T) := by
      rw [hkey]; exact Dv.intro hRd
    have hq := q_mem v u hN hs ht
    have hTm : T ∈ LocRing p := by
      have : T = (p : ℚ) ^ 3 * Lm v u s t - (p : ℚ) ^ 3 * ((RF v u p t - RF v u p s) / ((t : ℚ) - s)) := by
        rw [← hkey]; ring
      rw [this]
      have hp3 : ((p : ℚ) ^ 3) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) ((p : ℤ) ^ (3 : ℕ))
      exact (LocRing p).sub_mem hq ((LocRing p).mul_mem hp3 hRd)
    have := toR_dvd (R := R) hd
    rw [toR_sub hq hTm] at this
    exact (pow_dvd_pow (p : R) (by norm_num : 2 ≤ 3)).trans this




/-- **F2** (non-congruent nodes): the entry of `p³ H` is `p (σ(c_t) - σ(c_n))/(t - n)` modulo `p²`,
with `σ = p² S` and the inverse of the integer `t - n` taken in `ℤ_(p)`. -/
theorem F2 (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p) (ξ : R) {n t : ℕ}
    (hn : n < N) (ht : t < N) (hm : n % p ≠ t % p) :
    (p : R) ^ 2 ∣ Qent (p := p) v u ξ n t -
      (p : R) * (sigR (p := p) v u (cell p u t) - sigR (p := p) v u (cell p u n)) *
        toR p ((((t : ℚ) - n)⁻¹)) := by
  have hne : n ≠ t := fun h => hm (by rw [h])
  have hz : ¬ (p : ℤ) ∣ (t : ℤ) - n := by
    intro hd
    apply hm
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((t : ℤ) - n) p).2 hd
    push_cast at this
    rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff'] at this
    exact this.symm
  have hinv : (((t : ℚ) - n)⁻¹) ∈ LocRing p := by
    have := inv_int_mem (p := p) hz; push_cast at this; exact this
  have hpm : ((p : ℚ)) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)
  have hs1 := sig_cell_mem v u hodd hN ht
  have hs2 := sig_cell_mem v u hodd hN hn
  have hsd : sdiff v u p n (cell p u t) ∈ LocRing p := by
    unfold sdiff; rw [mul_sub]; exact (LocRing p).sub_mem hs1 hs2
  have hP : (p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹) ∈ LocRing p :=
    (LocRing p).mul_mem ((LocRing p).mul_mem hpm hsd) hinv
  have hq := q_mem v u hN hn ht
  have hd := q_decomp v u hodd hp5 hN hn ht hne
  have := toR_dvd (R := R) hd
  rw [toR_sub hq hP] at this
  have e1 : toR p ((p : ℚ) * sdiff v u p n (cell p u t) * (((t : ℚ) - n)⁻¹)) =
      (p : R) * (sigR (p := p) v u (cell p u t) - sigR (p := p) v u (cell p u n)) * toR p ((((t : ℚ) - n)⁻¹)) := by
    rw [toR_mul ((LocRing p).mul_mem hpm hsd) hinv, toR_mul hpm hsd, toR_p]
    congr 2
    unfold sdiff sigR
    rw [mul_sub, toR_sub hs1 hs2]
  have hQ : Qent (p := p) v u ξ n t = toR p ((p : ℚ) ^ 3 * Lm v u n t) := by
    unfold Qent; rw [if_neg hne, zero_add]
  rw [hQ, ← e1]
  exact (pow_dvd_pow (p : R) (by norm_num : 2 ≤ 3)).trans this




/-- The step of the polar sum at the period boundary: `p² (S(j+1,h) - S(j,h)) ≡ -v/(j+1)² (mod p)`. -/
theorem sig_step (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j h : ℕ} (hh : h ≤ 1)
    (hj : (j + 2) * p ≤ N) (hjp : j + 1 < p) :
    Dv p 1 ((p : ℚ) ^ 2 * (Scell v u p (j + 1, h) - Scell v u p (j, h)) + (v : ℚ) / ((j : ℚ) + 1) ^ 2) := by
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨c0, hc0⟩ : ∃ c0, c0 = h * ((p + 1) / 2) := ⟨_, rfl⟩
  have hhalf : c0 < p := by
    have := hp.out.two_le; rw [hc0]; interval_cases h <;> simp <;> omega
  have hcs : ∀ j', cstart p (j', h) = j' * p + c0 := by intro j'; simp [cstart, hc0]
  set a := cstart p (j, h) with ha
  have ha' : a = j * p + c0 := hcs j
  have hb' : cstart p (j + 1, h) = a + p := by rw [hcs, ha']; ring
  have e1 : (j + 1) * p = j * p + p := by ring
  have e2 : (j + 2) * p = j * p + 2 * p := by ring
  set K := (j + 1) * p with hK
  set F : ℕ → ℚ := fun i => PF v u p i - (if K ≤ i then T1 v u K else 0) with hF
  have hab : a ≤ a + p := by omega
  have hstep : ∀ i, a ≤ i → i < a + p → Vp p 1 (F (i + 1) - F i) := by
    intro i hai hib
    have hPs := PF_step v u (p := p) i
    have e : F (i + 1) - F i = polF v u p (i + 1) - (if i + 1 = K then T1 v u K else 0) := by
      simp only [hF]
      by_cases h1 : K ≤ i
      · rw [if_pos h1, if_pos (by omega), if_neg (by omega)]; linarith
      · by_cases h2 : i + 1 = K
        · rw [if_neg h1, if_pos (by omega), if_pos h2]; linarith
        · rw [if_neg h1, if_neg (by omega), if_neg h2]; linarith
    rw [e]
    by_cases h2 : i + 1 = K
    · rw [if_pos h2]
      unfold polF
      have hdK : p ∣ i + 1 := by rw [h2, hK]; exact Dvd.intro_left _ rfl
      rw [if_pos hdK]
      have hnd : ¬ p ∣ 2 * (i + 1) - 1 := by
        intro hd
        rw [h2, hK] at hd
        have h3 : p ∣ 2 * ((j + 1) * p) := Dvd.dvd.mul_left (Dvd.intro_left _ rfl) 2
        have h4 : 2 * ((j + 1) * p) - (2 * ((j + 1) * p) - 1) = 1 := by
          have : 1 ≤ 2 * ((j + 1) * p) := by omega
          omega
        have := Nat.dvd_sub h3 hd
        rw [h4] at this
        exact hp.out.one_lt.ne' (Nat.dvd_one.1 this)
      rw [if_neg hnd, h2]
      simp [Vp.zero]
    · rw [if_neg h2, sub_zero]
      have hnd : ¬ p ∣ i + 1 := by
        intro ⟨m, hm⟩
        have c1 : p * j = j * p := by ring
        have c3 : p * (j + 2) = j * p + 2 * p := by ring
        have h7 : j < m := by
          by_contra hcon
          have := Nat.mul_le_mul_left p (not_lt.1 hcon)
          omega
        have h8 : m < j + 2 := by
          by_contra hcon
          have := Nat.mul_le_mul_left p (not_lt.1 hcon)
          omega
        have : m = j + 1 := by omega
        apply h2; rw [hm, this, hK]; ring
      exact polF_pole_nomult v u (by omega) (by omega) hnd
  have hV := Vp_telescope F 1 a (a + p) hab hstep
  have hFb : F (a + p) - F a = PF v u p (a + p) - PF v u p a - T1 v u K := by
    simp only [hF]
    have hKb : K ≤ a + p := by omega
    have hKa : ¬ K ≤ a := by omega
    rw [if_pos hKb, if_neg hKa]; ring
  rw [hFb] at hV
  have hsc : Scell v u p (j + 1, h) - Scell v u p (j, h) = PF v u p (a + p) - PF v u p a := by
    unfold Scell; rw [hb']
  rw [hsc]
  have hT1 : (p : ℚ) ^ 2 * T1 v u K = ((u : ℚ) * p) * (((j + 1 : ℕ) : ℚ))⁻¹ - (v : ℚ) / ((j : ℚ) + 1) ^ 2 := by
    have hp0q : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    have hj1 : ((j : ℚ) + 1) ≠ 0 := by positivity
    unfold T1; rw [hK]; push_cast; field_simp
  have hinv := inv_natCast_mem_locRing (ℓ := p) (m := j + 1) (by
    intro hd; have := Nat.le_of_dvd (by omega) hd; omega)
  have hu1 : ((u : ℚ) * p) * (((j + 1 : ℕ) : ℚ))⁻¹ ∈ LocRing p :=
    (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (u * p)) hinv
  have hV' := Dv.of_Vp (k := 1) hV
  have e : (p : ℚ) ^ 2 * (PF v u p (a + p) - PF v u p a) + (v : ℚ) / ((j : ℚ) + 1) ^ 2 =
      (p : ℚ) ^ (1 + 1) * (PF v u p (a + p) - PF v u p a - T1 v u K) +
        (((u : ℚ) * p) * (((j + 1 : ℕ) : ℚ))⁻¹) := by
    have : (p : ℚ) ^ (1 + 1) * (PF v u p (a + p) - PF v u p a - T1 v u K) =
        (p : ℚ) ^ 2 * (PF v u p (a + p) - PF v u p a) - (p : ℚ) ^ 2 * T1 v u K := by ring
    rw [this, hT1]; ring
  rw [e]
  have hu2 : Dv p 1 (((u : ℚ) * p) * (((j + 1 : ℕ) : ℚ))⁻¹) := by
    have : ((u : ℚ) * p) * (((j + 1 : ℕ) : ℚ))⁻¹ = (p : ℚ) ^ 1 * ((u : ℚ) * (((j + 1 : ℕ) : ℚ))⁻¹) := by ring
    rw [this]
    exact Dv.intro ((LocRing p).mul_mem (int_mem_locRing u) hinv)
  exact Dv.add hV' hu2




/-! ### The two halves agree modulo `p` -/

theorem cstart_lt (hodd : p % 2 = 1) {j h : ℕ} (hh : h ≤ 1) (hj : (j + 1) * p ≤ N) : cstart p (j, h) < N := by
  have hm : (p + 1) / 2 < p := by have := hp.out.two_le; omega
  unfold cstart
  have e : (j + 1) * p = j * p + p := by ring
  interval_cases h <;> simp <;> omega

theorem sig_mem_cell (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j h : ℕ} (hh : h ≤ 1)
    (hj : (j + 1) * p ≤ N) : (p : ℚ) ^ 2 * Scell v u p (j, h) ∈ LocRing p := by
  have h0 : PF v u p 0 = 0 := by simp [PF]
  have := PF_diff_period v u hN (Nat.zero_le (cstart p (j, h))) (cstart_lt hodd hh hj)
  rw [h0, sub_zero] at this
  exact this

theorem gg_mem_cell (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j h : ℕ} (hh : h ≤ 1)
    (hj : (j + 1) * p ≤ N) : (p : ℚ) ^ 3 * Gcell v u p (j, h) ∈ LocRing p := by
  exact G_mem_cell v u hodd hN hj hh

theorem sigR_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j : ℕ} (hj : (j + 1) * p ≤ N) :
    (p : R) ∣ sigR (p := p) v u (j, 1) - sigR (p := p) v u (j, 0) := by
  unfold sigR
  rw [← toR_sub (sig_mem_cell v u hodd hN (by norm_num) hj) (sig_mem_cell v u hodd hN (by norm_num) hj)]
  have := toR_dvd (R := R) (Scell_halves v u hodd hN hj)
  rw [mul_sub] at this
  simpa using this

theorem ggR_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) {j : ℕ} (hj : (j + 1) * p ≤ N) :
    (p : R) ∣ ggR (p := p) v u (j, 0) - ggR (p := p) v u (j, 1) := by
  unfold ggR
  rw [← toR_sub (gg_mem_cell v u hodd hN (by norm_num) hj) (gg_mem_cell v u hodd hN (by norm_num) hj)]
  have := toR_dvd (R := R) (Gcell_halves v u hodd hN hj)
  rw [mul_sub] at this
  simpa using this

theorem Bm_halves (hodd : p % 2 = 1) (hN : 2 * N < p * p) (ξ : R) {l j : ℕ}
    (hl : (l + 1) * p ≤ N) (hj : (j + 1) * p ≤ N) :
    (p : R) ∣ Bm (p := p) v u ξ 1 l j - Bm (p := p) v u ξ 0 l j := by
  have hp0 : 0 < p := hp.out.pos
  unfold Bm
  by_cases hlj : l = j
  · subst hlj
    simp only [if_true]
    have := ggR_halves (R := R) v u hodd hN hl
    have e : ξ + ggR (p := p) v u (l, 1) - (ξ + ggR (p := p) v u (l, 0)) =
        -(ggR (p := p) v u (l, 0) - ggR (p := p) v u (l, 1)) := by ring
    rw [e]; exact (dvd_neg).2 this
  · simp only [if_neg hlj]
    have hlp : l < p := by nlinarith
    have hjp : j < p := by nlinarith
    have hu := unit_diff (p := p) hlj hlp hjp
    have hs : ∀ h, h ≤ 1 → ∀ j', (j' + 1) * p ≤ N →
        (p : ℚ) ^ 2 * Scell v u p (j', h) ∈ LocRing p := fun h hh j' hj' => sig_mem_cell v u hodd hN hh hj'
    have hA : ∀ h, h ≤ 1 → (p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j) ∈ LocRing p := by
      intro h hh
      have e : (p : ℚ) ^ 2 * (Scell v u p (l, h) - Scell v u p (j, h)) / ((l : ℚ) - j) =
          ((p : ℚ) ^ 2 * Scell v u p (l, h) - (p : ℚ) ^ 2 * Scell v u p (j, h)) * (((l : ℚ) - j)⁻¹) := by
        rw [mul_sub, div_eq_mul_inv]
      rw [e]
      exact (LocRing p).mul_mem ((LocRing p).sub_mem (hs h hh l hl) (hs h hh j hj)) hu
    rw [← toR_sub (hA 1 (by norm_num)) (hA 0 (by norm_num))]
    have hd : Dv p 1 ((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j) -
        (p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j)) := by
      have e : (p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (j, 1)) / ((l : ℚ) - j) -
          (p : ℚ) ^ 2 * (Scell v u p (l, 0) - Scell v u p (j, 0)) / ((l : ℚ) - j) =
          (((l : ℚ) - j)⁻¹) * (((p : ℚ) ^ 2 * (Scell v u p (l, 1) - Scell v u p (l, 0))) -
            ((p : ℚ) ^ 2 * (Scell v u p (j, 1) - Scell v u p (j, 0)))) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      rw [e]
      exact Dv.mul_mem hu (Dv.sub (Scell_halves v u hodd hN hl) (Scell_halves v u hodd hN hj))
    simpa using toR_dvd hd

end Facts

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.F1
#print axioms CatalanCore.Uniform.Content.Sweep.F2
#print axioms CatalanCore.Uniform.Content.Sweep.sig_step
#print axioms CatalanCore.Uniform.Content.Sweep.Bm_halves
