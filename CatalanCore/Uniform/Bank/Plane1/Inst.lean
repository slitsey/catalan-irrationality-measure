module

public import CatalanCore.Uniform.Bank.Plane1.PoleData
public import CatalanCore.Uniform.Content.BankShared.KTerm.Bundle
public import CatalanCore.Arith.Hybrid.SingLev
public import CatalanFrames.P6.Content
public import CatalanFrames.HybCommon.Numer

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The hybrid instance of the plane frames and their pole bundle (wave H4; ledger N7)

`planeInst σ a b c h0 : HybInst (planeFrame σ a b c h0)` is the **weight-free level instance** of the plane
theorem.  Its level is the singular count

  `lev q A = #{k ∈ [1, A] : q ∣ k (3k - ρ) ...}`  (precisely: `∃ i, q ∣ lin i k`, some atom has a pole of order
  divisible by `q` at `k`),

which reads the shifts only, so one instance (hence one tropical price, one catalogue and one cover) serves every
weight triple; cancellations among the weights are not used.  The instance cannot be `HybInst.ofSing` (the block
count of `Φ(k) = k (3k - ρ) (2k - 1)` has `Ebd N = 6 N³`, outside the cubic numerology `BadInfo`), nor `ofExact`
(its levels cancel and depend on the weights); it is built directly with `Ebd N = 3 N` and the same
proofs as `sing_off_val`, `sing_diag_val`, but with the valuation of each of the three *linear* forms counted
separately.

* `planeCD` (the `ContentData`): `Φ(k) = lin₀ lin₁ lin₂`, bad primes `{2, 3}`, norm `1`, `kq q` the first `k` with
  `q ∣ Φ(k)`, weight `small h = 2^⌊log₂ 3h⌋ 3^⌊log₃ 3h⌋ ≤ 9 h²`;
* `planeInst`, `planeInst_badInfo` (`BadInfo (planeInst …) 3 2`);
* `planeBundle σ a b c h0 : KBundle` (N7): the frame, `ρ`, the instances (constant in `(r, m)`), `DiagOK`, `BadInfo`,
  and the pole data of `PoleData.lean`. -/

namespace CatalanCore.Uniform.Bank.Plane1
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanCore.Uniform.Content.BankShared.KTerm

/-! ### Closed forms of `Δ`, `D` and the three linear forms -/

section Forms

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

/-- The three linear forms `3k - ρ`, `2k - 1`, `k` (atoms `0, 1, 2`). -/
def pl (σ : Support) : ℕ → ℕ → ℕ
  | 0, k => 3 * k - σ.rho
  | 1, k => 2 * k - 1
  | _, k => k

theorem lin_plane (i : Fin (planeFrame σ a b c h0).d) {k : ℕ} (hk : 1 ≤ k) :
    lin (planeFrame σ a b c h0) i k = pl σ i.1 k := by
  have h := lin_cast_int i hk
  obtain ⟨j, hj⟩ := i
  have hj3 : j < 3 := hj
  have hr : σ.rho ≤ 2 := by cases σ <;> simp [Support.rho]
  interval_cases j
  · change (lin (planeFrame σ a b c h0) ⟨0, hj⟩ k : ℤ) =
      ((σ.shift.den : ℤ) * ((k : ℤ) - 1) + σ.shift.num) at h
    rw [shift_den, shift_num] at h
    show _ = 3 * k - σ.rho
    omega
  · change (lin (planeFrame σ a b c h0) ⟨1, hj⟩ k : ℤ) =
      (((1 / 2 : ℚ).den : ℤ) * ((k : ℤ) - 1) + (1 / 2 : ℚ).num) at h
    rw [half_den, half_num] at h
    show _ = 2 * k - 1
    omega
  · change (lin (planeFrame σ a b c h0) ⟨2, hj⟩ k : ℤ) =
      (((1 : ℚ).den : ℤ) * ((k : ℤ) - 1) + (1 : ℚ).num) at h
    rw [one_den, one_num] at h
    show _ = k
    omega

end Forms

/-! ### The weight-free level and its valuation counts (any frame with shift denominators `≤ 3`) -/

section Levels

variable {Fr : Frame}

open Classical in
/-- The singular count: the number of `k ∈ [1, A]` such that some atom has a pole at `k` divisible by `q`. -/
noncomputable def levF (Fr : Frame) (q A : ℕ) : ℕ :=
  ((Icc 1 A).filter (fun k => ∃ i : Fin Fr.d, q ∣ lin Fr i k)).card

theorem levF_lt {q lo hi k : ℕ} (hk : k ∈ Ioc lo hi) (hs : ∃ i : Fin Fr.d, q ∣ lin Fr i k) :
    levF Fr q lo < levF Fr q hi := by
  classical
  unfold levF
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · have := Finset.mem_Ioc.mp hk
    refine ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, this.2⟩, hs⟩
    · simp only [Finset.mem_filter, Finset.mem_Icc, not_and]
      intro h; omega
  · intro x hx
    have := Finset.mem_Ioc.mp hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨hx.1.1, by omega⟩, hx.2⟩

theorem levF_pos {q c k : ℕ} (hk : k ∈ Icc 1 c) (hs : ∃ i : Fin Fr.d, q ∣ lin Fr i k) :
    0 < levF Fr q c := by
  classical
  unfold levF
  exact Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hs⟩⟩

theorem levF_zero {Q : ℕ} (hden : ∀ i, (Fr.μ i).den ≤ Q) {q N a : ℕ} (hq : Q * N < q) (ha : a ≤ N) :
    levF Fr q a = 0 := by
  classical
  unfold levF
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro k hk ⟨i, hd⟩
  have hk' := Finset.mem_Icc.mp hk
  have h1 := Nat.le_of_dvd (lin_pos i hk'.1) hd
  have h2 := lin_le i (hden i) hk'.1
  have hka : Q * k ≤ Q * N := Nat.mul_le_mul_left Q (hk'.2.trans ha)
  omega

theorem fact_lin_le {p E : ℕ} [Fact p.Prime] (i : Fin Fr.d) {k : ℕ} (hk1 : 1 ≤ k)
    (hlin : lin Fr i k < p ^ (E + 1)) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ e ∈ Icc 1 E, p ^ e ∣ lin Fr i k → P e) :
    (lin Fr i k).factorization p ≤ ((Icc 1 E).filter P).card :=
  fact_le_count (Fact.out) (lin_pos i hk1) hlin P hP

theorem pow_sum_Delta_mem {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (W : ℕ)
    (h : ∀ k ∈ s, 1 ≤ k ∧ ∀ i : Fin Fr.d, (lin Fr i k).factorization p ≤ W) :
    (p : ℚ) ^ W * ∑ k ∈ s, Fr.Delta k ∈ LocRing p := by
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  obtain ⟨hk1, hv⟩ := h k hk
  rw [Delta_lin k hk1, Finset.mul_sum]
  refine (LocRing p).sum_mem fun i _ => ?_
  have hm := pow_div_mem (p := p) (lin_pos i hk1) (hv i)
  have e : (p : ℚ) ^ W * (((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ)) =
      (((Fr.w i * ((Fr.μ i).den : ℤ) : ℤ)) : ℚ) * ((p : ℚ) ^ W / (lin Fr i k : ℚ)) := by
    push_cast; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) hm

theorem pow_sum_Dsq_mem {p : ℕ} [Fact p.Prime] (s : Finset ℕ) (W : ℕ)
    (h : ∀ k ∈ s, 1 ≤ k ∧ ∀ i : Fin Fr.d, (lin Fr i k).factorization p ≤ W) :
    (p : ℚ) ^ (2 * W) * ∑ k ∈ s, Fr.Dsq k ∈ LocRing p := by
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun k hk => ?_
  obtain ⟨hk1, hv⟩ := h k hk
  rw [Dsq_lin k hk1, Finset.mul_sum]
  refine (LocRing p).sum_mem fun i _ => ?_
  have hm := pow_div_mem (p := p) (lin_pos i hk1) (hv i)
  have e : (p : ℚ) ^ (2 * W) * (((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (lin Fr i k : ℚ) ^ 2) =
      (((Fr.w i * ((Fr.μ i).den : ℤ) ^ 2 : ℤ)) : ℚ) * ((p : ℚ) ^ W / (lin Fr i k : ℚ)) ^ 2 := by
    push_cast; rw [pow_mul']; ring
  rw [e]
  exact (LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).pow_mem hm 2)

/-- The generic instance: any content table with `L = Q` over a frame with shift denominators `≤ Q`. -/
noncomputable def planeInstOf (Fr : Frame) (cd : ContentData Fr) {Q : ℕ} (hL : cd.L = Q)
    (hden : ∀ i, (Fr.μ i).den ≤ Q) : HybInst Fr where
  cd := cd
  Ebd := fun N => Q * N
  lev := levF Fr
  off_val := by
    intro p _ E N lo hi h1 h2 hlo hhi
    refine off_val_of_jump _ p E lo hi hlo (by omega) ?_
    refine pow_sum_Delta_mem _ _ (fun k hk => ⟨?_, fun i => ?_⟩)
    · have := Finset.mem_Ioc.mp hk; omega
    · have hk' := Finset.mem_Ioc.mp hk
      have hk1 : 1 ≤ k := by omega
      have hlin : lin Fr i k < p ^ (E + 1) := by
        have hlinQ := lin_le i (hden i) hk1
        have hkhi := Nat.mul_le_mul_left Q hk'.2
        have hhiN := Nat.mul_le_mul_left Q (by omega : hi ≤ N)
        omega
      exact fact_lin_le i hk1 hlin _ (fun e _ hdv => ne_of_lt (levF_lt hk ⟨i, hdv⟩))
  diag_val := by
    intro p _ E N a h1 h2 _
    refine diag_val_of_pos _ p E a ?_
    refine pow_sum_Dsq_mem _ _ (fun k hk => ⟨(Finset.mem_Icc.mp hk).1, fun i => ?_⟩)
    have hk' := Finset.mem_Icc.mp hk
    have hlin : lin Fr i k < p ^ (E + 1) := by
      have hlinQ := lin_le i (hden i) hk'.1
      have hka := Nat.mul_le_mul_left Q hk'.2
      have haN := Nat.mul_le_mul_left Q (by omega : a ≤ N)
      omega
    exact fact_lin_le i hk'.1 hlin _ (fun e _ hdv => levF_pos (q := p ^ e) hk ⟨i, hdv⟩)
  lev_large := by
    intro p e N a hp _ he hbig ha
    exact levF_zero hden (by rw [hL] at hbig; exact hbig) ha
  lev_Ebd := by
    intro q N a hbig ha
    exact levF_zero hden (by omega) ha

end Levels

/-! ### The weight for the bad primes `2, 3` (generic) -/

section Small

variable {Fr : Frame}

theorem Mn_symm_gen (Fr : Frame) (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Frame.Mn
  by_cases h : a = b
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), max_comm, min_comm]

/-- `(p^⌊log_p 3h⌋)² · norm · Mn a b` is `p`-integral for `a, b < h`. -/
theorem u2_Mn_mem (p : ℕ) [Fact p.Prime] (hden : ∀ i, (Fr.μ i).den ≤ 3) {h a b : ℕ} (ha : a < h)
    (hb : b < h) :
    ((p : ℚ) ^ Nat.log p (3 * h)) ^ 2 * (Fr.norm * Fr.Mn a b) ∈ LocRing p := by
  set u : ℚ := (p : ℚ) ^ Nat.log p (3 * h) with hu
  have hnorm : (0 : ℚ) < Fr.norm := Fr.hnorm
  have off : ∀ a b : ℕ, a < b → b < h → u ^ 2 * (Fr.norm * Fr.Mn a b) ∈ LocRing p := by
    intro a b hab hbh
    have hMn : Fr.Mn a b = (1 / Fr.norm) * (1 / ((b : ℚ) - a)) * ∑ k ∈ Ioc a b, Fr.Delta k := by
      unfold Frame.Mn
      rw [if_neg hab.ne, max_eq_right hab.le, min_eq_left hab.le]
    have hs : u * ∑ k ∈ Ioc a b, Fr.Delta k ∈ LocRing p := by
      rw [Finset.mul_sum]
      refine (LocRing p).sum_mem fun k hk => ?_
      have hk' := Finset.mem_Ioc.mp hk
      have hk1 : 1 ≤ k := by omega
      rw [Delta_lin k hk1, Finset.mul_sum]
      refine (LocRing p).sum_mem fun i _ => ?_
      have hm : u / (lin Fr i k : ℚ) ∈ LocRing p :=
        CatalanFrames.P6.pw_mem' p (lin_pos i hk1) (by have := lin_le i (hden i) hk1; omega)
      have e : u * (((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ)) =
          (((Fr.w i * ((Fr.μ i).den : ℤ) : ℤ)) : ℚ) * (u / (lin Fr i k : ℚ)) := by
        push_cast; ring
      rw [e]
      exact (LocRing p).mul_mem (int_mem_locRing _) hm
    have hd : u / ((b - a : ℕ) : ℚ) ∈ LocRing p :=
      CatalanFrames.P6.pw_mem' p (by omega) (by omega)
    have hn0 : Fr.norm ≠ 0 := hnorm.ne'
    have e : u ^ 2 * (Fr.norm * Fr.Mn a b) = (u / ((b - a : ℕ) : ℚ)) * (u * ∑ k ∈ Ioc a b, Fr.Delta k) := by
      rw [hMn, Nat.cast_sub hab.le]
      field_simp
    rw [e]
    exact (LocRing p).mul_mem hd hs
  have diag : ∀ a : ℕ, a < h → u ^ 2 * (Fr.norm * Fr.Mn a a) ∈ LocRing p := by
    intro a hah
    have hMn : Fr.Mn a a = -(1 / Fr.norm) * ∑ k ∈ Icc 1 a, Fr.Dsq k := by
      unfold Frame.Mn; rw [if_pos rfl]
    have hs : u ^ 2 * ∑ k ∈ Icc 1 a, Fr.Dsq k ∈ LocRing p := by
      rw [Finset.mul_sum]
      refine (LocRing p).sum_mem fun k hk => ?_
      have hk' := Finset.mem_Icc.mp hk
      rw [Dsq_lin k hk'.1, Finset.mul_sum]
      refine (LocRing p).sum_mem fun i _ => ?_
      have hm : u / (lin Fr i k : ℚ) ∈ LocRing p :=
        CatalanFrames.P6.pw_mem' p (lin_pos i hk'.1) (by have := lin_le i (hden i) hk'.1; omega)
      have e : u ^ 2 * (((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (lin Fr i k : ℚ) ^ 2) =
          (((Fr.w i * ((Fr.μ i).den : ℤ) ^ 2 : ℤ)) : ℚ) * (u / (lin Fr i k : ℚ)) ^ 2 := by
        push_cast; ring
      rw [e]
      exact (LocRing p).mul_mem (int_mem_locRing _) ((LocRing p).pow_mem hm 2)
    have hn0 : Fr.norm ≠ 0 := hnorm.ne'
    have e : u ^ 2 * (Fr.norm * Fr.Mn a a) = -(u ^ 2 * ∑ k ∈ Icc 1 a, Fr.Dsq k) := by
      rw [hMn]; field_simp
    rw [e]
    exact (LocRing p).neg_mem hs
  rcases lt_trichotomy a b with hab | rfl | hba
  · exact off a b hab hb
  · exact diag a ha
  · rw [Mn_symm_gen]; exact off b a hba ha

/-- The weight for the bad primes `2, 3`. -/
def smallW (h : ℕ) : ℕ := 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h)

theorem smallW_pos (h : ℕ) : 0 < smallW h := by unfold smallW; positivity

theorem smallW_poly : ∃ A C : ℕ, ∀ h, smallW h ≤ A * (h + 1) ^ C := by
  refine ⟨9, 2, fun h => ?_⟩
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp [smallW]
  · have h2 := Nat.pow_log_le_self 2 (by omega : 3 * h ≠ 0)
    have h3 := Nat.pow_log_le_self 3 (by omega : 3 * h ≠ 0)
    unfold smallW
    calc 2 ^ Nat.log 2 (3 * h) * 3 ^ Nat.log 3 (3 * h) ≤ (3 * h) * (3 * h) := Nat.mul_le_mul h2 h3
      _ ≤ 9 * (h + 1) ^ 2 := by nlinarith

theorem smallW_ok (hden : ∀ i, (Fr.μ i).den ≤ 3) (hnorm : Fr.norm = 1) (p : ℕ) [Fact p.Prime]
    (hp : p ∈ ({2, 3} : Finset ℕ)) (h a b : ℕ) (ha : a < h) (hb : b < h) :
    ((smallW h : ℕ) : ℚ) ^ 2 * Fr.Mn a b ∈ LocRing p := by
  have hp' : p = 2 ∨ p = 3 := by simpa using hp
  have key := u2_Mn_mem p hden ha hb (Fr := Fr)
  rw [hnorm, one_mul] at key
  rcases hp' with rfl | rfl
  · have e : ((smallW h : ℕ) : ℚ) ^ 2 * Fr.Mn a b =
        ((3 : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 * (((2 : ℕ) : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 * Fr.Mn a b := by
      unfold smallW; push_cast; ring
    rw [e, mul_assoc]
    exact (LocRing 2).mul_mem ((LocRing 2).pow_mem ((LocRing 2).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 2) (3 : ℤ)) _) 2) key
  · have e : ((smallW h : ℕ) : ℚ) ^ 2 * Fr.Mn a b =
        ((2 : ℚ) ^ Nat.log 2 (3 * h)) ^ 2 * (((3 : ℕ) : ℚ) ^ Nat.log 3 (3 * h)) ^ 2 * Fr.Mn a b := by
      unfold smallW; push_cast; ring
    rw [e, mul_assoc]
    exact (LocRing 3).mul_mem ((LocRing 3).pow_mem ((LocRing 3).pow_mem
      (by exact_mod_cast int_mem_locRing (ℓ := 3) (2 : ℤ)) _) 2) key

end Small

/-! ### The content table of the plane frames -/

section CD

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

theorem rho_le (σ : Support) : σ.rho ≤ 2 := by cases σ <;> simp [Support.rho]
theorem rho_pos (σ : Support) : 0 < σ.rho := by cases σ <;> simp [Support.rho]

/-- `Φ(k) = k (3k - ρ) (2k - 1)`, the product of the three linear forms. -/
def planePhi (σ : Support) (k : ℕ) : ℕ := k * (3 * k - σ.rho) * (2 * k - 1)

theorem planePhi_pos {k : ℕ} (hk : 0 < k) : 0 < planePhi σ k := by
  have := rho_le σ
  unfold planePhi
  have h1 : 0 < 3 * k - σ.rho := by omega
  have h2 : 0 < 2 * k - 1 := by omega
  positivity

theorem plane_sum_forms {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℚ) :
    ∑ i : Fin (planeFrame σ a b c h0).d,
        ((![a, b, c] i : ℤ) : ℚ) * ((![σ.shift, 1 / 2, 1] i).den : ℚ) / f i.1 =
      3 * (a : ℚ) / f 0 + 2 * b / f 1 + c / f 2 := by
  change ∑ i : Fin 3, ((![a, b, c] i : ℤ) : ℚ) * ((![σ.shift, 1 / 2, 1] i).den : ℚ) / f i.1 = _
  rw [Fin.sum_univ_three]
  simp [shift_den, half_den, one_den]
  ring

/-- `Δ_k = 3a/(3k - ρ) + 2b/(2k - 1) + c/k`. -/
theorem plane_Delta {k : ℕ} (hk : 1 ≤ k) :
    (planeFrame σ a b c h0).Delta k =
      3 * (a : ℚ) / ((3 * k - σ.rho : ℕ) : ℚ) + 2 * b / ((2 * k - 1 : ℕ) : ℚ) + c / (k : ℚ) := by
  rw [Delta_lin k hk]
  have e : ∀ i ∈ (Finset.univ : Finset (Fin (planeFrame σ a b c h0).d)),
      ((((planeFrame σ a b c h0).w i : ℚ) * ((planeFrame σ a b c h0).μ i).den) /
        (lin (planeFrame σ a b c h0) i k : ℚ)) =
      ((![a, b, c] i : ℤ) : ℚ) * ((![σ.shift, 1 / 2, 1] i).den : ℚ) / ((pl σ i.1 k : ℕ) : ℚ) := by
    intro i _
    rw [lin_plane σ a b c h0 i hk]
    rfl
  rw [Finset.sum_congr rfl e, plane_sum_forms σ a b c h0 hk (fun j => ((pl σ j k : ℕ) : ℚ))]
  rfl

/-- `D_k = 9a/(3k - ρ)² + 4b/(2k - 1)² + c/k²`. -/
theorem plane_Dsq {k : ℕ} (hk : 1 ≤ k) :
    (planeFrame σ a b c h0).Dsq k =
      9 * (a : ℚ) / ((3 * k - σ.rho : ℕ) : ℚ) ^ 2 + 4 * b / ((2 * k - 1 : ℕ) : ℚ) ^ 2 +
        c / (k : ℚ) ^ 2 := by
  rw [Dsq_lin k hk]
  have e : ∀ i ∈ (Finset.univ : Finset (Fin (planeFrame σ a b c h0).d)),
      ((((planeFrame σ a b c h0).w i : ℚ) * ((planeFrame σ a b c h0).μ i).den ^ 2) /
        (lin (planeFrame σ a b c h0) i k : ℚ) ^ 2) =
      ((![a, b, c] i : ℤ) : ℚ) * ((![σ.shift, 1 / 2, 1] i).den : ℚ) ^ 2 /
        ((pl σ i.1 k : ℕ) : ℚ) ^ 2 := by
    intro i _
    rw [lin_plane σ a b c h0 i hk]
    rfl
  rw [Finset.sum_congr rfl e]
  change ∑ i : Fin 3, ((![a, b, c] i : ℤ) : ℚ) * ((![σ.shift, 1 / 2, 1] i).den : ℚ) ^ 2 /
      ((pl σ i.1 k : ℕ) : ℚ) ^ 2 = _
  rw [Fin.sum_univ_three]
  simp [shift_den, half_den, one_den, pl]
  ring

end CD

section CD2

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

theorem no_two_dvd_plane {p k : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hk : 0 < k) :
    ¬ (p ∣ k ∧ p ∣ 3 * k - σ.rho) ∧ ¬ (p ∣ 3 * k - σ.rho ∧ p ∣ 2 * k - 1) ∧
      ¬ (p ∣ k ∧ p ∣ 2 * k - 1) := by
  have hr := rho_le σ
  have hr0 := rho_pos σ
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hA, hB⟩
    have := Nat.dvd_sub (Dvd.dvd.mul_left hA 3) hB
    have e : 3 * k - (3 * k - σ.rho) = σ.rho := by omega
    rw [e] at this
    have hle := Nat.le_of_dvd hr0 this
    have hp2 := hp.two_le
    have : p = 2 := by omega
    exact h2 this
  · rintro ⟨hB, hC⟩
    cases σ
    · have := Nat.dvd_sub (Dvd.dvd.mul_left hC 3) (Dvd.dvd.mul_left hB 2)
      have e : 3 * (2 * k - 1) - 2 * (3 * k - Support.plus.rho) = 1 := by simp [Support.rho]; omega
      rw [e] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · have := Nat.dvd_sub (Dvd.dvd.mul_left hB 2) (Dvd.dvd.mul_left hC 3)
      have e : 2 * (3 * k - Support.minus.rho) - 3 * (2 * k - 1) = 1 := by simp [Support.rho]; omega
      rw [e] at this
      exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  · rintro ⟨hA, hC⟩
    have := Nat.dvd_sub (Dvd.dvd.mul_left hA 2) hC
    have e : 2 * k - (2 * k - 1) = 1 := by omega
    rw [e] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem pow_dvd_triple {p e x y z : ℕ} (hp : p.Prime) (he : 0 < e) (h : p ^ e ∣ x * y * z)
    (hxy : ¬ (p ∣ x ∧ p ∣ y)) (hyz : ¬ (p ∣ y ∧ p ∣ z)) (hxz : ¬ (p ∣ x ∧ p ∣ z)) :
    p ^ e ∣ x ∨ p ^ e ∣ y ∨ p ^ e ∣ z := by
  have hpe : p ∣ x * y * z := (dvd_pow_self p he.ne').trans h
  by_cases hx : p ∣ x
  · left
    have hy : ¬ p ∣ y := fun hy => hxy ⟨hx, hy⟩
    have hz : ¬ p ∣ z := fun hz => hxz ⟨hx, hz⟩
    have hc : Nat.Coprime (p ^ e) (y * z) :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2
        (fun hd => by rcases hp.dvd_mul.1 hd with h' | h' <;> contradiction))
    rw [mul_assoc] at h
    exact hc.dvd_of_dvd_mul_right h
  · by_cases hy : p ∣ y
    · right; left
      have hz : ¬ p ∣ z := fun hz => hyz ⟨hy, hz⟩
      have hc : Nat.Coprime (p ^ e) (x * z) :=
        Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2
          (fun hd => by rcases hp.dvd_mul.1 hd with h' | h' <;> contradiction))
      have : x * y * z = y * (x * z) := by ring
      rw [this] at h
      exact hc.dvd_of_dvd_mul_right h
    · right; right
      by_cases hz : p ∣ z
      · have hc : Nat.Coprime (p ^ e) (x * y) :=
          Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2
            (fun hd => by rcases hp.dvd_mul.1 hd with h' | h' <;> contradiction))
        have : x * y * z = z * (x * y) := by ring
        rw [this] at h
        exact hc.dvd_of_dvd_mul_right h
      · exfalso
        rcases hp.dvd_mul.1 hpe with h' | h'
        · rcases hp.dvd_mul.1 h' with h'' | h'' <;> contradiction
        · contradiction

open Classical in
/-- The first `k ≥ 1` at which `q` divides `Φ(k)` (`0` if none). -/
noncomputable def planeKq (σ : Support) (q : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ q ∣ planePhi σ k then Nat.find h else 0

theorem planeKq_le {q k : ℕ} (hq : IsPrimePow q) (h2 : ¬ 2 ∣ q) (h3 : ¬ 3 ∣ q) (hk : 0 < k)
    (hd : q ∣ planePhi σ k) : planeKq σ q ≤ k ∧ q ≤ 3 * k := by
  classical
  have hex : ∃ k, 0 < k ∧ q ∣ planePhi σ k := ⟨k, hk, hd⟩
  refine ⟨?_, ?_⟩
  · unfold planeKq
    rw [dif_pos hex]
    exact Nat.find_min' hex ⟨hk, hd⟩
  · obtain ⟨p, e, hp0, he, hqe⟩ := hq
    have hp := hp0.nat_prime
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact h2 (hqe ▸ dvd_pow_self 2 he.ne')
    obtain ⟨n1, n2, n3⟩ := no_two_dvd_plane σ hp hp2 hk
    have hr := rho_le σ
    unfold planePhi at hd
    rw [← hqe] at hd
    rcases pow_dvd_triple hp he hd n1 n2 n3 with h | h | h
    · have := Nat.le_of_dvd hk h; omega
    · have := Nat.le_of_dvd (by omega) h; omega
    · have := Nat.le_of_dvd (by omega) h; omega

/-- **The content table of the plane frames**: `Φ(k) = k (3k - ρ) (2k - 1)`, bad primes `{2, 3}`, norm `1`. -/
noncomputable def planeCD : ContentData (planeFrame σ a b c h0) where
  L := 3
  hL := by norm_num
  Phi := planePhi σ
  Phi_pos := fun k hk => planePhi_pos σ hk
  bad := {2, 3}
  bad_prime := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Nat.prime_two
    · exact Nat.prime_three
  normN := 1
  norm_eq := by simp [planeFrame]
  norm_dvd := by
    intro p hp hd
    have := Nat.le_of_dvd one_pos hd
    have := hp.two_le
    omega
  delta_int := by
    intro k hk
    have hk1 : 1 ≤ k := hk
    have hr := rho_le σ
    refine ⟨3 * a * k * (2 * k - 1) + 2 * b * k * (3 * k - σ.rho) +
      c * (3 * k - σ.rho) * (2 * k - 1), ?_⟩
    rw [plane_Delta σ a b c h0 hk1]
    have hy : ((3 * k - σ.rho : ℕ) : ℚ) = 3 * k - σ.rho := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hz : ((2 * k - 1 : ℕ) : ℚ) = 2 * k - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hy0 : (3 * (k : ℚ) - σ.rho) ≠ 0 := by
      rw [← hy]; exact_mod_cast (by omega : 3 * k - σ.rho ≠ 0)
    have hz0 : (2 * (k : ℚ) - 1) ≠ 0 := by
      rw [← hz]; exact_mod_cast (by omega : 2 * k - 1 ≠ 0)
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    unfold planePhi
    push_cast [hy, hz]
    generalize 3 * (k : ℚ) - σ.rho = X at hy0 ⊢
    generalize 2 * (k : ℚ) - 1 = Y at hz0 ⊢
    field_simp
  dsq_int := by
    intro k hk
    have hk1 : 1 ≤ k := hk
    have hr := rho_le σ
    refine ⟨9 * a * (k * (2 * k - 1)) ^ 2 + 4 * b * (k * (3 * k - σ.rho)) ^ 2 +
      c * ((3 * k - σ.rho) * (2 * k - 1)) ^ 2, ?_⟩
    rw [plane_Dsq σ a b c h0 hk1]
    have hy : ((3 * k - σ.rho : ℕ) : ℚ) = 3 * k - σ.rho := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hz : ((2 * k - 1 : ℕ) : ℚ) = 2 * k - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hy0 : (3 * (k : ℚ) - σ.rho) ≠ 0 := by
      rw [← hy]; exact_mod_cast (by omega : 3 * k - σ.rho ≠ 0)
    have hz0 : (2 * (k : ℚ) - 1) ≠ 0 := by
      rw [← hz]; exact_mod_cast (by omega : 2 * k - 1 ≠ 0)
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    unfold planePhi
    push_cast [hy, hz]
    generalize 3 * (k : ℚ) - σ.rho = X at hy0 ⊢
    generalize 2 * (k : ℚ) - 1 = Y at hz0 ⊢
    field_simp
  kq := planeKq σ
  kq_le := by
    intro q k hq hbad hk hd
    exact planeKq_le σ hq (hbad 2 (by simp)) (hbad 3 (by simp)) hk hd
  small := smallW
  small_pos := smallW_pos
  small_ok := fun p _ hp h a' b' ha hb => smallW_ok (plane_den_le σ a b c h0) rfl p hp h a' b' ha hb
  small_poly := smallW_poly

end CD2

/-! ### The instance, its numerology and the bundle (N7) -/

section InstFinal

open CatalanFrames.HybCommon

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

/-- **The weight-free hybrid instance of the plane frames** (singular-count levels, `Ebd N = 3 N`). -/
noncomputable def planeInst : HybInst (planeFrame σ a b c h0) :=
  planeInstOf _ (planeCD σ a b c h0) rfl (plane_den_le σ a b c h0)

instance planeInst_diagOK (r m : ℕ) : (planeInst σ a b c h0).DiagOK r m := ⟨fun _ _ => trivial⟩

theorem planeInst_lev (q A : ℕ) : (planeInst σ a b c h0).lev q A = levF (planeFrame σ a b c h0) q A := rfl

/-- **The numerology**: `L = 3`, `cOf ≤ 2`, `Ebd N + N = 4 N ≤ 5 N³`, bad primes `{2, 3}`. -/
theorem planeInst_badInfo : BadInfo (planeInst σ a b c h0) 3 2 where
  L_eq := rfl
  Lc_le := by norm_num
  cm_le := by norm_num
  Ebd_le := fun N => by
    show 3 * N + N ≤ 5 * N ^ 3
    rcases N with _ | N
    · simp
    · nlinarith [Nat.zero_le N, Nat.zero_le (N * N), Nat.zero_le (N * N * N)]
  two_mem := by show 2 ∈ ({2, 3} : Finset ℕ); simp
  bad_le := fun b' hb => by
    have : b' ∈ ({2, 3} : Finset ℕ) := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    omega
  cOf_le := fun p => by
    show (1 : ℕ).factorization p ≤ 2
    simp

/-- **The pole bundle of a plane frame** (N7): the frame, `ρ`, the (constant) instances, `DiagOK`, `BadInfo 3 2`,
the pole data (P102) with the singular set `p ∣ t`, `p ∣ 3t - ρ`, `p ∣ 2t - 1`. -/
noncomputable def planeBundle : KBundle where
  Fr := planeFrame σ a b c h0
  ρ := σ.rho
  inst := fun _ _ => planeInst σ a b c h0
  diagOK := fun r m => planeInst_diagOK σ a b c h0 r m
  badInfo := fun _ _ => planeInst_badInfo σ a b c h0
  pole := fun _ _ _ _ hN => planePoleData σ a b c h0 hN
  singular_iff := fun p N _ h5 hN t => planePoleData_singular σ a b c h0 hN t

theorem planeBundle_shifts : (planeBundle σ a b c h0).shifts = [⟨3, σ.rho, 1⟩, ⟨2, 1, 1⟩] := rfl

end InstFinal

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.planeInstOf
#print axioms CatalanCore.Uniform.Bank.Plane1.planeCD
#print axioms CatalanCore.Uniform.Bank.Plane1.planeInst_badInfo
#print axioms CatalanCore.Uniform.Bank.Plane1.planeBundle
#print axioms CatalanCore.Uniform.Bank.Plane1.smallW_ok
