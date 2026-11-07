module

public import CatalanCore.Arith.Hybrid.LemmaE.GleE4
public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic

@[expose] public section

/-!
# Lemma E, class 1 (`j = 3`, `4k = 3p + o`): the scalar Schur complement of the unpaired block

Generic in the offset `o` (this replaces the λ-only `HybLemmaE`/`HybLemmaE2`).  The table `TE` on the
unpaired block `U = [r-p, k)` (weight `0`) is the regular sum `(16 (b-a))⁻¹ ∑ (1/t - 1/(t-k))`; the
harmonic-sum identities of `Harmonic.lean` turn it into the Cauchy form `hUU` required by `gleAt_E_wit`
(DQ Lemma 3.1).  No frame enters: the frame appears only through `hL : LamData Fr o`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

open LemmaE

section

variable {p : ℕ} [Fact p.Prime]

/-- `φ(n) = H_n + H_{k-1} - H_{k-1-n}` in `ZMod p`. -/
def phiK (p k n : ℕ) [Fact p.Prime] : ZMod p :=
  Gs p (fun x => x⁻¹) n + Gs p (fun x => x⁻¹) (k - 1) - Gs p (fun x => x⁻¹) (k - 1 - n)

lemma Gs_succ (f : ZMod p → ZMod p) (n : ℕ) :
    Gs p f (n + 1) = Gs p f n + f ((n + 1 : ℕ) : ZMod p) := by
  unfold Gs; rw [Finset.sum_range_succ]

lemma sumReg_off {k a b : ℕ} (hab : a ≤ b) (hb : b ≤ k - 1) :
    ∑ t ∈ Ioc a b, ((((t : ℕ) : ZMod p))⁻¹ - (((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) =
      phiK p k b - phiK p k a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih (by omega)]
    unfold phiK
    have e1 : Gs p (fun x => x⁻¹) (b + 1) = Gs p (fun x => x⁻¹) b + ((b + 1 : ℕ) : ZMod p)⁻¹ :=
      Gs_succ _ b
    have e2 : Gs p (fun x => x⁻¹) (k - 1 - b) =
        Gs p (fun x => x⁻¹) (k - 1 - (b + 1)) + ((k - 1 - b : ℕ) : ZMod p)⁻¹ := by
      have : k - 1 - b = (k - 1 - (b + 1)) + 1 := by omega
      conv_lhs => rw [this]
      rw [Gs_succ]
      rw [show k - 1 - (b + 1) + 1 = k - 1 - b by omega]
    have e3 : (((k - 1 - b : ℕ)) : ZMod p) = (k : ZMod p) - ((b + 1 : ℕ) : ZMod p) := by
      rw [show k - 1 - b = k - (b + 1) by omega, Nat.cast_sub (by omega)]
    have e4 : (((b + 1 : ℕ) : ZMod p) - (k : ZMod p))⁻¹ = -((k : ZMod p) - ((b + 1 : ℕ) : ZMod p))⁻¹ := by
      rw [← inv_neg]; congr 1; ring
    rw [e1, e2, e3, e4]
    ring

lemma sumReg_diag {k a : ℕ} (ha : a ≤ k - 1) :
    ∑ t ∈ Icc 1 a, (((((t : ℕ) : ZMod p))⁻¹) ^ 2 - ((((t : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2) =
      Gs p (fun x => (x⁻¹) ^ 2) a - Gs p (fun x => (x⁻¹) ^ 2) (k - 1) +
        Gs p (fun x => (x⁻¹) ^ 2) (k - 1 - a) := by
  induction a with
  | zero => simp [Gs]
  | succ a ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have e1 : Gs p (fun x => (x⁻¹) ^ 2) (a + 1) =
        Gs p (fun x => (x⁻¹) ^ 2) a + ((((a + 1 : ℕ) : ZMod p))⁻¹) ^ 2 := Gs_succ _ a
    have e2 : Gs p (fun x => (x⁻¹) ^ 2) (k - 1 - a) =
        Gs p (fun x => (x⁻¹) ^ 2) (k - 1 - (a + 1)) + ((((k - 1 - a : ℕ) : ZMod p))⁻¹) ^ 2 := by
      have : k - 1 - a = (k - 1 - (a + 1)) + 1 := by omega
      conv_lhs => rw [this]
      rw [Gs_succ]
      rw [show k - 1 - (a + 1) + 1 = k - 1 - a by omega]
    have e3 : (((k - 1 - a : ℕ)) : ZMod p) = (k : ZMod p) - ((a + 1 : ℕ) : ZMod p) := by
      rw [show k - 1 - a = k - (a + 1) by omega, Nat.cast_sub (by omega)]
    have e4 : ((((a + 1 : ℕ) : ZMod p) - (k : ZMod p))⁻¹) ^ 2 =
        (((k : ZMod p) - ((a + 1 : ℕ) : ZMod p))⁻¹) ^ 2 := by
      rw [← neg_sub, inv_neg]; ring
    rw [e1, e2, e3, e4]
    ring

end

section

variable {o p r m k : ℕ} [Fact p.Prime]

/-- **The scalar Schur complement hypothesis for the class-1 residue table** (DQ Lemma 3.1),
for any offset `o`. -/
theorem hUU_gen (S : ESetup o p r m 3 k) :
    ∀ a b : ℕ, r - p ≤ a → a < k → r - p ≤ b → b < k →
      TE p 3 r k a b = (16 : ZMod p)⁻¹ * ((if a = b then Gs p (fun x => (x⁻¹) ^ 2) (k - 1) else 0) +
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹) := by
  intro a b ha1 ha2 hb1 hb2
  have hr := S.hpr
  have hkp := S.hkp
  have hp5 := S.p5
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero (four_ne_zmod p hp5) (four_ne_zmod p hp5)
  have hw : ∀ x, r - p ≤ x → x < k → wE p r k x + wE p r k x = 0 := fun x h1 h2 => by
    rw [wE_U h1 h2 (by omega)]
  have hw2 : ∀ x y, r - p ≤ x → x < k → r - p ≤ y → y < k → wE p r k x + wE p r k y = 0 :=
    fun x y h1 h2 h3 h4 => by rw [wE_U h1 h2 (by omega), wE_U h3 h4 (by omega)]
  have key : ∀ x y, x < y → r - p ≤ x → y < k →
      TE p 3 r k x y = (16 * ((y : ZMod p) - x))⁻¹ * (phiK p k y - phiK p k x) := by
    intro x y hxy hx hy
    have e0 : wE p r k x + wE p r k y = 0 := hw2 x y hx (by omega) (by omega) hy
    unfold TE
    rw [if_pos hxy, e0]
    unfold TEo
    rw [if_pos rfl, sumReg_off hxy.le (by omega)]
  have hwu : ∀ x y : ℕ, x < y → y < k → ((y : ZMod p) - x) ≠ 0 :=
    fun x y h1 h2 => sub_ne_zero_of_lt h1 (by omega)
  have hterm : ∀ x y : ℕ, x < y → y < k →
      (phiK p k y - phiK p k x) = ((y : ZMod p) - x) *
        ∑ c ∈ Ico k p, ((c : ZMod p) - x)⁻¹ * ((c : ZMod p) - y)⁻¹ := by
    intro x y hxy hy
    have h2 := schur_offdiag p (by omega) (K := k) (u := x) (w := y) (by omega) (by omega)
      (by omega)
    have ht : ∀ c ∈ Ico k p, ((((c : ℕ) : ZMod p) - y)⁻¹ - (((c : ℕ) : ZMod p) - x)⁻¹) =
        ((y : ZMod p) - x) * ((((c : ℕ) : ZMod p) - x)⁻¹ * (((c : ℕ) : ZMod p) - y)⁻¹) := by
      intro c hc
      have hc' := Finset.mem_Ico.mp hc
      have a1 : ((c : ZMod p) - x) ≠ 0 := sub_ne_zero_of_lt (by omega) (by omega)
      have a2 : ((c : ZMod p) - y) ≠ 0 := sub_ne_zero_of_lt (by omega) (by omega)
      field_simp
      ring
    rw [Finset.sum_congr rfl ht, ← Finset.mul_sum] at h2
    unfold phiK
    linear_combination -h2
  rcases lt_trichotomy a b with h | h | h
  · have hne := hwu a b h hb2
    rw [key a b h ha1 hb2, hterm a b h hb2, if_neg (by omega), zero_add]
    field_simp
  · subst h
    have e0 := hw a ha1 ha2
    unfold TE
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _), e0]
    unfold TEd
    rw [if_pos rfl, if_pos rfl, sumReg_diag (by omega)]
    have h2 := schur_diag p hp5 (K := k) (u := a) (by omega) ha2
    have h3 : ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - a)⁻¹ =
        ∑ c ∈ Ico k p, ((((c : ℕ) : ZMod p) - a)⁻¹) ^ 2 :=
      Finset.sum_congr rfl fun c _ => by rw [pow_two]
    rw [h3]
    linear_combination (-(1 / 16 : ZMod p)) * h2
  · have hne := hwu b a h ha2
    rw [TE_symm', key b a h hb1 ha2, hterm b a h ha2, if_neg (by omega), zero_add]
    have hs : ∑ c ∈ Ico k p, ((c : ZMod p) - b)⁻¹ * ((c : ZMod p) - a)⁻¹ =
        ∑ c ∈ Ico k p, ((c : ZMod p) - a)⁻¹ * ((c : ZMod p) - b)⁻¹ :=
      Finset.sum_congr rfl fun c _ => by rw [mul_comm]
    rw [hs]
    field_simp

/-- **Lemma E at a class-1 prime** (`j = 3`, `4k = 3p + o`), generic in the frame data. -/
theorem gleAt_E1_wit {Fr : Frame} (hL : LamData Fr o) (S : ESetup o p r m 3 k) :
    HasRankWit Fr p r m (fun a => wE p r k (Frame.hybRow r m a))
      (fun b => wE p r k (Frame.hybCol r m b)) m := by
  have hp5 := S.p5
  have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := S.hk; have := S.ho0; have := S.ho3
    omega
  have h3' : ((3 : ℕ) : ZMod p) * ((3 : ℕ) : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h3
  have he : -(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1 ≠ 0 := by
    intro h
    have h4 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = 0 := by rw [h]; ring
    have h5 : (-(4 * ((3 : ℕ) : ZMod p)⁻¹) + 1) * ((3 : ℕ) : ZMod p) = -1 := by
      linear_combination (-4) * h3'
    rw [h5] at h4
    exact one_ne_zero (neg_eq_zero.1 h4)
  exact gleAt_E_wit hL S (Gs p (fun x => (x⁻¹) ^ 2) (k - 1)) h3 he (hUU_gen S)

theorem wE_sum_gen (S : ESetup o p r m 3 k) :
    ∑ a : Fin r ⊕ Fin m, wE p r k (Frame.hybRow r m a) +
      ∑ b : Fin r ⊕ Fin m, wE p r k (Frame.hybCol r m b) = 2 * ((r - p) + (r - k)) + 4 * m :=
  wE_sum S.hrk (by have := S.hkp; have := S.hpr; omega)

end

end CatalanCore.Arith.Hybrid
