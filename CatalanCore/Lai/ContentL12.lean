module

public import CatalanCore.Lai.ContentLaw
public import CatalanCore.Content.ContentLaw
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# `CatalanCore.Lai.ContentL12`: Lemma U, the L1 basis, Lai's exact class bound

Lemma U (content note `N9-LAI-CONTENT-EXACT`): the unit-part ratio

Put `w_s = ĉ_s ∏_{r≠s} (s - r)^{2 μ_r}` (the exponents are even, so `(s-r)` and `(r-s)` agree) and
`Q(s) = ∏_{β ∈ N} (s - β)`.  If `s` and `s+1` lie in the same class then `w_{s+1} Q(s) = w_s Q(s+1)`.
The proof is the paper's: a cyclic shift of the product, Lemma S(ii), and the three class boundaries.
-/

open Finset CatalanCore.Content

namespace CatalanCore.Lai

section ProdShift

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∏_{r ≠ s} (s - r)^{e r}` over `ZMod p`. -/
def PQ (e : ZMod p → ℤ) (s : ZMod p) : ZMod p :=
  ∏ r : ZMod p, if r = s then 1 else (s - r) ^ e r

lemma PQ_shift (e : ZMod p → ℤ) (s : ZMod p) : PQ e (s + 1) = PQ (fun r => e (r + 1)) s := by
  unfold PQ
  symm
  refine Fintype.prod_equiv (Equiv.addRight (1 : ZMod p)) _ _ (fun x => ?_)
  simp only [Equiv.coe_addRight, add_left_inj, add_sub_add_right_eq_sub]

lemma PQ_add (e1 e2 : ZMod p → ℤ) (s : ZMod p) :
    PQ (fun r => e1 r + e2 r) s = PQ e1 s * PQ e2 s := by
  unfold PQ
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  by_cases hr : r = s
  · simp [hr]
  · have : s - r ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
    simp only [hr, if_false]
    exact zpow_add₀ this _ _

lemma PQ_const_shift (c : ℤ) (s : ZMod p) : PQ (fun _ => c) (s + 1) = PQ (fun _ => c) s :=
  PQ_shift (fun _ => c) s

lemma PQ_neg (e : ZMod p → ℤ) (s : ZMod p) :
    PQ (fun r => - e r) s * PQ e s = 1 := by
  rw [← PQ_add]
  unfold PQ
  refine Finset.prod_eq_one (fun r _ => ?_)
  by_cases hr : r = s
  · simp [hr]
  · simp [hr]

lemma PQ_ind (x s : ZMod p) (c : ℤ) :
    PQ (fun r => if r = x then c else 0) s = if x = s then 1 else (s - x) ^ c := by
  unfold PQ
  rw [Finset.prod_eq_single x]
  · by_cases hx : x = s
    · simp [hx]
    · simp [hx]
  · intro r _ hr
    simp [hr]
  · intro h; exact absurd (Finset.mem_univ x) h

end ProdShift

section Boundary

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- the class function on `ZMod p`. -/
def sigZ (n p : ℕ) (r : ZMod p) : ℤ := (sig n p r.val : ℤ)

lemma val_succ_cases (r : ZMod p) :
    (r + 1).val = if r.val + 1 = p then 0 else r.val + 1 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  rw [ZMod.val_add, ZMod.val_one]
  have hlt := ZMod.val_lt r
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma sig_jump (n p : ℕ) (hr6 : r6 n p < p) (hr2 : r2 n p < p) (v : ℕ) (hv : v < p) :
    (sig n p (if v + 1 = p then 0 else v + 1) : ℤ) - (sig n p v : ℤ) =
      (if v = r6 n p then 2 else 0) + (if v = p - r2 n p - 1 then 3 else 0) -
        (if v = p - 1 then 5 else 0) := by
  unfold sig
  split_ifs <;> omega

lemma sigZ_jump (n : ℕ) (hr6 : r6 n p < p) (hr2 : r2 n p < p) (r : ZMod p) :
    sigZ n p (r + 1) - sigZ n p r =
      (if r = ((r6 n p : ℕ) : ZMod p) then 2 else 0) +
      (if r = ((p - r2 n p - 1 : ℕ) : ZMod p) then 3 else 0) -
      (if r = ((p - 1 : ℕ) : ZMod p) then 5 else 0) := by
  have hv := ZMod.val_lt r
  have hjump := sig_jump n p hr6 hr2 r.val hv
  have key : ∀ x : ℕ, x < p → (r = (x : ZMod p) ↔ r.val = x) := by
    intro x hx
    constructor
    · intro h; rw [h, ZMod.val_natCast_of_lt hx]
    · intro h; rw [← h, ZMod.natCast_zmod_val]
  unfold sigZ
  rw [val_succ_cases, hjump]
  simp only [key (r6 n p) hr6, key (p - r2 n p - 1) (by omega), key (p - 1) (by have := hp.out.pos; omega)]

end Boundary

section ChatSucc

variable {p : ℕ} [hp : Fact p.Prime]

lemma chat_succ_aux (r6 r2 s a' B : ℕ) (hs : s + 1 < p) (hr6 : r6 < p) (hr2 : r2 < p)
    (ha : a' + 1 < p) (hB : B + 1 < p) :
    (fz p r6 / (fz p (s + 1) * fz p a')) ^ 2 * (fz p (B + 1) / (fz p r2 * fz p (s + 1))) ^ 3 *
        ((s : ZMod p) + 1) ^ 5 =
      (fz p r6 / (fz p s * fz p (a' + 1))) ^ 2 * (fz p B / (fz p r2 * fz p s)) ^ 3 *
        ((a' : ZMod p) + 1) ^ 2 * ((B : ZMod p) + 1) ^ 3 := by
  have h1 : fz p s ≠ 0 := fz_ne_zero (by omega)
  have h2 : fz p a' ≠ 0 := fz_ne_zero (by omega)
  have h3 : fz p B ≠ 0 := fz_ne_zero (by omega)
  have h4 : fz p r2 ≠ 0 := fz_ne_zero hr2
  have h5 : fz p r6 ≠ 0 := fz_ne_zero hr6
  have e1 : fz p (s + 1) = ((s : ZMod p) + 1) * fz p s := by
    unfold fz; rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
  have e2 : fz p (a' + 1) = ((a' : ZMod p) + 1) * fz p a' := by
    unfold fz; rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
  have e3 : fz p (B + 1) = ((B : ZMod p) + 1) * fz p B := by
    unfold fz; rw [Nat.factorial_succ, Nat.cast_mul]; push_cast; ring
  have n1 : ((s : ZMod p) + 1) ≠ 0 := by
    have : fz p (s + 1) ≠ 0 := fz_ne_zero hs
    rw [e1] at this; exact left_ne_zero_of_mul this
  have n2 : ((a' : ZMod p) + 1) ≠ 0 := by
    have : fz p (a' + 1) ≠ 0 := fz_ne_zero ha
    rw [e2] at this; exact left_ne_zero_of_mul this
  rw [e1, e2, e3]
  field_simp

lemma chat_succ (r6 r2 b ε s a' B : ℕ) (hs : s + 1 < p) (hr6 : r6 < p) (hr2 : r2 < p)
    (ha : r6 + b * p = s + 1 + a') (ha' : a' + 1 < p)
    (hB : r2 + s = ε * p + B) (hB' : B + 1 < p) :
    chat p r6 r2 b ε (s + 1) * ((s : ZMod p) + 1) ^ 5 =
      chat p r6 r2 b ε s * ((s : ZMod p) - r6) ^ 2 * ((s : ZMod p) + r2 + 1) ^ 3 := by
  have c1 : r6 + b * p - (s + 1) = a' := by omega
  have c2 : r6 + b * p - s = a' + 1 := by omega
  have c3 : r2 + (s + 1) - ε * p = B + 1 := by omega
  have c4 : r2 + s - ε * p = B := by omega
  unfold chat
  rw [c1, c2, c3, c4]
  have hA : ((a' : ZMod p) + 1) = (r6 : ZMod p) - s := by
    have := congrArg (fun z : ℕ => (z : ZMod p)) ha
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, add_zero, Nat.cast_one] at this
    linear_combination -this
  have hBc : ((B : ZMod p) + 1) = (s : ZMod p) + r2 + 1 := by
    have := congrArg (fun z : ℕ => (z : ZMod p)) hB
    simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add] at this
    linear_combination -this
  have := chat_succ_aux (p := p) r6 r2 s a' B hs hr6 hr2 ha' hB'
  rw [this, hA, hBc]
  ring

end ChatSucc

section LemmaUMain

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

/-- the exponents `2 μ_r` on `ZMod p`. -/
noncomputable def eZ (n p : ℕ) (r : ZMod p) : ℤ := 2 * (mu n p r.val : ℤ)

/-- `Q(s) = ∏_{β ∈ N} (s - β)`. -/
noncomputable def Qm (n p : ℕ) [Fact p.Prime] (s : ZMod p) : ZMod p :=
  ∏ r : ZMod p, if (lam n p - sigZ n p r) % 2 ≠ 0 then s - r else 1

/-- the odd class indicator (residues of `N`). -/
noncomputable def nN (n p : ℕ) (r : ZMod p) : ℤ := if (lam n p - sigZ n p r) % 2 ≠ 0 then 1 else 0

/-- `w_s = ĉ_s ∏_{r ≠ s} (s - r)^{2 μ_r}`. -/
noncomputable def wU (n p : ℕ) [Fact p.Prime] (s : ℕ) : ZMod p :=
  chat p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * PQ (eZ n p) (s : ZMod p)

lemma eZ_decomp (h : Rng n p) (r : ZMod p) :
    eZ n p r = (lam n p + 4 + nN n p r) + (- sigZ n p r) := by
  have hS := (lemmaS h).2.2.1 r.val (ZMod.val_lt r)
  unfold eZ nN sigZ at *
  by_cases hc : (lam n p - (sig n p r.val : ℤ)) % 2 = 0
  · simp only [hc, if_true] at hS
    simp [hc]; omega
  · simp only [hc, if_false] at hS
    simp [hc]; omega

lemma PQ_eZ (h : Rng n p) (s : ZMod p) :
    PQ (eZ n p) s = PQ (fun _ => lam n p + 4) s * PQ (nN n p) s * PQ (fun r => - sigZ n p r) s := by
  have : eZ n p = fun r => ((lam n p + 4) + nN n p r) + (- sigZ n p r) := by
    funext r; rw [eZ_decomp h r]
  rw [this, PQ_add, PQ_add (fun _ => lam n p + 4) (nN n p)]

lemma PQ_nN (s : ZMod p) (hs : ¬ ((lam n p - sigZ n p s) % 2 ≠ 0)) :
    PQ (nN n p) s = Qm n p s := by
  unfold PQ Qm
  refine Finset.prod_congr rfl (fun r _ => ?_)
  by_cases hr : r = s
  · subst hr; simp [hs]
  · by_cases hN : (lam n p - sigZ n p r) % 2 ≠ 0
    · simp [hr, hN, nN]
    · simp [hr, hN, nN]

lemma Qm_zero_of_N (s : ZMod p) (hs : (lam n p - sigZ n p s) % 2 ≠ 0) : Qm n p s = 0 := by
  unfold Qm
  exact Finset.prod_eq_zero (i := s) (Finset.mem_univ s) (by simp [hs])

lemma neg_sigZ_shift (hr6 : r6 n p < p) (hr2 : r2 n p < p) (s : ZMod p)
    (h1 : s ≠ ((r6 n p : ℕ) : ZMod p)) (h2 : s ≠ ((p - r2 n p - 1 : ℕ) : ZMod p))
    (h3 : s ≠ ((p - 1 : ℕ) : ZMod p)) :
    PQ (fun r => - sigZ n p r) (s + 1) * (s - ((r6 n p : ℕ) : ZMod p)) ^ 2 *
        (s - ((p - r2 n p - 1 : ℕ) : ZMod p)) ^ 3 =
      PQ (fun r => - sigZ n p r) s * (s - ((p - 1 : ℕ) : ZMod p)) ^ 5 := by
  rw [PQ_shift]
  have hfun : (fun r : ZMod p => - sigZ n p (r + 1)) =
      fun r => (-sigZ n p r) + ((if r = ((r6 n p : ℕ) : ZMod p) then (-2 : ℤ) else 0) +
        ((if r = ((p - r2 n p - 1 : ℕ) : ZMod p) then (-3 : ℤ) else 0) +
         (if r = ((p - 1 : ℕ) : ZMod p) then (5 : ℤ) else 0))) := by
    funext r
    have := sigZ_jump (p := p) n hr6 hr2 r
    split_ifs at this ⊢ <;> omega
  rw [hfun, PQ_add, PQ_add, PQ_add, PQ_ind, PQ_ind, PQ_ind]
  simp only [Ne.symm h1, Ne.symm h2, Ne.symm h3, if_false]
  have s1 : s - ((r6 n p : ℕ) : ZMod p) ≠ 0 := sub_ne_zero.2 h1
  have s2 : s - ((p - r2 n p - 1 : ℕ) : ZMod p) ≠ 0 := sub_ne_zero.2 h2
  rw [zpow_neg, zpow_neg]
  simp only [zpow_ofNat]
  field_simp

end LemmaUMain

section LemmaUThm

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

lemma flag_cases (n p s : ℕ) (hr2 : r2 n p < p) (hs : s + 1 < p)
    (hsig : sig n p s = sig n p (s + 1)) :
    bflag n p (s + 1) = bflag n p s ∧ eflag n p (s + 1) = eflag n p s ∧
    ((bflag n p s = 0 ∧ s + 1 ≤ r6 n p) ∨ (bflag n p s = 1 ∧ r6 n p < s)) ∧
    ((eflag n p s = 0 ∧ s + 1 + r2 n p < p) ∨ (eflag n p s = 1 ∧ p ≤ r2 n p + s)) := by
  have h1 := sig_eq_flags n p s
  have h2 := sig_eq_flags n p (s + 1)
  unfold bflag eflag at *
  unfold sig at hsig
  refine ⟨?_, ?_, ?_, ?_⟩ <;> split_ifs at * <;> omega

/-- **Lemma U.**  If `s` and `s+1` lie in one class, `w_{s+1} Q(s) = w_s Q(s+1)`. -/
theorem lemmaU (h : Rng n p) (s : ℕ) (hs : s + 1 < p) (hsig : sig n p s = sig n p (s + 1)) :
    wU n p (s + 1) * Qm n p (s : ZMod p) = wU n p s * Qm n p ((s : ZMod p) + 1) := by
  have hp1 := hp.out.pos
  have hr6 : r6 n p < p := r6_lt n p hp1
  have hr2 : r2 n p < p := r2_lt n p hp1
  have hc : ((s + 1 : ℕ) : ZMod p) = (s : ZMod p) + 1 := by push_cast; ring
  have e1 : sigZ n p (s : ZMod p) = (sig n p s : ℤ) := by
    unfold sigZ; rw [ZMod.val_natCast_of_lt (by omega)]
  have e2 : sigZ n p ((s : ZMod p) + 1) = (sig n p (s + 1) : ℤ) := by
    unfold sigZ; rw [← hc, ZMod.val_natCast_of_lt hs]
  by_cases hN : (lam n p - sigZ n p (s : ZMod p)) % 2 ≠ 0
  · have hN' : (lam n p - sigZ n p ((s : ZMod p) + 1)) % 2 ≠ 0 := by
      rw [e2, ← hsig, ← e1]; exact hN
    rw [Qm_zero_of_N _ hN, Qm_zero_of_N _ hN']; simp
  · have hN' : ¬ ((lam n p - sigZ n p ((s : ZMod p) + 1)) % 2 ≠ 0) := by
      rw [e2, ← hsig, ← e1]; exact hN
    obtain ⟨hb, he, hbc, hec⟩ := flag_cases n p s hr2 hs hsig
    -- the three boundary points differ from `s`
    have key : ∀ x : ℕ, x < p → s ≠ x → (s : ZMod p) ≠ (x : ZMod p) := by
      intro x hx hne hcast
      apply hne
      have := congrArg ZMod.val hcast
      rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt hx] at this
    have hs1 : s ≠ r6 n p := by
      intro hh; unfold sig at hsig; split_ifs at hsig <;> omega
    have hs2 : s ≠ p - r2 n p - 1 := by
      intro hh; unfold sig at hsig; split_ifs at hsig <;> omega
    have hs3 : s ≠ p - 1 := by omega
    have n1 := key _ hr6 hs1
    have n2 := key (p - r2 n p - 1) (by omega) hs2
    have n3 := key (p - 1) (by omega) hs3
    -- the shift identity for `-σ`
    have hsh := neg_sigZ_shift (p := p) (n := n) hr6 hr2 (s : ZMod p) n1 n2 n3
    have cp1 : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub hp1]; simp
    have cr : ((p - r2 n p - 1 : ℕ) : ZMod p) = -(r2 n p : ZMod p) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [cp1, cr] at hsh
    -- chat shift
    obtain ⟨a', ha⟩ : ∃ a', r6 n p + bflag n p s * p = s + 1 + a' := by
      rcases hbc with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact ⟨r6 n p - (s + 1), by rw [h0]; omega⟩
      · exact ⟨r6 n p + p - (s + 1), by rw [h0]; omega⟩
    obtain ⟨B, hB⟩ : ∃ B, r2 n p + s = eflag n p s * p + B := by
      rcases hec with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · exact ⟨r2 n p + s, by rw [h0]; omega⟩
      · exact ⟨r2 n p + s - p, by rw [h0]; omega⟩
    have ha' : a' + 1 < p := by
      rcases hbc with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] at ha <;> omega
    have hB' : B + 1 < p := by
      rcases hec with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [h0] at hB <;> omega
    have hch := chat_succ (p := p) (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s a' B hs hr6 hr2
      ha ha' hB hB'
    -- assemble
    have n2' : (s : ZMod p) ≠ -(r2 n p : ZMod p) - 1 := by rw [← cr]; exact n2
    have hfin : chat p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) (s + 1) *
          PQ (fun r => - sigZ n p r) ((s : ZMod p) + 1) =
        chat p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s *
          PQ (fun r => - sigZ n p r) (s : ZMod p) := by
      have hA : ((s : ZMod p) - r6 n p) ≠ 0 := sub_ne_zero.2 n1
      have hB : ((s : ZMod p) - (-(r2 n p : ZMod p) - 1)) ≠ 0 := sub_ne_zero.2 n2'
      apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hA) (pow_ne_zero 3 hB))
      linear_combination
        (chat p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) (s + 1)) * hsh +
          (PQ (fun r => - sigZ n p r) (s : ZMod p)) * hch
    unfold wU
    rw [hc, hb, he, PQ_eZ h, PQ_eZ h, PQ_const_shift, PQ_nN _ hN', PQ_nN _ hN]
    linear_combination (PQ (fun _ => lam n p + 4) (s : ZMod p) * Qm n p ((s : ZMod p) + 1) *
      Qm n p (s : ZMod p)) * hfin

end LemmaUThm

section LemmaUClass

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}

lemma sig_mono (n p : ℕ) {s s' : ℕ} (h : s ≤ s') : sig n p s ≤ sig n p s' := by
  unfold sig; split_ifs <;> omega

lemma Qm_ne_zero (s : ZMod p) (hs : ¬ ((lam n p - sigZ n p s) % 2 ≠ 0)) : Qm n p s ≠ 0 := by
  unfold Qm
  refine Finset.prod_ne_zero_iff.2 (fun r _ => ?_)
  by_cases hr : (lam n p - sigZ n p r) % 2 ≠ 0
  · rw [if_pos hr]
    intro h0
    have : s = r := sub_eq_zero.1 h0
    rw [this] at hs; exact hs hr
  · rw [if_neg hr]; exact one_ne_zero

lemma sigZ_nat (s : ℕ) (hs : s < p) : sigZ n p (s : ZMod p) = (sig n p s : ℤ) := by
  unfold sigZ; rw [ZMod.val_natCast_of_lt hs]

lemma lemmaU_chain (h : Rng n p) (s d : ℕ) :
    s + d < p → sig n p s = sig n p (s + d) →
    ¬ ((lam n p - sigZ n p (s : ZMod p)) % 2 ≠ 0) →
    wU n p (s + d) * Qm n p (s : ZMod p) = wU n p s * Qm n p ((s + d : ℕ) : ZMod p) := by
  induction d with
  | zero => intro _ _ _; simp
  | succ d ih =>
    intro hd1 hsg hN
    have hd : s + d < p := by omega
    have sg1 : sig n p s = sig n p (s + d) := by
      have := sig_mono n p (show s ≤ s + d by omega)
      have := sig_mono n p (show s + d ≤ s + (d + 1) by omega)
      omega
    have sg2 : sig n p (s + d) = sig n p (s + d + 1) := by
      have := sig_mono n p (show s + d ≤ s + d + 1 by omega)
      have := sig_mono n p (show s ≤ s + d by omega)
      have e : s + (d + 1) = s + d + 1 := by omega
      rw [e] at hsg
      omega
    have ih' := ih hd sg1 hN
    have hU := lemmaU h (s + d) (by omega) sg2
    have hc : (((s + d : ℕ)) : ZMod p) + 1 = ((s + (d + 1) : ℕ) : ZMod p) := by push_cast; ring
    have hc2 : (s + d + 1 : ℕ) = s + (d + 1) := by omega
    rw [hc] at hU
    rw [hc2] at hU
    have hq : Qm n p (((s + d : ℕ)) : ZMod p) ≠ 0 := by
      refine Qm_ne_zero _ ?_
      rw [sigZ_nat (s + d) hd, ← sg1, ← sigZ_nat s (by omega)]; exact hN
    apply mul_right_cancel₀ hq
    have : wU n p (s + (d + 1)) * Qm n p ((s + d : ℕ) : ZMod p) * Qm n p (s : ZMod p) =
        wU n p (s + d) * Qm n p ((s + (d + 1) : ℕ) : ZMod p) * Qm n p (s : ZMod p) := by
      rw [hU]
    linear_combination this + Qm n p ((s + (d + 1) : ℕ) : ZMod p) * ih'

/-- **Lemma U, class form.**  Within a class, `w_s / Q(s)` is constant (`w_s = K_c Q(s)`). -/
theorem lemmaU_class (h : Rng n p) (s s' : ℕ) (hs : s < p) (hs' : s' < p)
    (hsig : sig n p s = sig n p s') :
    wU n p s' * Qm n p (s : ZMod p) = wU n p s * Qm n p (s' : ZMod p) := by
  have key : ∀ s s' : ℕ, s ≤ s' → s' < p → sig n p s = sig n p s' →
      wU n p s' * Qm n p (s : ZMod p) = wU n p s * Qm n p (s' : ZMod p) := by
    intro s s' hle hs' hsig
    by_cases hN : (lam n p - sigZ n p (s : ZMod p)) % 2 ≠ 0
    · have hN' : (lam n p - sigZ n p (s' : ZMod p)) % 2 ≠ 0 := by
        rw [sigZ_nat s' hs', ← hsig, ← sigZ_nat s (by omega)]; exact hN
      rw [Qm_zero_of_N _ hN, Qm_zero_of_N _ hN']; simp
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      exact lemmaU_chain h s d hs' hsig hN
  rcases le_total s s' with hle | hle
  · exact key s s' hle hs' hsig
  · exact (key s' s hle hs hsig.symm).symm

end LemmaUClass

end CatalanCore.Lai


open CatalanCore.Basic MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section GramToJ

variable {p : ℕ} [hp : Fact p.Prime]

/-- Valuation of the Gram determinant of a CRT basis with integer roots distinct mod `p` gives the
valuation of `J_n` (after the `ν_p` normalisation). -/
theorem GV_laiJ_of_crt {S : Type*} [Fintype S] [DecidableEq S] (n : ℕ) (a : S → ℤ)
    (ha : Function.Injective fun r => (Int.castRingHom (ZMod p)) (a r)) (m : S → ℕ) (d : ℕ)
    (hN : ∑ r, m r + d = 3 * n) (e : ((Σ r : S, Fin (m r)) ⊕ Fin d) ≃ Fin (3 * n)) (E : ℤ)
    (hG : GV p E (Matrix.of fun x y : (Σ r : S, Fin (m r)) ⊕ Fin d =>
      laiL n (crtFam (fun r => ((a r : ℤ) : ℚ)) m d x *
        crtFam (fun r => ((a r : ℤ) : ℚ)) m d y)).det) :
    GV p (E - nuP n p) (laiJ n) := by
  have hf : ∀ x, (crtFam (fun r => ((a r : ℤ) : ℚ)) m d x).natDegree < 3 * n :=
    fun x => crtFam_natDegree_lt _ m d (3 * n) hN x
  rw [gram_det n e _ hf] at hG
  set Bz : Matrix (Fin (3 * n)) (Fin (3 * n)) ℤ :=
    Matrix.of fun (z : Fin (3 * n)) (i : Fin (3 * n)) => (crtFam a m d (e.symm z)).coeff i with hBz
  have hmapf : ∀ x, crtFam (fun r => ((a r : ℤ) : ℚ)) m d x =
      (crtFam a m d x).map (Int.castRingHom ℚ) := by
    intro x
    rw [crtFam_map]
    simp
  have hcoef : coeffMat n (fun z => crtFam (fun r => ((a r : ℤ) : ℚ)) m d (e.symm z)) =
      Bz.map ((MvPolynomial.C : ℚ →+* MP).comp (Int.castRingHom ℚ)) := by
    refine Matrix.ext fun z i => ?_
    simp only [coeffMat, Matrix.of_apply, Matrix.map_apply, hBz, RingHom.comp_apply]
    rw [hmapf, Polynomial.coeff_map]
  have hdetC : (coeffMat n (fun z => crtFam (fun r => ((a r : ℤ) : ℚ)) m d (e.symm z))).det =
      MvPolynomial.C (((Bz.det : ℤ) : ℚ)) := by
    rw [hcoef]
    have := RingHom.map_det ((MvPolynomial.C : ℚ →+* MP).comp (Int.castRingHom ℚ)) Bz
    simpa using this.symm
  have hnd : ¬ (p : ℤ) ∣ Bz.det := crt_det_not_dvd p a ha m d (3 * n) hN e
  have hβ : ((Bz.det : ℤ) : ℚ) ≠ 0 := by
    intro h0
    apply hnd
    have : Bz.det = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  have hβi := inv_intCast_mem (p := p) Bz.det hnd
  rw [hdetC] at hG
  have hdet : GV p E (laiMat n).det := by
    have hc : GV p 0 (MvPolynomial.C ((((Bz.det : ℤ) : ℚ))⁻¹ ^ 2) : MP) :=
      GV.const_loc ((LocRing p).pow_mem hβi 2)
    have := hc.mul hG
    rw [← mul_assoc, ← map_pow, ← map_mul, ← mul_pow, inv_mul_cancel₀ hβ] at this
    simpa using this
  exact GV_laiJ_of_det (p := p) n _ hdet

end GramToJ

section L1Basis

variable {n p : ℕ} [hp : Fact p.Prime]

/-- coordinates of the L1 basis: `(s, i)`, `i < μ_s`, and the `g_j`, `j < d`. -/
abbrev LIdx (n p : ℕ) : Type := (Σ r : Fin p, Fin (mu n p r)) ⊕ Fin (dcnt n p)

/-- integer roots `a_r = -r`. -/
def aL (p : ℕ) (r : Fin p) : ℤ := -((r : ℕ) : ℤ)

/-- the CRT basis over `ℚ`. -/
noncomputable def fL (n p : ℕ) : LIdx n p → Polynomial ℚ :=
  crtFam (fun r : Fin p => ((aL p r : ℤ) : ℚ)) (fun r : Fin p => mu n p r) (dcnt n p)

/-- exponents of `(X + r)`. -/
noncomputable def nuL (n p : ℕ) : LIdx n p → Fin p → ℕ
  | Sum.inl ⟨r0, i⟩ => fun r => if r = r0 then (i : ℕ) else mu n p r
  | Sum.inr _ => fun r => mu n p r

/-- power of `X`. -/
def wL (n p : ℕ) : LIdx n p → ℕ
  | Sum.inl _ => 0
  | Sum.inr j => (j : ℕ)

/-- twice the potential. -/
noncomputable def pot2 (n p : ℕ) : LIdx n p → ℤ
  | Sum.inl ⟨r, i⟩ => 2 * (i : ℤ) - 4 + (sig n p r : ℤ)
  | Sum.inr _ => lam n p

lemma fL_eq (x : LIdx n p) : fL n p x = Pd p (wL n p x) (nuL n p x) := by
  have hX : ∀ r : Fin p, (Polynomial.X - Polynomial.C ((aL p r : ℤ) : ℚ) : Polynomial ℚ) =
      Polynomial.X + Polynomial.C ((r : ℕ) : ℚ) := by
    intro r; simp [aL, sub_eq_add_neg]
  rcases x with ⟨r0, i⟩ | j
  · simp only [fL, crtFam, Sum.elim_inl, crtE, wL, nuL, Pd, pow_zero, one_mul]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin p)) _ (Finset.mem_univ r0)]
    simp only [hX, if_true]
    congr 1
    refine Finset.prod_congr rfl fun r hr => ?_
    have : r ≠ r0 := (Finset.mem_erase.1 hr).1
    simp [this]
  · simp only [fL, crtFam, Sum.elim_inr, crtG, wL, nuL, Pd]
    simp only [hX]

/-- the facts of Lemma S used for the entry bounds. -/
lemma lemmaS_bounds (h : Rng n p) (t : ℕ) (ht : t < p) :
    lam n p + 4 ≤ 2 * (mu n p t : ℤ) + sig n p t ∧ 2 * (mu n p t : ℤ) + sig n p t ≤ lam n p + 5 := by
  have := (lemmaS h).2.2.1 t ht
  split_ifs at this <;> omega

lemma pair_arith (h : Rng n p) (x y : LIdx n p) (s : ℕ) (hs : s < p) :
    pot2 n p x + pot2 n p y ≤
      2 * ((sig n p s : ℤ) - 4 + (nuL n p x ⟨s, hs⟩ : ℕ) + (nuL n p y ⟨s, hs⟩ : ℕ)) := by
  have hSs := lemmaS_bounds h s hs
  have key : ∀ (r : Fin p) (i : Fin (mu n p r)),
      2 * (i : ℤ) - 4 + (sig n p r : ℤ) ≤ lam n p + 5 - 6 ∧ ((i : ℕ) < mu n p r) := by
    intro r i
    have := lemmaS_bounds h r r.2
    have := i.2
    omega
  rcases x with ⟨r, i⟩ | j <;> rcases y with ⟨r', i'⟩ | j'
  · have hr := lemmaS_bounds h r r.2
    have hr' := lemmaS_bounds h r' r'.2
    have hi := i.2
    have hi' := i'.2
    simp only [pot2, nuL]
    by_cases h1 : (⟨s, hs⟩ : Fin p) = r <;> by_cases h2 : (⟨s, hs⟩ : Fin p) = r'
    · have e1 : s = (r : ℕ) := by rw [← h1]
      have e2 : s = (r' : ℕ) := by rw [← h2]
      rw [if_pos h1, if_pos h2]
      have : (r : ℕ) = (r' : ℕ) := by omega
      have : sig n p r = sig n p s := by rw [e1]
      have : sig n p r' = sig n p s := by rw [e2]
      push_cast; omega
    · have e1 : s = (r : ℕ) := by rw [← h1]
      rw [if_pos h1, if_neg h2]
      have : sig n p r = sig n p s := by rw [e1]
      push_cast; omega
    · have e2 : s = (r' : ℕ) := by rw [← h2]
      rw [if_neg h1, if_pos h2]
      have : sig n p r' = sig n p s := by rw [e2]
      push_cast; omega
    · rw [if_neg h1, if_neg h2]
      push_cast; omega
  · have hr := lemmaS_bounds h r r.2
    have hi := i.2
    simp only [pot2, nuL]
    by_cases h1 : (⟨s, hs⟩ : Fin p) = r
    · have e1 : s = (r : ℕ) := by rw [← h1]
      rw [if_pos h1]
      have : sig n p r = sig n p s := by rw [e1]
      push_cast; omega
    · rw [if_neg h1]
      push_cast; omega
  · have hr' := lemmaS_bounds h r' r'.2
    have hi' := i'.2
    simp only [pot2, nuL]
    by_cases h2 : (⟨s, hs⟩ : Fin p) = r'
    · have e2 : s = (r' : ℕ) := by rw [← h2]
      rw [if_pos h2]
      have : sig n p r' = sig n p s := by rw [e2]
      push_cast; omega
    · rw [if_neg h2]
      push_cast; omega
  · simp only [pot2, nuL]
    push_cast; omega

end L1Basis

section L1Entry

variable {n p : ℕ} [hp : Fact p.Prime]

/-- floor of the potential. -/
noncomputable def kL (n p : ℕ) (x : LIdx n p) : ℤ := pot2 n p x / 2

/-- the half-integral group: odd doubled potential. -/
noncomputable def BL (n p : ℕ) : Finset (LIdx n p) := Finset.univ.filter (fun x => pot2 n p x % 2 = 1)

lemma mmF_add (a b : Fin p → ℕ) (s : ℕ) (hs : s < p) :
    mmF p (fun r => a r + b r) s = a ⟨s, hs⟩ + b ⟨s, hs⟩ := by
  simp [mmF, hs]

lemma eL_le (h : Rng n p) (x y : LIdx n p) (s : ℕ) (hs : s < p) :
    kL n p x + kL n p y + (if x ∈ BL n p ∨ y ∈ BL n p then 1 else 0) ≤
      (sig n p s : ℤ) - 4 + (nuL n p x ⟨s, hs⟩ : ℕ) + (nuL n p y ⟨s, hs⟩ : ℕ) := by
  have := pair_arith h x y s hs
  unfold kL BL
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

/-- **Entry bounds.**  `v_p(⟨f_x, f_y⟩) ≥ π_x + π_y` (`+½` on mixed pairs), in integer form. -/
theorem entry_ge (h : Rng n p) (x y : LIdx n p) :
    GV p (kL n p x + kL n p y + (if x ∈ BL n p ∨ y ∈ BL n p then 1 else 0))
      (laiL n (fL n p x * fL n p y)) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  have hF : fL n p x * fL n p y =
      Pd p (wL n p x + wL n p y) (fun r => nuL n p x r + nuL n p y r) := by
    rw [fL_eq, fL_eq, Pd_mul]
  rw [hF]
  have key := laiL_ge_except (p := p) n h.h8 hp3
    (Pd p (wL n p x + wL n p y) (fun r => nuL n p x r + nuL n p y r))
    (fun s => mmF p (fun r => nuL n p x r + nuL n p y r) s)
    (fun s => RRF p (wL n p x + wL n p y) (fun r => nuL n p x r + nuL n p y r) s)
    (fun s _ => RRF_int _ _ _ _) (fun s _ => Pd_decomp _ _ _ s)
    (kL n p x + kL n p y + (if x ∈ BL n p ∨ y ∈ BL n p then 1 else 0)) ∅
    (Finset.empty_subset _)
    (by
      intro k _ _ _
      have hs : k % p < p := Nat.mod_lt _ hp.out.pos
      rw [mmF_add _ _ _ hs]
      have := eL_le h x y _ hs
      push_cast
      linarith)
    (by
      intro k _ _ hkp
      rw [mmF_add _ _ k hkp]
      have := eL_le h x y k hkp
      by_cases h2 : 2 ≤ nuL n p x ⟨k, hkp⟩ + nuL n p y ⟨k, hkp⟩
      · right; exact h2
      · left
        have : min (nuL n p x ⟨k, hkp⟩ + nuL n p y ⟨k, hkp⟩) 1 ≤ 1 := min_le_right _ _
        push_cast at this ⊢
        omega)
  simpa using key

lemma hsum_mu (h : Rng n p) : ∑ r : Fin p, mu n p r + dcnt n p = 3 * n := by
  have hp1 := hp.out.pos
  have hn := h.n2
  have hlam := lam_spec n p hp1 (by omega)
  have h1 : cnt n p (lam n p - 1) < 3 * n := hlam.2 _ (by omega)
  have h2 : ∑ s ∈ range p, mu n p s = cnt n p (lam n p - 1) := rfl
  have h3 : ∑ r : Fin p, mu n p r = ∑ s ∈ range p, mu n p s :=
    Fin.sum_univ_eq_sum_range (fun s => mu n p s) p
  unfold dcnt
  rw [h3]
  omega

end L1Entry

section L1Exact

variable {n p : ℕ} [hp : Fact p.Prime]

lemma pot2_eq (x : LIdx n p) : pot2 n p x = 2 * kL n p x + (if x ∈ BL n p then 1 else 0) := by
  unfold kL BL
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> omega

lemma sum_pot2 : ∑ x, pot2 n p x = 2 * ∑ x, kL n p x + ((BL n p).card : ℤ) := by
  rw [Finset.mul_sum]
  have : ∀ x, pot2 n p x = 2 * kL n p x + (if x ∈ BL n p then 1 else 0) := pot2_eq
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_mem]

lemma card_LIdx (h : Rng n p) : Fintype.card (LIdx n p) = 3 * n := by
  have := hsum_mu h
  simp only [LIdx, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  omega

/-- **The Gram determinant of the L1 basis** has valuation `≥ ∑ 2π`, with no gain. -/
theorem gram_det_ge (h : Rng n p) :
    GV p (∑ x, pot2 n p x)
      (Matrix.of fun x y : LIdx n p => laiL n (fL n p x * fL n p y)).det := by
  classical
  set M : Matrix (LIdx n p) (LIdx n p) MP := Matrix.of fun x y => laiL n (fL n p x * fL n p y) with hMdef
  have hM : ∀ i j, GV p (kL n p i + kL n p j + (if i ∈ BL n p ∨ j ∈ BL n p then 1 else 0)) (M i j) :=
    fun i j => entry_ge h i j
  have hex : ∀ i j : BL n p, ∃ g : MvPolynomial (Fin 3) (LocRing p),
      toQmv p g = MvPolynomial.C ((p : ℚ) ^ (-(kL n p i + kL n p j + 1))) * M i j := by
    intro i j
    have := hM i j
    have hc : (if (i : LIdx n p) ∈ BL n p ∨ (j : LIdx n p) ∈ BL n p then (1 : ℤ) else 0) = 1 := by
      simp [i.2]
    rw [hc] at this
    exact GV.exists_lift this
  choose ZB hZB using hex
  set Z : Matrix (BL n p) (BL n p) (MvPolynomial (Fin 3) (LocRing p)) :=
    Matrix.of (fun i j => ZB i j) with hZ
  have hrk : (Z.map (redMv p)).rank + 0 ≤ (BL n p).card := by
    have := Matrix.rank_le_card_height (Z.map (redMv p))
    simpa using this
  have := GV.det_halfInt (p := p) M (kL n p) (BL n p) hM Z (fun i j => hZB i j) 0 hrk
  rw [sum_pot2]
  simpa using this

lemma aL_inj : Function.Injective fun r : Fin p => (Int.castRingHom (ZMod p)) (aL p r) := by
  intro r r' hrr
  simp only [aL, eq_intCast, Int.cast_neg, Int.cast_natCast, neg_inj] at hrr
  have := (ZMod.natCast_eq_natCast_iff' (r : ℕ) (r' : ℕ) p).1 hrr
  rw [Nat.mod_eq_of_lt r.2, Nat.mod_eq_of_lt r'.2] at this
  exact Fin.ext this

/-- **Lai Lemma 4.4 (LC03, LC04), exact lower bound.**  For `√(8n) < p < 3n`,
`v_p(J_n) ≥ ∑ (the 3n smallest increments) - ν_p`; here `∑_x 2π_x` is that sum
(`∑_s ∑_{i<μ_s}(2i - 4 + σ_s) + d λ`). -/
theorem lai_exact_lower (h : Rng n p) : GV p (∑ x, pot2 n p x - nuP n p) (laiJ n) := by
  have hN := hsum_mu h
  have e : LIdx n p ≃ Fin (3 * n) := Fintype.equivFinOfCardEq (card_LIdx h)
  exact GV_laiJ_of_crt (p := p) n (aL p) aL_inj (fun r : Fin p => mu n p r) (dcnt n p) hN e _
    (gram_det_ge h)

end L1Exact

end CatalanCore.Lai


#print axioms CatalanCore.Lai.lemmaU
#print axioms CatalanCore.Lai.lemmaU_class
#print axioms CatalanCore.Lai.entry_ge
#print axioms CatalanCore.Lai.gram_det_ge
#print axioms CatalanCore.Lai.lai_exact_lower
