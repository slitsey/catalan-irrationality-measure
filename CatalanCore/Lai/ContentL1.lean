module

public import CatalanCore.Lai.TieBlock
public import CatalanCore.Lai.ClassCount
public import CatalanCore.Content.HankelCorank

@[expose] public section

/-!
# `CatalanCore.Lai.ContentL1`: Theorem L1 (first-level gain `x₁`) for Lai's `J_n`

For every prime `√(8n) < p < 3n` (`Rng n p`): `v_p(J_n) ≥ LaiExact(n, p) + x₁` (`lai_L1`), where
`x₁ = max(0, min(d - |Z|, |W| - d))` (`xone`).  The proof identifies the reduced tie block of the Gram
matrix with the matrix `NB` of `Content.HankelCorank` (entries `ent_ee_same`, `ent_eg`, `ent_gg`,
`entry_NB`), proves the shifted-sum identity from Lemma U and `sum_zmod_eval_eq_zero` (`hsum_core`),
and applies `NB_corank_spec` (`tie_rank`) inside `GV.det_halfInt` / `GV.det_halfInt_mirror`.
-/

-- part L1a
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Flags

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the harmonic correction `δ` of a node, in terms of the class flags `(b, ε)` and `ℓ`. -/
noncomputable def vLf (n p b ε l : ℕ) : ℚ :=
  -2 * (Hq 3 l * (5 * Hq 1 l - 3 * Hq 1 (q2 n p + l + ε) - 2 * Hq 1 (q6 n p - l - b)) + 3 * Hq 4 l)

lemma vL_flags (k : ℕ) (hk : k ≤ 6 * n) :
    vL n p k (k / p) = vLf n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) := by
  have hpp := hp.out.pos
  obtain ⟨h1, h2, h3⟩ := sub_div_mod p (6 * n) k hpp hk
  obtain ⟨g1, g2⟩ := add_div_mod p k (2 * n) hpp
  have e2 : (2 * n + k) / p = q2 n p + k / p + eflag n p (k % p) := by
    rw [add_comm (2 * n) k, g1]
    unfold q2 eflag r2
    split_ifs <;> omega
  have e6 : (6 * n - k) / p = q6 n p - k / p - bflag n p (k % p) := by
    rw [h2]
    unfold q6 bflag r6
    split_ifs <;> omega
  unfold vL laiDelta vLf
  rw [e2, e6]

end Flags

section Cast

variable {p : ℕ} [hp : Fact p.Prime]

/-- reduction mod `p`, total on `ℚ` (`0` off `ℤ_(p)`). -/
noncomputable def rzT (p : ℕ) [Fact p.Prime] (x : ℚ) : ZMod p :=
  open Classical in if h : x ∈ LocRing p then redQ p ⟨x, h⟩ else 0

lemma rzT_of_mem {x : ℚ} (hx : x ∈ LocRing p) : rzT p x = (x : ZMod p) := by
  unfold rzT; rw [dif_pos hx]; rfl

lemma rzT_mul {x y : ℚ} (hx : x ∈ LocRing p) (hy : y ∈ LocRing p) :
    rzT p (x * y) = rzT p x * rzT p y := by
  have hxy : x * y ∈ LocRing p := (LocRing p).mul_mem hx hy
  unfold rzT
  rw [dif_pos hxy, dif_pos hx, dif_pos hy]
  exact map_mul (redQ p) ⟨x, hx⟩ ⟨y, hy⟩

lemma rzT_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (hf : ∀ i ∈ s, f i ∈ LocRing p) :
    rzT p (∑ i ∈ s, f i) = ∑ i ∈ s, rzT p (f i) := by
  classical
  have hs : (∑ i ∈ s, f i) ∈ LocRing p := (LocRing p).sum_mem hf
  unfold rzT
  rw [dif_pos hs]
  have : (⟨∑ i ∈ s, f i, hs⟩ : LocRing p) = ∑ i : ↥s, (⟨f i, hf i i.2⟩ : LocRing p) := by
    apply Subtype.ext
    have := map_sum (LocRing p).subtype (fun i : ↥s => (⟨f i, hf i i.2⟩ : LocRing p)) Finset.univ
    simp only [Subring.subtype_apply] at this
    show (∑ i ∈ s, f i) = ((∑ i : ↥s, (⟨f i, hf i i.2⟩ : LocRing p) : LocRing p) : ℚ)
    exact (Finset.sum_coe_sort s f).symm.trans this.symm
  rw [this, map_sum, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [dif_pos (hf i i.2)]

lemma rzT_nat (m : ℕ) : rzT p (m : ℚ) = (m : ZMod p) := by
  rw [rzT_of_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (m : ℤ))]
  simp

/-- the exponent-`ν` cofactor at residue `s`, evaluated at `-s`, reduced mod `p`. -/
noncomputable def RRz (p : ℕ) [Fact p.Prime] (w : ℕ) (ν : Fin p → ℕ) (s : ℕ) : ZMod p :=
  (-(s : ZMod p)) ^ w * ∏ r : Fin p, if (r : ℕ) = s then 1 else (((r : ℕ) : ZMod p) - (s : ZMod p)) ^ ν r

lemma RRF_eval_cast (w : ℕ) (ν : Fin p → ℕ) (s : ℕ) (hs : s < p) :
    (((RRF p w ν s).eval (-(s : ℚ)) : ℚ) : ZMod p) = RRz p w ν s := by
  have hint : (RRF p w ν s).eval (-(s : ℚ)) =
      (((-(s : ℤ)) ^ w * ∏ r ∈ (Finset.univ : Finset (Fin p)).erase ⟨s, hs⟩,
        (((r : ℕ) : ℤ) - s) ^ ν r : ℤ) : ℚ) := by
    unfold RRF
    simp only [hs, dite_true, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C]
    push_cast
    congr 1
    refine Finset.prod_congr rfl (fun r _ => ?_)
    ring
  rw [hint, Rat.cast_intCast]
  push_cast
  unfold RRz
  congr 1
  rw [← Finset.prod_erase (Finset.univ : Finset (Fin p)) (a := (⟨s, hs⟩ : Fin p))
    (f := fun r : Fin p => if (r : ℕ) = s then (1 : ZMod p) else (((r : ℕ) : ZMod p) - (s : ZMod p)) ^ ν r)
    (by simp)]
  refine Finset.prod_congr rfl (fun r hr => ?_)
  have : (r : ℕ) ≠ s := fun h => (Finset.mem_erase.1 hr).1 (Fin.ext h)
  simp [this]

end Cast

section Res

variable {n p : ℕ}

/-- node sums at a residue: `k = r + ℓ p`, `1 ≤ ℓ ≤ L_r`. -/
lemma sum_res {M : Type*} [AddCommMonoid M] (hp : 0 < p) (r : ℕ) (hr : r < p) (g : ℕ → M) :
    ∑ k ∈ (range (6 * n + 1)).filter (fun k => 1 ≤ k / p ∧ k % p = r), g k =
      ∑ l ∈ Icc 1 (Lc n p r), g (r + l * p) := by
  have hq := qr6 n p hp
  have hr6 := r6_lt n p hp
  refine Finset.sum_nbij' (fun k => k / p) (fun l => r + l * p) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hk ⊢
    obtain ⟨hk6, h1, h2⟩ := hk
    refine ⟨h1, ?_⟩
    have hkk : k = p * (k / p) + r := by rw [← h2]; exact (Nat.div_add_mod k p).symm
    unfold Lc
    split_ifs with hc
    · by_contra hcon
      push_neg at hcon
      have : (q6 n p + 1) * p ≤ (k / p) * p := Nat.mul_le_mul_right p hcon
      nlinarith
    · by_contra hcon
      push_neg at hcon
      have hq : q6 n p ≤ k / p := by omega
      have : q6 n p * p ≤ (k / p) * p := Nat.mul_le_mul_right p hq
      nlinarith
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hl ⊢
    obtain ⟨h1, h2⟩ := hl
    have hd : (r + l * p) / p = l := by
      rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr]; simp
    have hm : (r + l * p) % p = r := by
      rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hr
    refine ⟨?_, by rw [hd]; exact h1, hm⟩
    unfold Lc at h2
    split_ifs at h2 with hc
    · nlinarith
    · have : l + 1 ≤ q6 n p := by omega
      have : (l + 1) * p ≤ q6 n p * p := Nat.mul_le_mul_right p this
      nlinarith
  · intro k hk
    simp only [Finset.mem_filter] at hk
    have hkk : k = p * (k / p) + r := by rw [← hk.2.2]; exact (Nat.div_add_mod k p).symm
    show r + (k / p) * p = k
    rw [mul_comm]; omega
  · intro l hl
    simp only [Finset.mem_Icc] at hl
    show (r + l * p) / p = l
    rw [Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr]; simp
  · intro k hk
    simp only [Finset.mem_filter] at hk
    have hkk : k = p * (k / p) + r := by rw [← hk.2.2]; exact (Nat.div_add_mod k p).symm
    congr 1
    rw [mul_comm]; omega

end Res

end CatalanCore.Lai

-- part L1b
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Tight

variable {n p : ℕ} [hp : Fact p.Prime]

/-- tie residues: `σ(s) ≡ λ (mod 2)`. -/
def tieR (n p s : ℕ) : Prop := (lam n p - (sig n p s : ℤ)) % 2 = 0

noncomputable instance (n p : ℕ) : DecidablePred (tieR n p) := fun s => inferInstanceAs (Decidable (_ = _))

lemma mu_sig (h : Rng n p) (t : ℕ) (ht : t < p) :
    2 * (mu n p t : ℤ) + sig n p t = lam n p + 4 + (if tieR n p t then 0 else 1) := by
  have := (lemmaS h).2.2.1 t ht
  unfold tieR
  exact this

/-- `x` and `y` meet the node bound with equality at residue `s`. -/
def Tight (n p : ℕ) (x y : LIdx n p) (s : ℕ) (hs : s < p) : Prop :=
  pot2 n p x + pot2 n p y = 2 * ((sig n p s : ℤ) - 4 + (nuL n p x ⟨s, hs⟩ : ℕ) + (nuL n p y ⟨s, hs⟩ : ℕ))

lemma tight_ee (h : Rng n p) (r r' : Fin p) (i : Fin (mu n p r)) (i' : Fin (mu n p r'))
    (s : ℕ) (hs : s < p) :
    Tight n p (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) s hs ↔ (r = r' ∧ (r : ℕ) = s) := by
  obtain ⟨r, hr⟩ := r
  obtain ⟨r', hr'⟩ := r'
  obtain ⟨i, hi⟩ := i
  obtain ⟨i', hi'⟩ := i'
  have b1 := lemmaS_bounds h r hr
  have b2 := lemmaS_bounds h r' hr'
  have b3 := lemmaS_bounds h s hs
  unfold Tight
  simp only [pot2, nuL, Fin.mk.injEq, Fin.val_mk] at *
  dsimp only at hi hi' ⊢
  by_cases h1 : s = r <;> by_cases h2 : s = r'
  · subst h1; subst h2
    simp only [if_true]; push_cast
    constructor <;> intro _ <;> first | omega | exact ⟨trivial, trivial⟩ | trivial
  · subst h1
    simp only [if_true, h2, if_false]; push_cast
    constructor
    · intro hh; omega
    · rintro ⟨e, e2⟩; first | omega | exact e.elim | exact e2.elim
  · subst h2
    simp only [if_true, h1, if_false]; push_cast
    constructor
    · intro hh; omega
    · rintro ⟨e, e2⟩; first | omega | exact e.elim | exact e2.elim
  · simp only [h1, h2, if_false]; push_cast
    constructor
    · intro hh; omega
    · rintro ⟨e2, e⟩; first | omega | exact e.elim | exact e2.elim

lemma tight_eg (h : Rng n p) (r : Fin p) (i : Fin (mu n p r)) (hr : tieR n p r) (j : Fin (dcnt n p))
    (s : ℕ) (hs : s < p) :
    Tight n p (Sum.inl ⟨r, i⟩) (Sum.inr j) s hs ↔ (r : ℕ) = s := by
  obtain ⟨r, hr0⟩ := r
  obtain ⟨i, hi⟩ := i
  have b1 := mu_sig h r hr0
  have b3 := lemmaS_bounds h s hs
  have b1' : (if tieR n p r then (0 : ℤ) else 1) = 0 := by simp [hr]
  rw [b1'] at b1
  unfold Tight
  simp only [pot2, nuL, Fin.mk.injEq, Fin.val_mk] at *
  dsimp only at hi ⊢
  by_cases h1 : s = r
  · subst h1; simp only [if_true]; push_cast
    constructor <;> intro _ <;> first | omega | trivial
  · simp only [h1, if_false]; push_cast
    constructor
    · intro hh; omega
    · intro e; omega

lemma tight_gg (h : Rng n p) (j j' : Fin (dcnt n p)) (s : ℕ) (hs : s < p) :
    Tight n p (Sum.inr j) (Sum.inr j') s hs ↔ tieR n p s := by
  have b3 := mu_sig h s hs
  unfold Tight
  simp only [pot2, nuL]
  by_cases ht : tieR n p s
  · simp only [ht, if_true] at b3
    exact ⟨fun _ => ht, fun _ => by omega⟩
  · simp only [ht, if_false] at b3
    exact ⟨fun hh => by omega, fun hh => absurd hh ht⟩

lemma mem_Eset_iff (x y : LIdx n p) (k : ℕ) :
    k ∈ Eset n p x y ↔ k ≤ 6 * n ∧ 1 ≤ k / p ∧ ∃ hs : k % p < p, Tight n p x y (k % p) hs := by
  have hs : k % p < p := Nat.mod_lt _ hp.out.pos
  unfold Eset
  simp only [Finset.mem_filter, Finset.mem_range]
  have hm : mmk n p x y k = nuL n p x ⟨k % p, hs⟩ + nuL n p y ⟨k % p, hs⟩ := by
    unfold mmk nuS
    rw [mmF_add (nuL n p x) (nuL n p y) _ hs]
  rw [hm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h2, hs, by unfold Tight; push_cast at h3 ⊢; linarith⟩
  · rintro ⟨h1, h2, _, h3⟩
    exact ⟨by omega, h2, by unfold Tight at h3; push_cast; linarith⟩

end Tight

end CatalanCore.Lai

-- part L1c
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Reduce

variable {n p : ℕ} [hp : Fact p.Prime]

/-- `∏_{r ≠ s} (r - s)^{2 μ_r}` over `𝔽_p`. -/
noncomputable def Pm (n p s : ℕ) : ZMod p :=
  ∏ r : Fin p, if (r : ℕ) = s then 1 else (((r : ℕ) : ZMod p) - (s : ZMod p)) ^ (2 * mu n p r)

/-- the weight `w_s = ĉ_s ∏_{r≠s} (r - s)^{2 μ_r}`. -/
noncomputable def wz (n p s : ℕ) [Fact p.Prime] : ZMod p :=
  chat p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s * Pm n p s

/-- one node of the class constant `Φ`. -/
noncomputable def tauF (n p b ε m l : ℕ) [Fact p.Prime] : ZMod p :=
  kappa p (q6 n p) (q2 n p) b ε l * rzT p (leadF m l (uL l) (vLf n p b ε l))

/-- the class constant `Φ_c(m) = ∑_{ℓ=1}^{L_c} κ_c(ℓ) · red(leadF)`. -/
noncomputable def PhiF (n p b ε m : ℕ) [Fact p.Prime] : ZMod p :=
  ∑ l ∈ Icc 1 (q6 n p - b), tauF n p b ε m l

noncomputable def Phi (n p s m : ℕ) [Fact p.Prime] : ZMod p :=
  PhiF n p (bflag n p s) (eflag n p s) m

lemma Phi_class (s s' : ℕ) (hs : sig n p s = sig n p s') (m : ℕ) : Phi n p s m = Phi n p s' m := by
  have h1 := sig_eq_flags n p s
  have h2 := sig_eq_flags n p s'
  have hb : ∀ t, bflag n p t = 0 ∨ bflag n p t = 1 := fun t => by unfold bflag; split_ifs <;> simp
  have he : ∀ t, eflag n p t = 0 ∨ eflag n p t = 1 := fun t => by unfold eflag; split_ifs <;> simp
  have hb1 : bflag n p s = bflag n p s' := by
    rcases hb s with a | a <;> rcases hb s' with b | b <;> rcases he s with c | c <;> rcases he s' with d | d <;> omega
  have he1 : eflag n p s = eflag n p s' := by
    rcases hb s with a | a <;> rcases hb s' with b | b <;> rcases he s with c | c <;> rcases he s' with d | d <;> omega
  unfold Phi; rw [hb1, he1]

lemma rz_qTerm (h : Rng n p) (x y : LIdx n p) (k : ℕ) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p) :
    rzT p (qTerm n p x y k) =
      kappa p (q6 n p) (q2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k / p) *
        chat p (r6 n p) (r2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k % p) *
        RRz p (wS n p x y) (nuS n p x y) (k % p) *
        rzT p (leadF (mmk n p x y k) (k / p) (uL (k / p))
          (vLf n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p))) := by
  have hp3 : 3 ≤ p := by have := h.p5; omega
  have hs : k % p < p := Nat.mod_lt _ hp.out.pos
  have hkp : k / p < p := by
    rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by have := h.h8; omega)
  obtain ⟨u, hu, hu2, -⟩ := laiCoef_unit (p := p) h.h8 hp3 k hk
  have huk : uk n p k = u := by
    unfold uk; rw [hu]; exact Nat.mul_div_cancel_left _ (pow_pos hp.out.pos _)
  have ha : ((uk n p k : ℕ) : ℚ) ∈ LocRing p := natq_mem _
  have hb : (RRk n p x y k).eval (-((k % p : ℕ) : ℚ)) ∈ LocRing p :=
    (RRF_int (p := p) _ _ _ _).eval_mem ((LocRing p).neg_mem (natq_mem _))
  have hc : leadF (mmk n p x y k) (k / p) (uL (k / p)) (vL n p k (k / p)) ∈ LocRing p :=
    leadF_mem (p := p) _ _ _ _ (natq_mem _) (uL_mem (p := p) _ hkp) (vL_mem (p := p) n k _ h.h8 hk hkp)
  unfold qTerm
  rw [rzT_mul ((LocRing p).mul_mem ha hb) hc, rzT_mul ha hb, rzT_nat, rzT_of_mem hb, huk, hu2,
    vL_flags k hk]
  unfold RRk
  rw [RRF_eval_cast _ _ _ hs]

lemma RRz_eq (w : ℕ) (ν : Fin p → ℕ) (s : ℕ) (hν : ∀ r : Fin p, (r : ℕ) ≠ s → ν r = 2 * mu n p r) :
    RRz p w ν s = (-(s : ZMod p)) ^ w * Pm n p s := by
  unfold RRz Pm
  congr 1
  refine Finset.prod_congr rfl (fun r _ => ?_)
  by_cases hr : (r : ℕ) = s
  · simp [hr]
  · simp only [hr, if_false, hν r hr]

lemma entry_sum (h : Rng n p) (x y : LIdx n p) (R : Finset ℕ) (hR : ∀ s ∈ R, s < p)
    (hE : ∀ k, k ∈ Eset n p x y ↔ k ≤ 6 * n ∧ 1 ≤ k / p ∧ k % p ∈ R)
    (hν : ∀ s ∈ R, ∀ r : Fin p, (r : ℕ) ≠ s → nuS n p x y r = 2 * mu n p r)
    (M : ℕ → ℕ) (hM : ∀ s ∈ R, ∀ hs : s < p, mmF p (nuS n p x y) s = M s) :
    ∑ k ∈ Eset n p x y, rzT p (qTerm n p x y k) =
      ∑ s ∈ R, (-(s : ZMod p)) ^ (wS n p x y) * wz n p s * Phi n p s (M s) := by
  have hpp := hp.out.pos
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => k % p) (t := R)
    (fun k hk => ((hE k).1 hk).2.2)]
  refine Finset.sum_congr rfl (fun s hsR => ?_)
  have hsp := hR s hsR
  have hset : (Eset n p x y).filter (fun k => k % p = s) =
      (range (6 * n + 1)).filter (fun k => 1 ≤ k / p ∧ k % p = s) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, hE]
    constructor
    · rintro ⟨⟨a, b, c⟩, d⟩; exact ⟨by omega, b, d⟩
    · rintro ⟨a, b, d⟩; exact ⟨⟨by omega, b, d ▸ hsR⟩, d⟩
  rw [hset, sum_res hpp s hsp]
  unfold Phi PhiF
  rw [Finset.mul_sum]
  have hLc : Lc n p s = q6 n p - bflag n p s := by unfold Lc bflag; split_ifs <;> omega
  refine Finset.sum_congr (by rw [hLc]) (fun l hl => ?_)
  have hl' := Finset.mem_Icc.1 hl
  have hk6 : s + l * p ≤ 6 * n := by
    have := hl'.2
    unfold bflag at this
    have hq := qr6 n p hpp
    have hr6 := r6_lt n p hpp
    split_ifs at this with hc
    · have h1 : l + 1 ≤ q6 n p := by have := hl'.1; omega
      nlinarith [Nat.mul_le_mul_right p h1]
    · have h1 : l ≤ q6 n p := by omega
      have h2 : s ≤ r6 n p := by omega
      nlinarith [Nat.mul_le_mul_right p h1]
  have hd : (s + l * p) / p = l := by
    rw [Nat.add_mul_div_right _ _ hpp, Nat.div_eq_of_lt hsp]; simp
  have hm : (s + l * p) % p = s := by
    rw [Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hsp
  rw [rz_qTerm h x y _ hk6 (by rw [hd]; exact hl'.1), hd, hm,
    RRz_eq _ _ _ (hν s hsR)]
  have hmk : mmk n p x y (s + l * p) = M s := by
    unfold mmk; rw [hm]; exact hM s hsR hsp
  rw [hmk]
  unfold wz tauF
  ring

end Reduce

end CatalanCore.Lai

-- part L1d
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Ent

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the tie residues. -/
noncomputable def Sres (n p : ℕ) : Finset ℕ := (range p).filter (tieR n p)

lemma mem_Sres {s : ℕ} : s ∈ Sres n p ↔ s < p ∧ tieR n p s := by
  unfold Sres; simp [Finset.mem_filter, Finset.mem_range]

/-- the reduced entry of `⟨f_x, f_y⟩`. -/
noncomputable def ent (n p : ℕ) [Fact p.Prime] (x y : LIdx n p) : ZMod p :=
  ∑ k ∈ Eset n p x y, rzT p (qTerm n p x y k)

lemma nuS_mu_ee (r r' : Fin p) (i : Fin (mu n p r)) (i' : Fin (mu n p r')) (s : ℕ)
    (hs : r.1 = s) (hs' : r'.1 = s) (t : Fin p) (ht : (t : ℕ) ≠ s) :
    nuS n p (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) t = 2 * mu n p t := by
  have h1 : t ≠ r := fun e => ht (by rw [e]; exact hs)
  have h2 : t ≠ r' := fun e => ht (by rw [e]; exact hs')
  simp only [nuS, nuL, h1, h2, if_false]; ring

lemma mmF_nuS (x y : LIdx n p) (s : ℕ) (hs : s < p) :
    mmF p (nuS n p x y) s = nuL n p x ⟨s, hs⟩ + nuL n p y ⟨s, hs⟩ := by
  unfold nuS; exact mmF_add (nuL n p x) (nuL n p y) s hs

theorem ent_ee_same (h : Rng n p) (r : Fin p) (i i' : Fin (mu n p r)) :
    ent n p (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r, i'⟩) = wz n p r * Phi n p r ((i : ℕ) + i') := by
  unfold ent
  have := entry_sum h (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r, i'⟩) {r.1} (by simp)
    (fun k => by
      rw [mem_Eset_iff]
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨a, b, hs, ht⟩
        exact ⟨a, b, ((tight_ee h r r i i' _ hs).1 ht).2.symm⟩
      · rintro ⟨a, b, c⟩
        have hs : k % p < p := Nat.mod_lt _ hp.out.pos
        exact ⟨a, b, hs, (tight_ee h r r i i' _ hs).2 ⟨rfl, c.symm⟩⟩)
    (fun s hs t ht => by
      rw [Finset.mem_singleton] at hs
      exact nuS_mu_ee r r i i' s hs.symm hs.symm t ht)
    (fun _ => (i : ℕ) + i')
    (fun s hs hlt => by
      rw [Finset.mem_singleton] at hs
      rw [mmF_nuS _ _ _ hlt]
      subst hs
      simp [nuL])
  rw [this]
  simp [wS, wL]

theorem ent_ee_ne (h : Rng n p) (r r' : Fin p) (hne : r ≠ r') (i : Fin (mu n p r)) (i' : Fin (mu n p r')) :
    ent n p (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) = 0 := by
  unfold ent
  have : Eset n p (Sum.inl ⟨r, i⟩) (Sum.inl ⟨r', i'⟩) = ∅ := by
    ext k
    rw [mem_Eset_iff]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨a, b, hs, ht⟩
    exact hne ((tight_ee h r r' i i' _ hs).1 ht).1
  rw [this]; simp

theorem ent_eg (h : Rng n p) (r : Fin p) (hr : tieR n p r) (i : Fin (mu n p r)) (j : Fin (dcnt n p)) :
    ent n p (Sum.inl ⟨r, i⟩) (Sum.inr j) =
      (-((r : ℕ) : ZMod p)) ^ (j : ℕ) * wz n p r * Phi n p r ((i : ℕ) + mu n p r) := by
  unfold ent
  have := entry_sum h (Sum.inl ⟨r, i⟩) (Sum.inr j) {r.1} (by simp)
    (fun k => by
      rw [mem_Eset_iff]
      simp only [Finset.mem_singleton]
      constructor
      · rintro ⟨a, b, hs, ht⟩
        exact ⟨a, b, ((tight_eg h r i hr j _ hs).1 ht).symm⟩
      · rintro ⟨a, b, c⟩
        have hs : k % p < p := Nat.mod_lt _ hp.out.pos
        exact ⟨a, b, hs, (tight_eg h r i hr j _ hs).2 c.symm⟩)
    (fun s hs t ht => by
      rw [Finset.mem_singleton] at hs
      have h1 : t ≠ r := fun e => ht (by rw [e]; exact hs.symm)
      simp only [nuS, nuL, h1, if_false]; ring)
    (fun _ => (i : ℕ) + mu n p r)
    (fun s hs hlt => by
      rw [Finset.mem_singleton] at hs
      rw [mmF_nuS _ _ _ hlt]
      subst hs
      simp [nuL])
  rw [this]
  simp [wS, wL]

theorem ent_ge (h : Rng n p) (r : Fin p) (hr : tieR n p r) (i : Fin (mu n p r)) (j : Fin (dcnt n p)) :
    ent n p (Sum.inr j) (Sum.inl ⟨r, i⟩) =
      (-((r : ℕ) : ZMod p)) ^ (j : ℕ) * wz n p r * Phi n p r ((i : ℕ) + mu n p r) := by
  unfold ent
  have := entry_sum h (Sum.inr j) (Sum.inl ⟨r, i⟩) {r.1} (by simp)
    (fun k => by
      rw [mem_Eset_iff]
      simp only [Finset.mem_singleton]
      have hT : ∀ hs : k % p < p, Tight n p (Sum.inr j) (Sum.inl ⟨r, i⟩) (k % p) hs ↔
          Tight n p (Sum.inl ⟨r, i⟩) (Sum.inr j) (k % p) hs := fun hs => by
        unfold Tight; constructor <;> intro hh <;> linarith
      constructor
      · rintro ⟨a, b, hs, ht⟩
        exact ⟨a, b, (((tight_eg h r i hr j _ hs).1 ((hT hs).1 ht))).symm⟩
      · rintro ⟨a, b, c⟩
        have hs : k % p < p := Nat.mod_lt _ hp.out.pos
        exact ⟨a, b, hs, (hT hs).2 ((tight_eg h r i hr j _ hs).2 c.symm)⟩)
    (fun s hs t ht => by
      rw [Finset.mem_singleton] at hs
      have h1 : t ≠ r := fun e => ht (by rw [e]; exact hs.symm)
      simp only [nuS, nuL, h1, if_false]; ring)
    (fun _ => (i : ℕ) + mu n p r)
    (fun s hs hlt => by
      rw [Finset.mem_singleton] at hs
      rw [mmF_nuS _ _ _ hlt]
      subst hs
      simp [nuL]; ring)
  rw [this]
  simp [wS, wL]

theorem ent_gg (h : Rng n p) (j j' : Fin (dcnt n p)) :
    ent n p (Sum.inr j) (Sum.inr j') =
      ∑ s ∈ Sres n p, (-(s : ZMod p)) ^ ((j : ℕ) + j') * wz n p s * Phi n p s (2 * mu n p s) := by
  unfold ent
  have := entry_sum h (Sum.inr j) (Sum.inr j') (Sres n p) (fun s hs => (mem_Sres.1 hs).1)
    (fun k => by
      rw [mem_Eset_iff]
      constructor
      · rintro ⟨a, b, hs, ht⟩
        exact ⟨a, b, mem_Sres.2 ⟨hs, (tight_gg h j j' _ hs).1 ht⟩⟩
      · rintro ⟨a, b, c⟩
        have hs := (mem_Sres.1 c).1
        exact ⟨a, b, hs, (tight_gg h j j' _ hs).2 (mem_Sres.1 c).2⟩)
    (fun s hs t ht => by simp only [nuS, nuL]; ring)
    (fun s => 2 * mu n p s)
    (fun s hs hlt => by rw [mmF_nuS _ _ _ hlt]; simp only [nuL]; ring)
  rw [this]
  simp [wS, wL]

end Ent

end CatalanCore.Lai

-- part L1e
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section ZSum

variable {n p : ℕ} [hp : Fact p.Prime]

lemma sum_zmod_range {M : Type*} [AddCommMonoid M] (F : ZMod p → M) :
    ∑ r : ZMod p, F r = ∑ r ∈ range p, F (r : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_nbij' (fun r : ZMod p => r.val) (fun m : ℕ => (m : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact Finset.mem_range.2 (ZMod.val_lt r)
  · intro m _; exact Finset.mem_univ _
  · intro r _; exact ZMod.natCast_zmod_val r
  · intro m hm; exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hm)
  · intro r _; simp

lemma prod_zmod_range {M : Type*} [CommMonoid M] (F : ZMod p → M) :
    ∏ r : ZMod p, F r = ∏ r ∈ range p, F (r : ZMod p) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.prod_nbij' (fun r : ZMod p => r.val) (fun m : ℕ => (m : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact Finset.mem_range.2 (ZMod.val_lt r)
  · intro m _; exact Finset.mem_univ _
  · intro r _; exact ZMod.natCast_zmod_val r
  · intro m hm; exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hm)
  · intro r _; simp

lemma natCast_inj_lt {a b : ℕ} (ha : a < p) (hb : b < p) : (a : ZMod p) = (b : ZMod p) ↔ a = b := by
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

lemma wz_eq_wU (s : ℕ) (hs : s < p) : wz n p s = wU n p s := by
  unfold wz wU Pm PQ
  congr 1
  rw [prod_zmod_range (fun r : ZMod p => if r = (s : ZMod p) then (1 : ZMod p) else
    ((s : ZMod p) - r) ^ (eZ n p r)), ← Fin.prod_univ_eq_prod_range
      (fun r : ℕ => if (r : ZMod p) = (s : ZMod p) then (1 : ZMod p) else
        ((s : ZMod p) - (r : ZMod p)) ^ (eZ n p (r : ZMod p))) p]
  refine Finset.prod_congr rfl (fun r _ => ?_)
  have hr := r.2
  by_cases he : (r : ℕ) = s
  · simp [he]
  · have : ¬ ((r : ℕ) : ZMod p) = (s : ZMod p) := fun e => he ((natCast_inj_lt hr hs).1 e)
    simp only [he, this, if_false]
    have hv : ((r : ℕ) : ZMod p).val = r := ZMod.val_natCast_of_lt hr
    have : eZ n p ((r : ℕ) : ZMod p) = ((2 * mu n p r : ℕ) : ℤ) := by
      unfold eZ; rw [hv]; push_cast; ring
    rw [this, zpow_natCast]
    have : ((s : ZMod p) - ((r : ℕ) : ZMod p)) ^ (2 * mu n p r) =
        (-(((r : ℕ) : ZMod p) - (s : ZMod p))) ^ (2 * mu n p r) := by ring_nf
    rw [this, Even.neg_pow ⟨mu n p r, by ring⟩]

end ZSum

section Hsum

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the non-tie residues of `ZMod p`. -/
noncomputable def Nz (n p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Finset.univ.filter (fun r => (lam n p - sigZ n p r) % 2 ≠ 0)

lemma Qm_eq_prod (s : ZMod p) : Qm n p s = ∏ r ∈ Nz n p, (s - r) := by
  unfold Qm Nz; rw [Finset.prod_filter]

lemma card_Nz (hpp : 0 < p) :
    (Nz n p).card = ((range p).filter (fun s => ¬ tieR n p s)).card := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.card_nbij' (fun r : ZMod p => r.val) (fun m : ℕ => (m : ZMod p)) ?_ ?_ ?_ ?_
  · intro r hr
    have hr' := (Finset.mem_filter.1 hr).2
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (ZMod.val_lt r), hr'⟩
  · intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.1 hm
    have hm1' := Finset.mem_range.1 hm1
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show (lam n p - ((sig n p (m : ZMod p).val : ℕ) : ℤ)) % 2 ≠ 0
    rw [ZMod.val_natCast_of_lt hm1']; exact hm2
  · intro r _; exact ZMod.natCast_zmod_val r
  · intro m hm
    exact ZMod.val_natCast_of_lt (Finset.mem_range.1 (Finset.mem_filter.1 hm).1)

/-- **The shifted-sum identity** (`hsum` of `NB_corank_spec`). -/
theorem hsum_core (h : Rng n p) (σW : ℕ) (Wr Zr : Finset ℕ)
    (hW : ∀ s ∈ Wr, s < p ∧ tieR n p s ∧ sig n p s = σW) (hZ : ∀ z ∈ Zr, z < p ∧ tieR n p z)
    (hdisj : Disjoint Wr Zr) (hcover : ∀ s < p, tieR n p s → s ∈ Wr ∨ s ∈ Zr) (m j : ℕ)
    (hdeg : ((range p).filter (fun s => ¬ tieR n p s)).card + Zr.card + m + j ≤ p - 2) :
    ∑ s ∈ Wr, wz n p s * ((∏ z ∈ Zr, ((-(s : ZMod p)) - (-(z : ZMod p)))) * (-(s : ZMod p)) ^ m) *
      (-(s : ZMod p)) ^ j = 0 := by
  have hpp := hp.out.pos
  -- the polynomial
  set Hp : Polynomial (ZMod p) := (∏ r ∈ Nz n p, (Polynomial.X - Polynomial.C r)) *
      (∏ z ∈ Zr, (Polynomial.C (z : ZMod p) - Polynomial.X)) * (-Polynomial.X) ^ (m + j) with hHp
  have hev : ∀ x : ZMod p, Hp.eval x = Qm n p x * (∏ z ∈ Zr, ((z : ZMod p) - x)) * (-x) ^ (m + j) := by
    intro x
    simp only [hHp, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_neg, Qm_eq_prod]
  have hdegH : Hp.natDegree ≤ p - 2 := by
    have h1 : (∏ r ∈ Nz n p, (Polynomial.X - Polynomial.C r)).natDegree = (Nz n p).card := by
      rw [Polynomial.natDegree_prod_of_monic _ _ (fun r _ => Polynomial.monic_X_sub_C _)]
      simp
    have h2 : (∏ z ∈ Zr, (Polynomial.C (z : ZMod p) - Polynomial.X)).natDegree ≤ Zr.card := by
      refine (Polynomial.natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) (fun z _ => ?_)).trans (by simp)
      have : (Polynomial.C (z : ZMod p) - Polynomial.X : Polynomial (ZMod p)) =
          -(Polynomial.X - Polynomial.C (z : ZMod p)) := by ring
      rw [this, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
    have h3 : ((-Polynomial.X : Polynomial (ZMod p)) ^ (m + j)).natDegree ≤ m + j := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_neg, Polynomial.natDegree_X]; simp
    refine (Polynomial.natDegree_mul_le).trans ?_
    refine (add_le_add (Polynomial.natDegree_mul_le) le_rfl).trans ?_
    rw [h1, card_Nz hpp] at *
    omega
  have hzero := sum_zmod_eval_eq_zero (p := p) Hp hdegH
  have hcast : ∀ x : ZMod p, (ZMod.castHom (dvd_refl p) (ZMod p)) x = x := fun x => by simp
  simp only [hcast] at hzero
  rw [sum_zmod_range] at hzero
  simp only [hev] at hzero
  -- the sum over `Wr` equals the full sum, up to the constant `K`
  by_cases hWe : Wr = ∅
  · simp [hWe]
  obtain ⟨s0, hs0⟩ := Finset.nonempty_iff_ne_empty.2 hWe
  obtain ⟨hs0p, hs0t, hs0s⟩ := hW s0 hs0
  have hQ0 : Qm n p (s0 : ZMod p) ≠ 0 := by
    refine Qm_ne_zero _ ?_
    rw [sigZ_nat s0 hs0p]; unfold tieR at hs0t; omega
  have hrel : ∀ s ∈ Wr, wz n p s = (wz n p s0 / Qm n p (s0 : ZMod p)) * Qm n p (s : ZMod p) := by
    intro s hs
    obtain ⟨hsp, -, hss⟩ := hW s hs
    have := lemmaU_class h s0 s hs0p hsp (by rw [hs0s, hss])
    rw [wz_eq_wU s hsp, wz_eq_wU s0 hs0p]
    rw [div_mul_eq_mul_div, eq_div_iff hQ0]; exact this
  have hfull : ∑ s ∈ range p, Qm n p (s : ZMod p) * (∏ z ∈ Zr, ((z : ZMod p) - (s : ZMod p))) *
      (-(s : ZMod p)) ^ (m + j) = ∑ s ∈ Wr, Qm n p (s : ZMod p) *
        (∏ z ∈ Zr, ((z : ZMod p) - (s : ZMod p))) * (-(s : ZMod p)) ^ (m + j) := by
    symm
    refine Finset.sum_subset (fun s hs => Finset.mem_range.2 (hW s hs).1) (fun s hs hsW => ?_)
    have hsp := Finset.mem_range.1 hs
    by_cases ht : tieR n p s
    · have hZm : s ∈ Zr := (hcover s hsp ht).resolve_left hsW
      have : (∏ z ∈ Zr, ((z : ZMod p) - (s : ZMod p))) = 0 :=
        Finset.prod_eq_zero hZm (sub_self _)
      rw [this]; simp
    · have : Qm n p (s : ZMod p) = 0 := by
        apply Qm_zero_of_N
        rw [sigZ_nat s hsp]; exact ht
      rw [this]; simp
  rw [hfull] at hzero
  have : ∑ s ∈ Wr, wz n p s * ((∏ z ∈ Zr, ((-(s : ZMod p)) - (-(z : ZMod p)))) * (-(s : ZMod p)) ^ m) *
      (-(s : ZMod p)) ^ j = (wz n p s0 / Qm n p (s0 : ZMod p)) *
        ∑ s ∈ Wr, Qm n p (s : ZMod p) * (∏ z ∈ Zr, ((z : ZMod p) - (s : ZMod p))) *
          (-(s : ZMod p)) ^ (m + j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [hrel s hs]
    have : (∏ z ∈ Zr, ((-(s : ZMod p)) - (-(z : ZMod p)))) = ∏ z ∈ Zr, ((z : ZMod p) - (s : ZMod p)) :=
      Finset.prod_congr rfl (fun z _ => by ring)
    rw [this, pow_add]; ring
  rw [this, hzero, mul_zero]

end Hsum

end CatalanCore.Lai

-- part L1f
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Split

variable {n p : ℕ} [hp : Fact p.Prime]

open Classical in
/-- the two tie classes: `Z` the smaller, `W` the larger. -/
theorem tie_split (h : Rng n p) :
    ∃ σZ σW : ℕ, σZ ≠ σW ∧ (∀ s < p, tieR n p s ↔ (sig n p s = σZ ∨ sig n p s = σW)) ∧
      ((range p).filter (fun s => sig n p s = σZ)).card = tieZ n p ∧
      ((range p).filter (fun s => sig n p s = σW)).card = tieW n p := by
  have c0 := card_sig_zero h
  have c2 := card_sig_two h
  have c3 := card_sig_three h
  have c5 := card_sig_five h
  have hs : ∀ s, sig n p s = 0 ∨ sig n p s = 2 ∨ sig n p s = 3 ∨ sig n p s = 5 := by
    intro s; rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  by_cases hev : lam n p % 2 = 0
  · by_cases hAC : szA n p ≤ szC n p
    · refine ⟨0, 2, by omega, fun s _ => ?_, ?_, ?_⟩
      · unfold tieR; have := hs s; omega
      · rw [c0]; unfold tieZ; rw [if_pos hev]; omega
      · rw [c2]; unfold tieW; rw [if_pos hev]; omega
    · refine ⟨2, 0, by omega, fun s _ => ?_, ?_, ?_⟩
      · unfold tieR; have := hs s; omega
      · rw [c2]; unfold tieZ; rw [if_pos hev]; omega
      · rw [c0]; unfold tieW; rw [if_pos hev]; omega
  · by_cases hBD : szB n p ≤ szD n p
    · refine ⟨3, 5, by omega, fun s _ => ?_, ?_, ?_⟩
      · unfold tieR; have := hs s; omega
      · rw [c3]; unfold tieZ; rw [if_neg hev]; omega
      · rw [c5]; unfold tieW; rw [if_neg hev]; omega
    · refine ⟨5, 3, by omega, fun s _ => ?_, ?_, ?_⟩
      · unfold tieR; have := hs s; omega
      · rw [c5]; unfold tieZ; rw [if_neg hev]; omega
      · rw [c3]; unfold tieW; rw [if_neg hev]; omega

end Split

section Equiv

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the tie residues as a type. -/
abbrev SS (n p : ℕ) [Fact p.Prime] : Type := ↥(Sres n p)

/-- block sizes on the tie residues. -/
noncomputable def muS (n p : ℕ) [Fact p.Prime] (s : SS n p) : ℕ := mu n p s.1

lemma tieR_of_mem {T' : Finset (LIdx n p)} (hT' : ∀ x, x ∈ T' ↔ pot2 n p x % 2 = lam n p % 2)
    {r : Fin p} {i : Fin (mu n p r)} (hx : (Sum.inl ⟨r, i⟩ : LIdx n p) ∈ T') : tieR n p r.1 := by
  have := (hT' _).1 hx
  simp only [pot2] at this
  unfold tieR; omega

lemma mem_of_tieR {T' : Finset (LIdx n p)} (hT' : ∀ x, x ∈ T' ↔ pot2 n p x % 2 = lam n p % 2)
    (r : Fin p) (i : Fin (mu n p r)) (ht : tieR n p r.1) : (Sum.inl ⟨r, i⟩ : LIdx n p) ∈ T' := by
  rw [hT']
  simp only [pot2]
  unfold tieR at ht; omega

noncomputable def eI (T' : Finset (LIdx n p)) (hT' : ∀ x, x ∈ T' ↔ pot2 n p x % 2 = lam n p % 2) :
    NBIdx (SS n p) (muS n p) (dcnt n p) ≃ {x // x ∈ T'} where
  toFun a := match a with
    | Sum.inl ⟨s, i⟩ => ⟨Sum.inl ⟨⟨s.1, (mem_Sres.1 s.2).1⟩, i⟩,
        mem_of_tieR hT' _ _ (mem_Sres.1 s.2).2⟩
    | Sum.inr j => ⟨Sum.inr j, (hT' _).2 (by simp [pot2])⟩
  invFun x := match x with
    | ⟨Sum.inl ⟨r, i⟩, hx⟩ => Sum.inl ⟨⟨r.1, mem_Sres.2 ⟨r.2, tieR_of_mem hT' hx⟩⟩, i⟩
    | ⟨Sum.inr j, _⟩ => Sum.inr j
  left_inv a := by rcases a with ⟨s, i⟩ | j <;> rfl
  right_inv x := by rcases x with ⟨⟨r, i⟩ | j, hx⟩ <;> rfl

end Equiv

end CatalanCore.Lai

-- part L1g
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Main

variable {n p : ℕ} [hp : Fact p.Prime]

abbrev KK (p : ℕ) [Fact p.Prime] : Type := FractionRing (MvPolynomial (Fin 3) (ZMod p))

noncomputable def iotaK (p : ℕ) [Fact p.Prime] : ZMod p →+* KK p :=
  (algebraMap (MvPolynomial (Fin 3) (ZMod p)) (KK p)).comp MvPolynomial.C

noncomputable def X1K (p : ℕ) [Fact p.Prime] : KK p :=
  algebraMap (MvPolynomial (Fin 3) (ZMod p)) (KK p) (MvPolynomial.X 1)

lemma redMv_entry (h : Rng n p) (x y : LIdx n p) (hpar : pot2 n p x % 2 = pot2 n p y % 2)
    (Z : MvPolynomial (Fin 3) (LocRing p))
    (hZ : toQmv p Z = C ((p : ℚ) ^ (-((pot2 n p x + pot2 n p y) / 2))) * laiL n (fL n p x * fL n p y)) :
    redMv p Z = iotaK p (ent n p x y) * X1K p := by
  obtain ⟨q, hq, hr⟩ := red_entry h x y hpar Z hZ
  have hent : redQ p q = ent n p x y := by
    rw [redQ_apply, ← rzT_of_mem q.2, hq]
    unfold ent
    refine rzT_sum _ _ (fun k hk => ?_)
    obtain ⟨hk1, hl, -⟩ := Finset.mem_filter.1 hk
    have hk6 : k ≤ 6 * n := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hk1
    have hkp : k / p < p := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by have := h.h8; omega)
    exact qTerm_mem h x y k hk6 hkp
  rw [hr, hent]
  simp [iotaK, X1K, map_mul]

lemma sum_SS_filter {M : Type*} [AddCommMonoid M] (F : ℕ → M) (P : ℕ → Prop) [DecidablePred P] :
    ∑ s ∈ (Finset.univ : Finset (SS n p)).filter (fun s => P s.1), F s.1 =
      ∑ s ∈ (Sres n p).filter P, F s := by
  rw [Finset.sum_filter, Finset.sum_coe_sort (Sres n p) (fun s => if P s then F s else 0),
    ← Finset.sum_filter]

lemma prod_SS_filter {M : Type*} [CommMonoid M] (F : ℕ → M) (P : ℕ → Prop) [DecidablePred P] :
    ∏ s ∈ (Finset.univ : Finset (SS n p)).filter (fun s => P s.1), F s.1 =
      ∏ s ∈ (Sres n p).filter P, F s := by
  rw [Finset.prod_filter, Finset.prod_coe_sort (Sres n p) (fun s => if P s then F s else 1),
    ← Finset.prod_filter]

lemma card_SS_filter (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ : Finset (SS n p)).filter (fun s => P s.1)).card = ((Sres n p).filter P).card := by
  have := sum_SS_filter (n := n) (p := p) (fun _ => (1 : ℕ)) P
  simpa using this

end Main

end CatalanCore.Lai

-- part L1h
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section Entry

variable {n p : ℕ} [hp : Fact p.Prime]

/-- the NB matrix of the tie block over `K = Frac 𝔽_p[a, b, X]`. -/
noncomputable def NBK (n p : ℕ) [Fact p.Prime] :
    Matrix (NBIdx (SS n p) (muS n p) (dcnt n p)) (NBIdx (SS n p) (muS n p) (dcnt n p)) (KK p) :=
  NB (muS n p) (dcnt n p) (fun s => X1K p * iotaK p (wz n p s.1))
    (fun s => iotaK p (-((s.1 : ℕ) : ZMod p))) (fun s m => iotaK p (Phi n p s.1 m))

lemma entry_NB (h : Rng n p) (T' : Finset (LIdx n p))
    (hT' : ∀ x, x ∈ T' ↔ pot2 n p x % 2 = lam n p % 2)
    (Z : Matrix T' T' (MvPolynomial (Fin 3) (LocRing p)))
    (hZ : ∀ x y : T', toQmv p (Z x y) =
      C ((p : ℚ) ^ (-((pot2 n p x + pot2 n p y) / 2))) * laiL n (fL n p x * fL n p y))
    (a b : NBIdx (SS n p) (muS n p) (dcnt n p)) :
    (Z.map (redMv p)) (eI T' hT' a) (eI T' hT' b) = NBK n p a b := by
  rw [Matrix.map_apply, redMv_entry h _ _
    (by rw [(hT' _).1 (eI T' hT' a).2, (hT' _).1 (eI T' hT' b).2]) _ (hZ _ _)]
  rcases a with ⟨s, i⟩ | j <;> rcases b with ⟨s', i'⟩ | j'
  · by_cases hss : s = s'
    · subst hss
      simp only [eI, Equiv.coe_fn_mk, NBK, NB, Matrix.of_apply, if_true]
      refine (congrArg (fun z => iotaK p z * X1K p)
        (ent_ee_same h ⟨s.1, (mem_Sres.1 s.2).1⟩ i i')).trans ?_
      simp only [map_mul, Fin.val_mk]; ring
    · simp only [eI, Equiv.coe_fn_mk, NBK, NB, Matrix.of_apply, hss, if_false]
      refine (congrArg (fun z => iotaK p z * X1K p)
        (ent_ee_ne h ⟨s.1, (mem_Sres.1 s.2).1⟩ ⟨s'.1, (mem_Sres.1 s'.2).1⟩
          (fun e => hss (Subtype.ext (congrArg Fin.val e))) i i')).trans ?_
      simp
  · simp only [eI, Equiv.coe_fn_mk, NBK, NB, Matrix.of_apply]
    refine (congrArg (fun z => iotaK p z * X1K p)
        (ent_eg h ⟨s.1, (mem_Sres.1 s.2).1⟩ (mem_Sres.1 s.2).2 i j')).trans ?_
    simp only [map_mul, map_pow, Fin.val_mk, muS]; ring
  · simp only [eI, Equiv.coe_fn_mk, NBK, NB, Matrix.of_apply]
    refine (congrArg (fun z => iotaK p z * X1K p)
        (ent_ge h ⟨s'.1, (mem_Sres.1 s'.2).1⟩ (mem_Sres.1 s'.2).2 i' j)).trans ?_
    simp only [map_mul, map_pow, Fin.val_mk, muS]; ring
  · simp only [eI, Equiv.coe_fn_mk, NBK, NB, Matrix.of_apply]
    rw [ent_gg h, map_sum, Finset.sum_mul, ← Finset.sum_coe_sort (Sres n p)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp only [map_mul, map_pow, muS]; ring

end Entry

end CatalanCore.Lai

-- part L1i
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section TieRank

variable {n p : ℕ} [hp : Fact p.Prime]

lemma mu_tie (h : Rng n p) (t : ℕ) (ht : t < p) (hti : tieR n p t) :
    2 * (mu n p t : ℤ) + sig n p t = lam n p + 4 := by
  have := mu_sig h t ht
  rw [if_pos hti] at this
  omega

open Classical in
/-- **The corank of the tie block** (Lemma K, assembled): any integral lift of the scaled tie Gram block
has reduced rank at most `|T| - x₁`. -/
theorem tie_rank (h : Rng n p) (T' : Finset (LIdx n p))
    (hT' : ∀ x, x ∈ T' ↔ pot2 n p x % 2 = lam n p % 2)
    (Z : Matrix T' T' (MvPolynomial (Fin 3) (LocRing p)))
    (hZ : ∀ x y : T', toQmv p (Z x y) =
      C ((p : ℚ) ^ (-((pot2 n p x + pot2 n p y) / 2))) * laiL n (fL n p x * fL n p y)) :
    (Z.map (redMv p)).rank + (xone n p).toNat ≤ T'.card := by
  have hpp := hp.out.pos
  have hcardT : Fintype.card {x // x ∈ T'} = T'.card := Fintype.card_coe T'
  by_cases hx0 : (xone n p).toNat = 0
  · rw [hx0, add_zero, ← hcardT]; exact Matrix.rank_le_card_width _
  have hx1 : 0 < xone n p := by omega
  obtain ⟨σZ, σW, hne, hiff, hcZ, hcW⟩ := tie_split h
  have hsum_tie := tie_sum h
  -- the class finsets
  set Wr : Finset ℕ := (Sres n p).filter (fun s => sig n p s = σW) with hWr
  set Zr : Finset ℕ := (Sres n p).filter (fun s => sig n p s = σZ) with hZr
  set Wf : Finset (SS n p) := Finset.univ.filter (fun s => sig n p s.1 = σW) with hWf
  set Zf : Finset (SS n p) := Finset.univ.filter (fun s => sig n p s.1 = σZ) with hZf
  have hSW : Wr = (range p).filter (fun s => sig n p s = σW) := by
    ext s
    simp only [hWr, Finset.mem_filter, mem_Sres, Finset.mem_range]
    constructor
    · rintro ⟨⟨a, -⟩, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, (hiff s a).2 (Or.inr b)⟩, b⟩
  have hSZ : Zr = (range p).filter (fun s => sig n p s = σZ) := by
    ext s
    simp only [hZr, Finset.mem_filter, mem_Sres, Finset.mem_range]
    constructor
    · rintro ⟨⟨a, -⟩, b⟩; exact ⟨a, b⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, (hiff s a).2 (Or.inl b)⟩, b⟩
  have hcW' : Wr.card = tieW n p := by rw [hSW]; exact hcW
  have hcZ' : Zr.card = tieZ n p := by rw [hSZ]; exact hcZ
  have hcWf : Wf.card = tieW n p := by
    rw [← hcW']; exact card_SS_filter (n := n) (p := p) (fun s => sig n p s = σW)
  have hcZf : Zf.card = tieZ n p := by
    rw [← hcZ']; exact card_SS_filter (n := n) (p := p) (fun s => sig n p s = σZ)
  -- facts on x1
  have hxa : (xone n p).toNat + tieZ n p ≤ dcnt n p := by unfold xone at hx1 ⊢; omega
  have hxb : (xone n p).toNat + dcnt n p ≤ tieW n p := by unfold xone at hx1 ⊢; omega
  -- the NB corank
  have hWne : Wf.Nonempty := by
    rw [← Finset.card_pos, hcWf]; omega
  obtain ⟨s0, hs0⟩ := hWne
  have hsigW : ∀ s : SS n p, s ∈ Wf → sig n p s.1 = σW := fun s hs => (Finset.mem_filter.1 hs).2
  have hWZ : Disjoint Wf Zf := by
    rw [Finset.disjoint_left]
    intro s h1 h2
    exact hne ((Finset.mem_filter.1 h2).2.symm.trans (Finset.mem_filter.1 h1).2)
  have hcov : Wf ∪ Zf = Finset.univ := by
    ext s
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, iff_true]
    have := (hiff s.1 (mem_Sres.1 s.2).1).1 (mem_Sres.1 s.2).2
    rcases this with a | a
    · exact Or.inr a
    · exact Or.inl a
  have hμ : ∀ s ∈ Wf, muS n p s = muS n p s0 := by
    intro s hs
    have e1 := mu_tie h s.1 (mem_Sres.1 s.2).1 (mem_Sres.1 s.2).2
    have e2 := mu_tie h s0.1 (mem_Sres.1 s0.2).1 (mem_Sres.1 s0.2).2
    have := hsigW s hs
    have := hsigW s0 hs0
    unfold muS; omega
  have hΦ : ∀ s ∈ Wf, (fun m => iotaK p (Phi n p s.1 m)) = (fun m => iotaK p (Phi n p s0.1 m)) := by
    intro s hs
    funext m
    rw [Phi_class s.1 s0.1 (by rw [hsigW s hs, hsigW s0 hs0]) m]
  have hcardN : ((range p).filter (fun s => ¬ tieR n p s)).card + tieZ n p + tieW n p = p := by
    have h1 := Finset.card_filter_add_card_filter_not (s := range p) (fun s => tieR n p s)
    have h2 : (Sres n p).card = tieZ n p + tieW n p := by
      have : Sres n p = Zr ∪ Wr := by
        ext s
        simp only [hZr, hWr, Finset.mem_union, Finset.mem_filter]
        constructor
        · intro hs; have := (hiff s (mem_Sres.1 hs).1).1 (mem_Sres.1 hs).2; tauto
        · rintro (⟨a, -⟩ | ⟨a, -⟩) <;> exact a
      rw [this, Finset.card_union_of_disjoint, hcZ', hcW']
      rw [Finset.disjoint_left]
      intro s h1 h2
      exact hne ((Finset.mem_filter.1 h1).2.symm.trans (Finset.mem_filter.1 h2).2)
    have h3 : (Sres n p).card = ((range p).filter (fun s => tieR n p s)).card := rfl
    simp only [Finset.card_range] at h1
    omega
  have hsum : ∀ m < (xone n p).toNat, ∀ j < dcnt n p,
      ∑ s ∈ Wf, (X1K p * iotaK p (wz n p s.1)) *
        ((∏ z ∈ Zf, (iotaK p (-((s.1 : ℕ) : ZMod p)) - iotaK p (-((z.1 : ℕ) : ZMod p)))) *
          iotaK p (-((s.1 : ℕ) : ZMod p)) ^ m) * iotaK p (-((s.1 : ℕ) : ZMod p)) ^ j = 0 := by
    intro m hm j hj
    have hz : ∑ s ∈ Wf, wz n p s.1 *
        ((∏ z ∈ Zf, ((-((s.1 : ℕ) : ZMod p)) - (-((z.1 : ℕ) : ZMod p)))) *
          (-((s.1 : ℕ) : ZMod p)) ^ m) * (-((s.1 : ℕ) : ZMod p)) ^ j = 0 := by
      have e1 : ∀ s : SS n p, ∏ z ∈ Zf, ((-((s.1 : ℕ) : ZMod p)) - (-((z.1 : ℕ) : ZMod p))) =
          ∏ z ∈ Zr, ((-((s.1 : ℕ) : ZMod p)) - (-((z : ℕ) : ZMod p))) := fun s =>
        prod_SS_filter (n := n) (p := p) (fun z => (-((s.1 : ℕ) : ZMod p)) - (-((z : ℕ) : ZMod p)))
          (fun z => sig n p z = σZ)
      simp only [e1]
      have e2 := sum_SS_filter (n := n) (p := p)
        (fun s => wz n p s * ((∏ z ∈ Zr, ((-((s : ℕ) : ZMod p)) - (-((z : ℕ) : ZMod p)))) *
          (-((s : ℕ) : ZMod p)) ^ m) * (-((s : ℕ) : ZMod p)) ^ j) (fun s => sig n p s = σW)
      refine e2.trans ?_
      refine hsum_core h σW Wr Zr (fun s hs => ?_) (fun z hz => ?_) ?_ (fun s hs ht => ?_) m j ?_
      · obtain ⟨a, b⟩ := Finset.mem_filter.1 hs
        exact ⟨(mem_Sres.1 a).1, (mem_Sres.1 a).2, b⟩
      · obtain ⟨a, b⟩ := Finset.mem_filter.1 hz
        exact ⟨(mem_Sres.1 a).1, (mem_Sres.1 a).2⟩
      · rw [Finset.disjoint_left]
        intro s h1 h2
        exact hne ((Finset.mem_filter.1 h2).2.symm.trans (Finset.mem_filter.1 h1).2)
      · have := (hiff s hs).1 ht
        rcases this with a | a
        · exact Or.inr (Finset.mem_filter.2 ⟨mem_Sres.2 ⟨hs, ht⟩, a⟩)
        · exact Or.inl (Finset.mem_filter.2 ⟨mem_Sres.2 ⟨hs, ht⟩, a⟩)
      · rw [hcZ']; omega
    have := congrArg (fun z : ZMod p => X1K p * iotaK p z) hz
    simp only [map_zero, mul_zero] at this
    rw [← this, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [map_mul, map_prod, map_sub, map_pow]
    ring
  have hxlt : Zf.card + (xone n p).toNat ≤ dcnt n p := by omega
  have hNB := NB_corank_spec (L := KK p) (S := SS n p) Wf Zf hWZ hcov (muS n p) (muS n p s0)
    (dcnt n p) (xone n p).toNat hμ hxlt (fun s => X1K p * iotaK p (wz n p s.1))
    (fun s => iotaK p (-((s.1 : ℕ) : ZMod p))) (fun s m => iotaK p (Phi n p s.1 m))
    (fun m => iotaK p (Phi n p s0.1 m)) hΦ hsum
  have hrk : (Z.map (redMv p)).rank = (NBK n p).rank := by
    rw [← Matrix.rank_submatrix (Z.map (redMv p)) (eI T' hT') (eI T' hT')]
    congr 1
    ext a b
    exact entry_NB h T' hT' Z hZ a b
  have hcard : Fintype.card (NBIdx (SS n p) (muS n p) (dcnt n p)) = T'.card := by
    rw [← hcardT]; exact Fintype.card_congr (eI T' hT')
  rw [hrk, ← hcard]
  exact hNB

end TieRank

end CatalanCore.Lai

-- part L1j
open Finset CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Content MvPolynomial
open scoped Nat

namespace CatalanCore.Lai

section L1

variable {n p : ℕ} [hp : Fact p.Prime]

/-- **The Gram determinant of the L1 basis with the first-level gain.** -/
theorem gram_det_gain (h : Rng n p) :
    GV p (∑ x, pot2 n p x + (xone n p).toNat)
      (Matrix.of fun x y : LIdx n p => laiL n (fL n p x * fL n p y)).det := by
  classical
  set M : Matrix (LIdx n p) (LIdx n p) MP := Matrix.of fun x y => laiL n (fL n p x * fL n p y) with hMdef
  have hM : ∀ i j, GV p (kL n p i + kL n p j + (if i ∈ BL n p ∨ j ∈ BL n p then 1 else 0)) (M i j) :=
    fun i j => entry_ge h i j
  have hpot : ∀ x, pot2 n p x = 2 * kL n p x + (if x ∈ BL n p then 1 else 0) := pot2_eq
  have hmod : ∀ x, x ∈ BL n p ↔ pot2 n p x % 2 = 1 := fun x => by
    unfold BL; simp [Finset.mem_filter]
  rcases Int.emod_two_eq_zero_or_one (lam n p) with hl | hl
  · -- even λ: the tie group is the complement of `BL`
    set A : Finset (LIdx n p) := Finset.univ \ BL n p with hA
    have hTA : ∀ x, x ∈ A ↔ pot2 n p x % 2 = lam n p % 2 := fun x => by
      rw [hA, Finset.mem_sdiff, hmod]; simp only [Finset.mem_univ, true_and]; omega
    have hex : ∀ i j : A, ∃ g : MvPolynomial (Fin 3) (LocRing p),
        toQmv p g = MvPolynomial.C ((p : ℚ) ^ (-((pot2 n p i + pot2 n p j) / 2))) * M i j := by
      intro i j
      have := hM i j
      have hi : (i : LIdx n p) ∉ BL n p := (Finset.mem_sdiff.1 i.2).2
      have hj : (j : LIdx n p) ∉ BL n p := (Finset.mem_sdiff.1 j.2).2
      have hc : (if (i : LIdx n p) ∈ BL n p ∨ (j : LIdx n p) ∈ BL n p then (1 : ℤ) else 0) = 0 := by
        simp [hi, hj]
      rw [hc, add_zero] at this
      have e : (pot2 n p i + pot2 n p j) / 2 = kL n p i + kL n p j := by
        have := hpot i; have := hpot j
        simp only [hi, hj, if_false] at *
        omega
      rw [e]
      exact GV.exists_lift this
    choose ZA hZA using hex
    set Z : Matrix A A (MvPolynomial (Fin 3) (LocRing p)) := Matrix.of (fun i j => ZA i j) with hZ
    have hrk := tie_rank h A hTA Z (fun x y => hZA x y)
    have key := GV.det_halfInt_mirror (p := p) M (kL n p) (BL n p) hM Z
      (fun i j => by
        have := hZA i j
        have hi : (i : LIdx n p) ∉ BL n p := (Finset.mem_sdiff.1 i.2).2
        have hj : (j : LIdx n p) ∉ BL n p := (Finset.mem_sdiff.1 j.2).2
        have e : (pot2 n p i + pot2 n p j) / 2 = kL n p i + kL n p j := by
          have := hpot i; have := hpot j
          simp only [hi, hj, if_false] at *
          omega
        rw [e] at this; exact this)
      (xone n p).toNat (by simpa [hA] using hrk)
    rw [sum_pot2]
    simpa using key
  · -- odd λ: the tie group is `BL`
    have hTB : ∀ x, x ∈ BL n p ↔ pot2 n p x % 2 = lam n p % 2 := fun x => by rw [hmod]; omega
    have hex : ∀ i j : BL n p, ∃ g : MvPolynomial (Fin 3) (LocRing p),
        toQmv p g = MvPolynomial.C ((p : ℚ) ^ (-((pot2 n p i + pot2 n p j) / 2))) * M i j := by
      intro i j
      have := hM i j
      have hc : (if (i : LIdx n p) ∈ BL n p ∨ (j : LIdx n p) ∈ BL n p then (1 : ℤ) else 0) = 1 := by
        simp [i.2]
      rw [hc] at this
      have e : (pot2 n p i + pot2 n p j) / 2 = kL n p i + kL n p j + 1 := by
        have := hpot i; have := hpot j
        simp only [i.2, j.2, if_true] at *
        omega
      rw [e]
      exact GV.exists_lift this
    choose ZB hZB using hex
    set Z : Matrix (BL n p) (BL n p) (MvPolynomial (Fin 3) (LocRing p)) := Matrix.of (fun i j => ZB i j) with hZ
    have hrk := tie_rank h (BL n p) hTB Z (fun x y => hZB x y)
    have key := GV.det_halfInt (p := p) M (kL n p) (BL n p) hM Z
      (fun i j => by
        have := hZB i j
        have e : (pot2 n p i + pot2 n p j) / 2 = kL n p i + kL n p j + 1 := by
          have := hpot i; have := hpot j
          simp only [i.2, j.2, if_true] at *
          omega
        rw [e] at this; exact this)
      (xone n p).toNat hrk
    rw [sum_pot2]
    simpa using key

/-- **Theorem L1** (`N9-LAI-CONTENT-EXACT`): for every prime `√(8n) < p < 3n`,
`v_p(J_n) ≥ LaiExact(n, p) + x₁`, with `x₁ = max(0, min(d - |Z|, |W| - d))`. -/
theorem lai_L1 (h : Rng n p) :
    GV p (∑ x, pot2 n p x - nuP n p + (xone n p).toNat) (laiJ n) := by
  have hN := hsum_mu h
  have e : LIdx n p ≃ Fin (3 * n) := Fintype.equivFinOfCardEq (card_LIdx h)
  have := GV_laiJ_of_crt (p := p) n (aL p) aL_inj (fun r : Fin p => mu n p r) (dcnt n p) hN e _
    (gram_det_gain h)
  have e2 : ∑ x, pot2 n p x + ((xone n p).toNat : ℤ) - nuP n p =
      ∑ x, pot2 n p x - nuP n p + (xone n p).toNat := by ring
  rw [e2] at this
  exact this

end L1

end CatalanCore.Lai

#print axioms CatalanCore.Lai.lai_L1
#print axioms CatalanCore.Lai.tie_rank
#print axioms CatalanCore.Lai.hsum_core
#print axioms CatalanCore.Lai.entry_NB
