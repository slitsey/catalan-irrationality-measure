module

public import CatalanCore.Star.Leonard.DSGood
public import CatalanCore.Star.Leonard.HD2

/-!
# The induction on `n` (base case, assembly)

* `uu_one`: base case `n = 1`, `uu m 1 S θ` is a Cauchy determinant (`cauFac`);
* `uu_one_good`: it is good with bound `S + 3m`;
* `uu_good`: assuming the K-step transfer `KSH`, `uu m n S` is good for all `n ≤ S`.
-/

@[expose] public section

open Finset Matrix CatalanCore.ThmA

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

theorem uu_one (m S : ℕ) (θ : ℚ) (hθ : Gen θ)
    (hΔ : IsUnit ((Wb (m + 1) θ (bX m (S : ℤ)))ᵀ * Wb (m + 1) θ (bY m (S : ℤ))).det) :
    uu m 1 S θ = cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun _ : Fin 1 => ((S : ℤ) : ℚ)) : Fin (m + 1) → ℚ) := by
  obtain ⟨-, hPc⟩ := projB_props m 1 S θ hΔ
  obtain ⟨a, ha⟩ := hPc (wcol (m + 1) θ (S : ℤ))
  unfold uu CatalanCore.bkdet
  have hK : CatalanCore.krylovE (Atil m 1 S θ) (projB (m + 1) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ
      wcol (m + 1) θ (S : ℤ)) =
      (Matrix.of fun i (_ : Fin 1) => wcol (m + 1) θ (S : ℤ) i) * (1 : Matrix (Fin 1) (Fin 1) ℚ) +
        Wb (m + 1) θ (bY m (S : ℤ)) * (Matrix.of fun r (_ : Fin 1) => -(a r)) := by
    ext i k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    have := congrFun ha i
    simp only [CatalanCore.krylovE, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.mul_one, Fin.val_zero, pow_zero, Matrix.one_mulVec]
    rw [this]
    simp [Matrix.mulVec, dotProduct, sub_eq_add_neg, mul_neg, Finset.sum_neg_distrib]
  rw [hK, CatalanCore.det_bmat_comb, Matrix.det_one, one_mul]
  have hne : ∀ (a : Fin (m + 1)) (j : Fin (m + 1)),
      θ + ((a : ℕ) : ℚ) + (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
        (fun _ : Fin 1 => ((S : ℤ) : ℚ)) : Fin (m + 1) → ℚ) j ≠ 0 := by
    intro a j
    refine Fin.addCases (fun i => ?_) (fun j => ?_) j
    · simp only [Fin.addCases_left]; exact gen_add hθ a _
    · simp only [Fin.addCases_right]; exact gen_add hθ a _
  exact CatalanCore.bmat_cauchy_det θ _ _ hne

/-- the base case is good with bound `S + 3m` -/
theorem uu_one_good (m S : ℕ) (hm : 1 ≤ m) (hS : 1 ≤ S) (hl : S + 3 * m + 1 ≤ ℓ) :
    GoodF ℓ (S + 3 * m) (uu m 1 S) := by
  have hc : LU ℓ (cnum (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : ℚ))
      (fun _ : Fin 1 => ((S : ℤ) : ℚ)) : Fin (m + 1) → ℚ)) := by
    refine LU_cnum_add (fun i : Fin m => bY m (S : ℤ) i) (fun _ : Fin 1 => (S : ℤ))
      (2 * m + 1) (by omega) (by omega) (S : ℤ) ((S : ℤ) + 2 * m) (fun i => ?_) (fun j => ?_)
      (by omega) (bY_inj m _) (fun i j h => Fin.ext (by omega)) (fun i j => ?_)
    · have := bY_bounds m (S : ℤ) i; omega
    · omega
    · have := bY_bounds m (S : ℤ) i; omega
  have hP1 : GoodF ℓ (S + 3 * m) (fun θ => ∏ i : Fin (m + 1), ∏ j : Fin m,
      (θ + ((i : ℕ) : ℚ) + ((bY m (S : ℤ) j : ℤ) : ℚ))) := by
    refine GoodF.prod _ _ fun i _ => GoodF.prod _ _ fun j _ => ?_
    have hi := i.2; have hj := j.2
    have := GoodF.lin1 (ℓ := ℓ) ((i : ℕ) + S + 2 * (j : ℕ)) (B := S + 3 * m) (by omega)
    refine this.congr fun θ h0 hg => ?_
    simp only [bY]; push_cast; ring
  have hP2 : GoodF ℓ (S + 3 * m) (fun θ => ∏ i : Fin (m + 1), ∏ j : Fin 1,
      (θ + ((i : ℕ) : ℚ) + ((S : ℤ) : ℚ))) := by
    refine GoodF.prod _ _ fun i _ => GoodF.prod _ _ fun j _ => ?_
    have hi := i.2
    have := GoodF.lin1 (ℓ := ℓ) ((i : ℕ) + S - 1) (B := S + 3 * m) (by omega)
    refine this.congr fun θ h0 hg => ?_
    have e : (i : ℕ) + S - 1 + 1 = (i : ℕ) + S := by omega
    rw [e]; push_cast; ring
  refine ((GoodF.const (B := S + 3 * m) hc).div (hP1.mul hP2)).congr fun θ h0 hg => ?_
  have hΔ : IsUnit ((Wb (m + 1) θ (bX m (S : ℤ)))ᵀ * Wb (m + 1) θ (bY m (S : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + 1) m S (by omega) θ h0)
  rw [uu_one m S θ hg hΔ, cauFac_split]

/-- the K-step transfer (to be proved): good at `(n', n'+1)` gives good at `(n'+1, n'+1)` -/
def KSTransfer (ℓ m : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ n' : ℕ, 1 ≤ n' → n' + 1 + (n' + 1) + 3 * m ≤ ℓ →
    GoodF ℓ ((n' + 1) + n' + 3 * m - 1) (uu m n' (n' + 1)) →
    GoodF ℓ ((n' + 1) + (n' + 1) + 3 * m - 1) (uu m (n' + 1) (n' + 1))

/-- the diagonal chain: from `S = n` to all `S ≥ n` -/
theorem uu_good_chain (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h0 : GoodF ℓ (n + n + 3 * m - 1) (uu m n n)) :
    ∀ S, n ≤ S → S + n + 3 * m ≤ ℓ → GoodF ℓ (S + n + 3 * m - 1) (uu m n S) := by
  intro S hS
  induction S, hS using Nat.le_induction with
  | base => intro _; exact h0
  | succ S hS ih =>
    intro hl
    have h1 := ih (by omega)
    have h2 := uu_good_succ m n S _ hm hn hS (by omega) h1
    exact h2.mono (by omega)

theorem uu_good (m : ℕ) (hm : 1 ≤ m) (KS : KSTransfer ℓ m) :
    ∀ n, 1 ≤ n → ∀ S, n ≤ S → S + n + 3 * m ≤ ℓ → GoodF ℓ (S + n + 3 * m - 1) (uu m n S) := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _ S hS hl
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      have := uu_one_good (ℓ := ℓ) m S hm (by omega) (by omega)
      exact this.mono (by omega)
    · have h1 := ih hn (n + 1) (by omega) (by omega)
      have h2 := KS n hn (by omega) h1
      exact uu_good_chain m (n + 1) hm (by omega) h2 S hS hl

/-- `C_ν` is an `ℓ`-unit -/
theorem Cnu_LU (m n S : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : n ≤ S) (hl : S + n + 2 * m + 1 ≤ ℓ) :
    LU ℓ (Cnu (F := ℚ) m n S) := by
  set L := S + n + 2 * m with hLdef
  have hL : L < ℓ := by omega
  have hX : LU ℓ (piB (bX m (S : ℤ)) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bX]; omega)
  have hY : LU ℓ (piB (bY m (S : ℤ)) (S : ℚ)) := LU_piB m S _ (fun i => by
    have := i.2; simp only [bY]; omega)
  have hP : LU ℓ (∏ j : Fin n, piB (bY m (S : ℤ)) (xv n j : ℚ)) := by
    refine LU.prod _ _ fun j _ => ?_
    have hj := j.2
    have := LU_piB (ℓ := ℓ) m (((j : ℕ) + 1 : ℕ)) (bY m (S : ℤ)) (fun i => by
      have := i.2; simp only [bY]; push_cast; omega)
    simpa [xv] using this
  have hV : LU ℓ (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (xv n j - xv n i : ℚ)) := by
    refine LU.prod _ _ fun i _ => LU.prod _ _ fun j hj => ?_
    have hlt0 : i < j := Finset.mem_Ioi.1 hj
    have hlt : (i : ℕ) < j := hlt0
    have := LU_int' (ℓ := ℓ) (z := ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) hL (by omega)
      (by have := j.2; omega)
    simpa [xv] using this
  have hC : LU ℓ (cnum (vshift (F := ℚ) m n S)) := by
    have := LU_cnum_add (ℓ := ℓ) (fun i : Fin m => bY m (S : ℤ) i)
      (fun j : Fin n => (((j : ℕ) + 1 : ℕ) : ℤ)) L hL (by omega) 1 ((S : ℤ) + 2 * m)
      (fun i => ?_) (fun j => ?_) (by omega) (bY_inj m _)
      (fun i j h => Fin.ext (by simp at h; omega)) (fun i j => ?_)
    · exact this
    · have := bY_bounds m (S : ℤ) i; omega
    · have := j.2; omega
    · have := bY_bounds m (S : ℤ) i; have := j.2; push_cast; omega
  unfold Cnu
  exact (((hX.div hY).pow n).mul (hP.mul hV)).div hC

theorem kgen_good (m n S : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hS : n ≤ S) (hl : S + n + 3 * m ≤ ℓ)
    (huu : GoodF ℓ (S + n + 3 * m - 1) (uu m n S)) :
    GoodF ℓ (S + n + 3 * m - 1) (kgen (m + n) m S) := by
  have hYD : GoodF ℓ (S + n + 3 * m - 1) (fun θ => YD m n S θ) := by
    refine GoodF.prod _ _ fun a _ => GoodF.prod _ _ fun i _ => ?_
    have := GoodF.lin1 (ℓ := ℓ) ((a : ℕ) + S + 2 * (i : ℕ)) (B := S + n + 3 * m - 1)
      (by have := a.2; have := i.2; omega)
    refine this.congr fun θ h0 hg => ?_
    simp only [bY]; push_cast; ring
  refine (((GoodF.const (B := S + n + 3 * m - 1) (Cnu_LU m n S hm hn hS (by omega))).mul hYD).mul
    huu).congr fun θ h0 hg => ?_
  have hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det :=
    isUnit_iff_ne_zero.2 (Delta_ne_pos (m + n) m S (by omega) θ h0)
  rw [kgen_eq_nu_mul_u m n S θ hg hS (by omega) hΔ, nu_form m n S θ hg hS]
  rfl

end CatalanCore.Star.Leonard
