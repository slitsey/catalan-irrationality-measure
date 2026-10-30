module

public import CatalanCore.Star.Defs
public import CatalanCore.Basic.ZModGood
public import CatalanCore.Star.Leonard.DeltaUnit

/-!
# Reduction of `kgenCore` at `θ = 0` modulo `ℓ`

`GoodM A B`: the rational matrix `A` is `ℓ`-integral and reduces entrywise to `B`.  Closed under
products, sums, powers, `vecMul`, determinants, adjugates and inverses (when the determinant is a
unit).  Consequence: `kgenCore K m 0 J S bx by'` over `ℚ` is `ℓ`-integral and reduces to the same
expression over `ZMod ℓ`, provided all node/column sums `a + j` are in `[1, ℓ-1]` and
`det(W_Xᵀ W_Y)` is an `ℓ`-unit.
-/

@[expose] public section

open Finset Matrix CatalanCore

namespace CatalanCore.Star.Leonard

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- entrywise reduction -/
def GoodM {ι κ : Type*} (A : Matrix ι κ ℚ) (B : Matrix ι κ (ZMod ℓ)) : Prop :=
  ∀ i j, Good ℓ (A i j) (B i j)

/-- entrywise reduction of vectors -/
def GoodV {ι : Type*} (a : ι → ℚ) (b : ι → ZMod ℓ) : Prop := ∀ i, Good ℓ (a i) (b i)

section
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] [DecidableEq ι] [DecidableEq κ]

lemma GoodM.mul {A : Matrix ι κ ℚ} {A' : Matrix ι κ (ZMod ℓ)} {B : Matrix κ μ ℚ}
    {B' : Matrix κ μ (ZMod ℓ)} (hA : GoodM A A') (hB : GoodM B B') : GoodM (A * B) (A' * B') :=
  fun i j => by
    simp only [Matrix.mul_apply]
    exact Good.sum _ _ _ fun k _ => (hA i k).mul (hB k j)

lemma GoodM.add {A B : Matrix ι κ ℚ} {A' B' : Matrix ι κ (ZMod ℓ)} (hA : GoodM A A')
    (hB : GoodM B B') : GoodM (A + B) (A' + B') := fun i j => (hA i j).add (hB i j)

lemma GoodM.sub {A B : Matrix ι κ ℚ} {A' B' : Matrix ι κ (ZMod ℓ)} (hA : GoodM A A')
    (hB : GoodM B B') : GoodM (A - B) (A' - B') := fun i j => (hA i j).sub (hB i j)

lemma GoodM.one : GoodM (1 : Matrix ι ι ℚ) (1 : Matrix ι ι (ZMod ℓ)) := fun i j => by
  by_cases h : i = j
  · subst h; simpa using (Good.one (ℓ := ℓ))
  · simpa [Matrix.one_apply, h] using (Good.zero (ℓ := ℓ))

lemma GoodM.transpose {A : Matrix ι κ ℚ} {A' : Matrix ι κ (ZMod ℓ)} (hA : GoodM A A') :
    GoodM Aᵀ A'ᵀ := fun i j => hA j i

lemma GoodM.pow {A : Matrix ι ι ℚ} {A' : Matrix ι ι (ZMod ℓ)} (hA : GoodM A A') (n : ℕ) :
    GoodM (A ^ n) (A' ^ n) := by
  induction n with
  | zero => simpa using (GoodM.one (ℓ := ℓ) (ι := ι))
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hA

lemma GoodM.vecMul {a : ι → ℚ} {a' : ι → ZMod ℓ} {B : Matrix ι κ ℚ} {B' : Matrix ι κ (ZMod ℓ)}
    (ha : GoodV a a') (hB : GoodM B B') : GoodV (a ᵥ* B) (a' ᵥ* B') := fun j => by
  simp only [Matrix.vecMul, dotProduct]
  exact Good.sum _ _ _ fun i _ => (ha i).mul (hB i j)

lemma GoodM.det {A : Matrix ι ι ℚ} {A' : Matrix ι ι (ZMod ℓ)} (hA : GoodM A A') :
    Good ℓ A.det A'.det := red_det A A' hA

lemma GoodM.adjugate {A : Matrix ι ι ℚ} {A' : Matrix ι ι (ZMod ℓ)} (hA : GoodM A A') :
    GoodM A.adjugate A'.adjugate := fun i j => by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  refine red_det _ _ fun a b => ?_
  by_cases h : a = j
  · subst h
    simp only [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst hb; simpa using (Good.one (ℓ := ℓ))
    · simpa [Pi.single_apply, hb] using (Good.zero (ℓ := ℓ))
  · simpa [Matrix.updateRow_ne h] using hA a b

lemma GoodM.inv {A : Matrix ι ι ℚ} {A' : Matrix ι ι (ZMod ℓ)} (hA : GoodM A A')
    (hd : A'.det ≠ 0) : GoodM A⁻¹ A'⁻¹ := by
  have hdet := hA.det
  have hinv := hdet.inv hd
  have hadj := hA.adjugate
  intro i j
  rw [Matrix.inv_def, Matrix.inv_def, Ring.inverse_eq_inv', Ring.inverse_eq_inv']
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact hinv.mul (hadj i j)

end

lemma ne_zero_of_LU_good {q : ℚ} {y : ZMod ℓ} (hq : CatalanCore.ThmA.LU ℓ q) (h : Good ℓ q y) :
    y ≠ 0 := by
  intro hy
  have h2 : Good ℓ q⁻¹ (red ℓ q⁻¹) := ⟨hq.2.2, rfl⟩
  have h3 := (h.mul h2).2
  rw [mul_inv_cancel₀ hq.1] at h3
  have h4 : red ℓ 1 = 1 := Good.one.2
  rw [h4, hy, zero_mul] at h3
  exact one_ne_zero h3

section Obj
variable {K m : ℕ}

lemma good_cast_add (a : ℕ) (j : ℤ) :
    Good ℓ ((0 : ℚ) + (a : ℚ) + (j : ℚ)) ((0 : ZMod ℓ) + (a : ZMod ℓ) + (j : ZMod ℓ)) :=
  ((Good.zero).add (Good.natCast a)).add (Good.intCast j)

lemma zmod_ne_zero_aj (a : ℕ) (j : ℤ) (hj : 1 ≤ j) (hl : a + j.toNat < ℓ) :
    (0 : ZMod ℓ) + (a : ZMod ℓ) + (j : ZMod ℓ) ≠ 0 := by
  have : (0 : ZMod ℓ) + (a : ZMod ℓ) + (j : ZMod ℓ) = ((a + j.toNat : ℕ) : ZMod ℓ) := by
    have : (j : ZMod ℓ) = ((j.toNat : ℕ) : ZMod ℓ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [this]; push_cast; ring
  rw [this]
  exact CatalanCore.natCast_ne_zero' (by omega) hl

lemma good_wcol (j : ℤ) (hj : 1 ≤ j) (hjl : j + K ≤ ℓ) :
    GoodV (wcol K (0 : ℚ) j) (wcol K (0 : ZMod ℓ) j) := fun a => by
  simp only [wcol]
  exact Good.div Good.one (good_cast_add a j)
    (zmod_ne_zero_aj a j hj (by have := a.2; omega))

lemma good_Wb {m : ℕ} (b : Fin m → ℤ) (hb : ∀ i, 1 ≤ b i ∧ b i + K ≤ ℓ) :
    GoodM (Wb K (0 : ℚ) b) (Wb K (0 : ZMod ℓ) b) := fun a i =>
  good_wcol (b i) (hb i).1 (hb i).2 a

lemma good_Nmat (J : Finset ℤ) (hJ : ∀ j ∈ J, 1 ≤ j ∧ j + K ≤ ℓ) :
    GoodM (Nmat K (0 : ℚ) J) (Nmat K (0 : ZMod ℓ) J) := fun a b => by
  simp only [Nmat, Matrix.sum_apply, Matrix.vecMulVec_apply]
  exact Good.sum _ _ _ fun j hj =>
    (good_wcol j (hJ j hj).1 (hJ j hj).2 a).mul (good_wcol j (hJ j hj).1 (hJ j hj).2 b)

lemma good_ubasis {m : ℕ} (n : ℕ) (bx : Fin m → ℤ) (hK : K < ℓ) :
    GoodM (ubasis K n (0 : ℚ) bx) (ubasis K n (0 : ZMod ℓ) bx) := fun a i => by
  simp only [ubasis, piB, pia]
  have hz : Good ℓ (-((0 : ℚ) + ((a : ℕ) : ℚ))) (-((0 : ZMod ℓ) + ((a : ℕ) : ZMod ℓ))) :=
    ((Good.zero).add (Good.natCast _)).neg
  refine Good.div ((Good.prod _ _ _ fun j _ => hz.sub (Good.intCast _)).mul (hz.pow' _)) ?_ ?_
  · exact Good.prod _ _ _ fun b _ => (Good.natCast _).sub (Good.natCast _)
  · refine Finset.prod_ne_zero_iff.2 fun b hb => ?_
    have hba : (b : ℕ) ≠ (a : ℕ) := fun h => (Finset.mem_erase.1 hb).1 (Fin.ext h)
    exact sub_ne_zero.2 (CatalanCore.natCast_ne_natCast (by have := b.2; omega)
      (by have := a.2; omega) hba)

lemma good_projB {m : ℕ} (bx by' : Fin m → ℤ) (hbx : ∀ i, 1 ≤ bx i ∧ bx i + K ≤ ℓ)
    (hby : ∀ i, 1 ≤ by' i ∧ by' i + K ≤ ℓ)
    (hΔ : CatalanCore.ThmA.LU ℓ ((Wb K (0 : ℚ) bx)ᵀ * Wb K (0 : ℚ) by').det) :
    GoodM (projB K (0 : ℚ) bx by') (projB K (0 : ZMod ℓ) bx by') := by
  have hG := (good_Wb (K := K) bx hbx).transpose.mul (good_Wb (K := K) by' hby)
  have hd : ((Wb K (0 : ZMod ℓ) bx)ᵀ * Wb K (0 : ZMod ℓ) by').det ≠ 0 :=
    ne_zero_of_LU_good hΔ hG.det
  unfold projB
  exact GoodM.one.sub (((good_Wb (K := K) by' hby).mul (hG.inv hd)).mul
    (good_Wb (K := K) bx hbx).transpose)

/-- **`kgenCore` reduces.** -/
theorem good_kgenCore {m : ℕ} (J : Finset ℤ) (S : ℤ) (bx by' : Fin m → ℤ) (hK : K < ℓ)
    (hJ : ∀ j ∈ J, 1 ≤ j ∧ j + K ≤ ℓ) (hS : 1 ≤ S ∧ S + K ≤ ℓ)
    (hbx : ∀ i, 1 ≤ bx i ∧ bx i + K ≤ ℓ) (hby : ∀ i, 1 ≤ by' i ∧ by' i + K ≤ ℓ)
    (hΔ : CatalanCore.ThmA.LU ℓ ((Wb K (0 : ℚ) bx)ᵀ * Wb K (0 : ℚ) by').det) :
    Good ℓ (kgenCore K m (0 : ℚ) J S bx by') (kgenCore K m (0 : ZMod ℓ) J S bx by') := by
  unfold kgenCore
  refine GoodM.det (fun k i => ?_)
  have hPN := (good_projB bx by' hbx hby hΔ).mul (good_Nmat (K := K) J hJ)
  have hv1 := GoodM.vecMul (good_wcol (K := K) S hS.1 hS.2) (hPN.pow (k : ℕ))
  have hv := GoodM.vecMul hv1 (good_ubasis (K - m) bx hK)
  simp only [Matrix.of_apply]
  exact hv i

end Obj

end CatalanCore.Star.Leonard
