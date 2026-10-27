module
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponseRational
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponseStep
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanMeasure.GenD.Uniform.Prefix
open Polynomial Finset OAI.InternalCatalan
noncomputable section
variable {p : ℕ} [Fact p.Prime]
local notation "Fp" => ZMod p

def integerPstepPsi (K ah q J : ℕ) (S : ℤ) (a b : ℤ[X]) : ℚ :=
  ∑ k∈range (q+1),(((-1:ℤ)^(q-k)*(q.choose k:ℤ)):ℚ)*integerPsi K ah (J+k) S a b

def pstepMomentException (K q J : ℕ) : ℕ :=
  ∏ k∈range (q+1),sourceMomentException (J+k) K

theorem pstepMomentException_pos (K q J : ℕ) : 0<pstepMomentException K q J := by
  apply Finset.prod_pos
  intro k _
  exact sourceMomentException_pos _ _

theorem integerPstepPsi_residue (K ah q J : ℕ) (S : ℤ) (a b : ℤ[X])
    (hpD : ¬p∣pstepMomentException K q J) :
    ((integerPstepPsi K ah q J S a b).den:Fp)≠0 ∧
    palindromicRatResidue p (integerPstepPsi K ah q J S a b)=
      pstepCovector q (fun j s => sourcePsi K ah j s
        (a.map (Int.castRingHom Fp)) (b.map (Int.castRingHom Fp))) J S := by
  have hlocal : ∀k∈range (q+1),¬p∣sourceMomentException (J+k) K := by
    intro k hk hd
    exact hpD (hd.trans (Finset.dvd_prod_of_mem (fun k => sourceMomentException (J+k) K) hk))
  have hden : ∀k∈range (q+1),((integerPsi K ah (J+k) S a b).den:Fp)≠0 := by
    intro k hk
    exact (integerPsi_residue K ah (J+k) S a b (hlocal k hk)).1
  have hr := palindromicRatResidue_int_sum (p:=p) (range (q+1))
    (fun k => (-1:ℤ)^(q-k)*(q.choose k:ℤ)) (fun k => integerPsi K ah (J+k) S a b) hden
  refine ⟨hr.1,?_⟩
  rw [show integerPstepPsi K ah q J S a b=
      ∑ k∈range (q+1),(((-1:ℤ)^(q-k)*(q.choose k:ℤ)):ℚ)*integerPsi K ah (J+k) S a b from rfl,hr.2]
  unfold pstepCovector
  apply Finset.sum_congr rfl
  intro k hk
  rw [(integerPsi_residue K ah (J+k) S a b (hlocal k hk)).2]
  simp only [Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,Int.cast_natCast]

#print axioms integerPstepPsi_residue
end
end CatalanMeasure.GenD.Uniform.Prefix

