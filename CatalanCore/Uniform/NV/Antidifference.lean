module
public import CatalanCore.Uniform.NV.StepWronskian
@[expose] public section
open Polynomial
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [CharZero K]
open CatalanCore.Rect.CharZeroNV

/-- A genuine simple pole isolated in its translation orbit. -/
structure IsolatedStepPole (L a : K) (D A : K[X]) : Prop where
  step_ne_zero : L ≠ 0
  pole : D.eval a = 0
  residue : A.eval a ≠ 0
  forward : ∀ n : ℕ, D.eval (a+((n:K)+1)*L) ≠ 0
  backward : ∀ n : ℕ, D.eval (a-((n:K)+1)*L) ≠ 0

theorem no_reduced_step_antidifference {L a : K} {D A q p : K[X]}
    (h : IsolatedStepPole L a D A) (hcp : IsCoprime q p) (hp : p ≠ 0) :
    D*(shiftBy L q*p-q*shiftBy L p) ≠ A*p*shiftBy L p := by
  intro heq
  have he (x : K) := congrArg (fun P : K[X] => P.eval x) heq
  have hstart : p.eval a = 0 ∨ p.eval (a+L) = 0 := by
    have he' := he a
    simp only [eval_mul,eval_sub,eval_shiftBy,h.pole,zero_mul] at he'
    rcases mul_eq_zero.mp he'.symm with hprod | hz
    · exact Or.inl ((mul_eq_zero.mp hprod).resolve_left h.residue)
    · exact Or.inr hz
  have hroot : ∀ n : ℕ, p.eval (a+((n:K)+1)*L) = 0 ∨ p.eval (a-(n:K)*L) = 0 := by
    rcases hstart with hneg | hpos
    · have hall : ∀ n : ℕ, p.eval (a-(n:K)*L) = 0 := by
        intro n
        induction n with
        | zero => simpa using hneg
        | succ n ih =>
          have he' := he (a-((n:K)+1)*L)
          have hs : a-((n:K)+1)*L+L = a-(n:K)*L := by ring
          simp only [eval_mul,eval_sub,eval_shiftBy,hs,ih,mul_zero,sub_zero] at he'
          have hz := (mul_eq_zero.mp ((mul_eq_zero.mp he').resolve_left (h.backward n))).resolve_left
            (coprime_eval_ne_zero hcp ih)
          simpa only [Nat.cast_succ] using hz
      exact fun n => Or.inr (hall n)
    · have hall : ∀ n : ℕ, p.eval (a+((n:K)+1)*L) = 0 := by
        intro n
        induction n with
        | zero => simpa using hpos
        | succ n ih =>
          have he' := he (a+((n:K)+1)*L)
          simp only [eval_mul,eval_sub,eval_shiftBy,ih,mul_zero,zero_mul,zero_sub] at he'
          have hz := (mul_eq_zero.mp he').resolve_left (h.forward n)
          have hz' := (mul_eq_zero.mp (neg_eq_zero.mp hz)).resolve_left
            (coprime_eval_ne_zero hcp ih)
          convert hz' using 1 <;> push_cast <;> congr 1 <;> ring
      exact fun n => Or.inl (hall n)
  have hinf : Set.Infinite {x : K | p.IsRoot x} := by
    by_contra hn
    have hf := Set.not_infinite.mp hn
    have hfpos : Set.Finite {n : ℕ | p.eval (a+((n:K)+1)*L) = 0} :=
      hf.preimage (by
        intro n _ m _ he
        apply Nat.cast_injective (R := K)
        have hm : ((n:K)-(m:K))*L = 0 := by linear_combination he
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right h.step_ne_zero))
    have hfneg : Set.Finite {n : ℕ | p.eval (a-(n:K)*L) = 0} :=
      hf.preimage (by
        intro n _ m _ he
        apply Nat.cast_injective (R := K)
        have hm : ((n:K)-(m:K))*L = 0 := by linear_combination -he
        exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right h.step_ne_zero))
    have hu : Set.Finite (Set.univ : Set ℕ) := by
      apply (hfpos.union hfneg).subset
      intro n _
      exact hroot n
    exact Set.infinite_univ hu
  exact hp (p.eq_zero_of_infinite_isRoot hinf)

/-- Coprime reduction removes no obstruction and introduces no new premise. -/
theorem no_step_antidifference {L a : K} {D A : K[X]}
    (h : IsolatedStepPole L a D A) (q p : K[X]) (hp : p ≠ 0) :
    D*(shiftBy L q*p-q*shiftBy L p) ≠ A*p*shiftBy L p := by
  classical
  let g := GCDMonoid.gcd q p
  have hg : g ≠ 0 := gcd_ne_zero_of_right hp
  let q0 := q/g
  let p0 := p/g
  have hq : g*q0 = q := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_left _ _)
  have hp' : g*p0 = p := EuclideanDomain.mul_div_cancel' hg (gcd_dvd_right _ _)
  have hcp : IsCoprime q0 p0 := isCoprime_div_gcd_div_gcd hp
  have hp0 : p0 ≠ 0 := right_div_gcd_ne_zero hp
  have hsg : shiftBy L g ≠ 0 := by
    intro hz
    have hback := congrArg (fun P : K[X] => P.comp (X-C L)) hz
    have hid : (shiftBy L g).comp (X-C L) = g := by
      simp only [shiftBy,comp_assoc,add_comp,X_comp,C_comp]
      convert g.comp_X using 1
      congr 1
      ring
    rw [hid,zero_comp] at hback
    exact hg hback
  intro heq
  apply no_reduced_step_antidifference h hcp hp0
  apply mul_left_cancel₀ (mul_ne_zero hg hsg)
  calc
    (g*shiftBy L g)*(D*(shiftBy L q0*p0-q0*shiftBy L p0)) =
        D*(shiftBy L q*p-q*shiftBy L p) := by
      rw [← hq,← hp']
      simp only [shiftBy,mul_comp]
      ring
    _ = A*p*shiftBy L p := heq
    _ = (g*shiftBy L g)*(A*p0*shiftBy L p0) := by
      rw [← hp']
      simp only [shiftBy,mul_comp]
      ring

theorem stepDefect_ne_zero {L a : K} {D A : K[X]} (h : IsolatedStepPole L a D A)
    (q p : K[X]) (hp : p ≠ 0) : stepDefect L D A q p ≠ 0 := by
  intro hz
  exact no_step_antidifference h q p hp (sub_eq_zero.mp hz)
end CatalanCore.Uniform.NV
