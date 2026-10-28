module

public import CatalanCore.Uniform.Content.RankProducer.Triv
public import CatalanFrames.P6.Frame

@[expose] public section

/-! Axiom audit and a non-vacuity instance for lane H15 (rank-layer producer). -/

open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Member CatalanFrames.P6

namespace CatalanCore.Uniform.Content.RankProducer.Audit

/-- The p6 frame with rational shifts `1, 1/3, 1/2`. -/
def u6 : Fin 3 → ℕ := ![1, 1, 1]
def q6 : Fin 3 → ℕ := ![1, 3, 2]

theorem hu6 : ∀ j, p6Frame.μ j = u6 j / q6 j := by
  intro j; fin_cases j <;> simp [p6Frame, u6, q6]

theorem hq6 : ∀ j, 0 < q6 j := by
  intro j; fin_cases j <;> simp [q6]

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Non-vacuity: the empty member of the p6 digamma frame at `p = 7` has a `RankMember`, and the
rank theorem applies to it. -/
noncomputable def emptyMember : RankMember p6Frame u6 q6 (fun a : Fin 0 => 0)
    (fun _ : Fin 0 => 0) (fun _ : Fin 0 => 0) ∅ 7 :=
  RankMember.triv p6Frame u6 q6 _ _ _ _ 7 0
    (by
      intro j
      show (((p6Frame.w j : ℤ) : ℚ) / p6Frame.norm) ∈ S 7
      fin_cases j <;> (rw [mem_S]; decide +kernel))
    (by intro j; fin_cases j <;> simp [frameDigamma, q6] <;> decide +kernel)
    (by norm_num)
    (by intro j; fin_cases j <;> simp [frameDigamma, q6, u6] <;> decide +kernel)
    (by norm_num)
    (fun i => isEmptyElim i) (fun j => isEmptyElim j)
    (fun i j _ => isEmptyElim i) (fun i j _ => isEmptyElim i)

end CatalanCore.Uniform.Content.RankProducer.Audit

#print axioms CatalanCore.Uniform.Content.RankProducer.blockKernelOfCerts
#print axioms CatalanCore.Uniform.Content.RankProducer.rowLoad_eq
#print axioms CatalanCore.Uniform.Content.RankProducer.colLoad_block
#print axioms CatalanCore.Uniform.Content.RankProducer.ucol_le_colSpan
#print axioms CatalanCore.Uniform.Content.RankProducer.urow_le_rowAnn
#print axioms CatalanCore.Uniform.Content.RankProducer.rank_price_certs
#print axioms CatalanCore.Uniform.Content.RankProducer.RankMember.gle
#print axioms CatalanCore.Uniform.Content.RankProducer.DebitLayer.rank
#print axioms CatalanCore.Uniform.Content.RankProducer.RankMember.ofExact
#print axioms CatalanCore.Uniform.Content.RankProducer.RankMember.triv
#print axioms CatalanCore.Uniform.Content.RankProducer.RankMember.price_le_two_mul
#print axioms CatalanCore.Uniform.Content.RankProducer.trivCert_realizes
#print axioms CatalanCore.Uniform.Content.RankProducer.Audit.emptyMember
