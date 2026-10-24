module
public import CatalanArchive.CatalanCore.Arith.Hybrid.PeriodicPerturbation
public import CatalanArchive.CatalanCore.Linalg.DiagonalMinor
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

def gleAddSubgroup (p B : ℕ) [Fact p.Prime] : AddSubgroup ℚ[X] where
  carrier := GLE p B
  zero_mem' := GLE.zero B
  add_mem' := GLE.add
  neg_mem' := by
    intro f hf
    change GLE p B (-f)
    simpa using hf.zsmul (-1)

/-- Every principal restriction retaining the zone has the same weighted
denominator bound as the full common core. -/
theorem principal_full_det_weighted (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hx : ∀z,xs z<N) (hy : ∀y,ys y<N)
    (hxlo : ∀z,r≤xs z) (hylo : ∀y,r≤ys y) (hne : ∀z y,xs z≠ys y)
    (w : Z→Z→ℕ) (hw : ∀z y,w z y≤2)
    (hzero : ∀z y,w z y=0→NoCut (Cut p r D.singular)
      (min (xs z:ℤ) (ys y)) (max (xs z:ℤ) (ys y)))
    (hone : ∀z y,w z y=1→xs z%p≠ys y%p)
    (s : Finset (Fin r⊕Z)) (hzone : ∀z,Sum.inr z∈s) :
    GLE p (tropVal w+2*r)
      ((full Fr p r xs ys).submatrix (Subtype.val : s→Fin r⊕Z) Subtype.val).det := by
  let O : Subring ℚ[X] := (Int.castRingHom ℚ[X]).range
  apply CatalanCore.Linalg.principal_mem_of_diagonal_stability O
    (gleAddSubgroup p (tropVal w+2*r)) (full Fr p r xs ys) s
  intro d hd
  have hc (a : Fin r⊕Z) : C ((d a:ℚ[X]).coeff 0)=(d a:ℚ[X]) := by
    obtain ⟨n,hn⟩ := (d a).property
    change (n:ℚ[X])=(d a:ℚ[X]) at hn
    rw [←hn]
    simp
  let E : Matrix (Fin r) (Fin r) ℚ := Matrix.diagonal (fun i=>(d (Sum.inl i):ℚ[X]).coeff 0)
  have he : ∀i j,E i j∈S p := by
    intro i j
    by_cases hij : i=j
    · subst j
      obtain ⟨n,hn⟩ := (d (Sum.inl i)).property
      change (n:ℚ[X])=(d (Sum.inl i):ℚ[X]) at hn
      simpa [E,Matrix.diagonal_apply,←hn] using (Good.intCast (ℓ:=p) n).mem
    · simp [E,Matrix.diagonal_apply,hij,(S p).zero_mem]
  have hm : (full Fr p r xs ys)+Matrix.diagonal (fun a=>(d a:ℚ[X]))=
      Matrix.fromBlocks ((full Fr p r xs ys).toBlocks₁₁+E.map C)
        (full Fr p r xs ys).toBlocks₁₂ (full Fr p r xs ys).toBlocks₂₁
        (full Fr p r xs ys).toBlocks₂₂ := by
    apply Matrix.ext
    intro a b
    rcases a with a|a <;> rcases b with b|b
    · by_cases hab : a=b
      · subst b;simp [E,Matrix.diagonal_apply,hc] <;> rfl
      · simp [E,Matrix.diagonal_apply,hab] <;> rfl
    · simp [Matrix.diagonal_apply] <;> rfl
    · simp [Matrix.diagonal_apply] <;> rfl
    · have hz : (d (Sum.inr a):ℚ[X])=0 := by rw [hd _ (hzone a)];rfl
      simp [Matrix.diagonal_apply,hz] <;> rfl
  change GLE p (tropVal w+2*r) _
  rw [hm]
  exact perturbed_full_det_weighted D hN hr hx hy hxlo hylo hne w hw hzero hone E he
end CatalanCore.Arith.Hybrid.Periodic.Model
