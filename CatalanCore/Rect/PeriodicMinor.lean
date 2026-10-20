module
public import CatalanCore.Arith.Hybrid.PeriodicPrincipal
public import CatalanCore.Rect.MinorContent
@[expose] public section
open Matrix Polynomial CatalanCore.Arith.Hybrid
namespace CatalanCore.Rect
open Arith.Hybrid.LemmaE Arith.Hybrid.ChainClasses Arith.Hybrid.ChainModel
open Arith.Hybrid.Periodic
variable {p r m N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The cut-free periodic content bound is uniform in all common-node deletions. -/
theorem commonMinorPoly_periodic_gle (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hzN : r+2*m≤N)
    (w : Fin m→Fin m→ℕ) (hw : ∀i j,w i j≤2)
    (hzero : ∀i j,w i j=0→NoCut (Cut p r D.singular)
      (min ((r+2*i.val:ℕ):ℤ) (r+2*j.val+1))
      (max ((r+2*i.val:ℕ):ℤ) (r+2*j.val+1)))
    (hone : ∀i j,w i j=1→(r+2*i.val)%p≠(r+2*j.val+1)%p)
    (s : Finset (Fin r)) : GLE p (tropVal w+2*r) (commonMinorPoly Fr r m s) := by
  classical
  let S : Finset (Fin r⊕Fin m):=Finset.univ.filter (fun a=>match a with
    | Sum.inl i=>i∈s | Sum.inr _=>True)
  let f : (s⊕Fin m)→S :=fun a=>match a with
    | Sum.inl i=>⟨Sum.inl i.val,by simp [S,i.property]⟩
    | Sum.inr i=>⟨Sum.inr i,by simp [S]⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have H:=congrArg Subtype.val hab
      rcases a with a|a <;> rcases b with b|b <;> simp_all [f]
    · intro a
      rcases a with ⟨a,ha⟩
      rcases a with a|a
      · exact ⟨Sum.inl ⟨a,by simpa [S] using ha⟩,rfl⟩
      · exact ⟨Sum.inr a,rfl⟩
  let e : (s⊕Fin m)≃S := Equiv.ofBijective f hf
  let F:=full Fr p r (fun i:Fin m=>r+2*i.val) (fun j:Fin m=>r+2*j.val+1)
  have H:=Periodic.Model.principal_full_det_weighted
    (xs:=fun i:Fin m=>r+2*i.val) (ys:=fun j:Fin m=>r+2*j.val+1) D hN hr
    (fun i=>by have:=i.isLt;omega) (fun i=>by have:=i.isLt;omega)
    (fun i=>by omega) (fun i=>by omega) (fun i j=>by omega)
    w hw hzero hone S (fun z=>by simp [S])
  have he := Matrix.det_submatrix_equiv_self e
    (F.submatrix (Subtype.val : S→Fin r⊕Fin m) Subtype.val)
  rw [←he] at H
  have hm : ((F.submatrix (Subtype.val : S→Fin r⊕Fin m) Subtype.val).submatrix e e)=
      (FullN Fr (fun i:s=>i.val.val) (fun i:Fin m=>r+2*i.val)
        (fun j:Fin m=>r+2*j.val+1) (X:ℚ[X])).map (rescaleHom p 2) := by
    apply Matrix.ext
    intro a b
    rcases a with a|a <;> rcases b with b|b
    · change rescaleHom p 2 (C (Fr.Mn a.val.val b.val.val)+X*(if a.val=b.val then 1 else 0))=
        rescaleHom p 2 (C (Fr.Mn a.val.val b.val.val)+X*(if a=b then 1 else 0))
      simp only [Subtype.val_inj]
    · rfl
    · rfl
    · rfl
  change GLE p (tropVal w+2*r) _ at H
  rw [hm,det_rescale] at H
  exact GLE.of_rescale H
end CatalanCore.Rect
