module
public import CatalanCore.Arith.Hybrid.PoleModel
public import CatalanCore.Arith.Hybrid.LoewnerMoment
@[expose] public section
open Finset Matrix CatalanCore
namespace CatalanCore.Arith.Hybrid
open ChainClasses

/-- A free residue has the source chain's prefix, with only its last node optional.
No primality or matrix hypothesis is used; the statement crosses the core boundary. -/
theorem free_residue_core_prefix {p r N z c c0 q : ℕ}
    (hc : c<p) (hc0 : c0<p) (hz : z=c0+q*p) (hrz : r≤z) (hzN : z<N)
    (hfree : ∀k, r≤k → k<N → k%p≠c) (i : ℕ) :
    c+i*p<r ↔ i<q ∨ (i=q ∧ c+q*p<r) := by
  have hsmall (hi : i<q) : c+i*p<r := by
    have hmul : (i+1)*p≤q*p := Nat.mul_le_mul_right p (by omega)
    have hiz : c+i*p<z := by nlinarith
    by_contra hh
    have hb : r≤c+i*p := by omega
    have hm : (c+i*p)%p=c := by simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
    exact hfree _ hb (hiz.trans hzN) hm
  constructor
  · intro hi
    by_cases hlt : i<q
    · exact Or.inl hlt
    · have hle : i≤q := by
        by_contra hn
        have hmul : (q+1)*p≤ i*p := Nat.mul_le_mul_right p (by omega)
        nlinarith
      exact Or.inr ⟨by omega, by simpa [show i=q by omega] using hi⟩
  · rintro (hi | ⟨rfl, hi⟩)
    · exact hsmall hi
    · exact hi

/-- The source residue has exactly the preceding prefix when the zone is shorter
than a period. -/
theorem source_residue_core_prefix {p r N z c0 q : ℕ}
    (hc0 : c0<p) (hz : z=c0+q*p) (hrz : r≤z) (hzN : z<N)
    (hwidth : N<r+p) (i : ℕ) : c0+i*p<r ↔ i<q := by
  constructor
  · intro hi
    by_contra hn
    have hm : q*p≤ i*p := Nat.mul_le_mul_right p (by omega)
    omega
  · intro hi
    have hm : (i+1)*p≤q*p := Nat.mul_le_mul_right p (by omega)
    nlinarith

variable {p : ℕ} [Fact p.Prime]
/-- Prefixes include their left endpoint's pole jump. There is no crossing of
that jump inside either unwrapped half-open residue arc. -/
theorem residue_arc_noCut {o h a b : ℕ} (hp : 5≤p)
    (hh : h<p) (hroot : 4*(h:ZMod p)=(o:ZMod p))
    (hab : a≤b) (hb : b<p) (harc : b<h ∨ h≤a) :
    NoCut (Singular p o) a b := by
  intro t hat htb hs
  have ht0 : (0:ℤ)<t := by omega
  have htp : t<(p:ℤ) := by omega
  rcases hs with hs | hs
  · have he := Int.le_of_dvd ht0 hs
    omega
  · have hmod : (((4*t-(o:ℤ)):ℤ):ZMod p)=0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact hs
    push_cast at hmod
    have h4 : (4:ZMod p)≠0 := four_ne_zmod p hp
    have hte : (t:ZMod p)=(h:ZMod p) := by
      apply mul_left_cancel₀ h4
      exact (sub_eq_zero.mp hmod).trans hroot.symm
    have htn : ((t.toNat:ℕ):ℤ)=t := Int.toNat_of_nonneg (by omega)
    have htnp : t.toNat<p := by omega
    have he : ((t.toNat:ℕ):ZMod p)=(h:ZMod p) := by
      rw [←Int.cast_natCast,htn]
      exact hte
    have hv := congrArg ZMod.val he
    have hne : t.toNat=h := by simpa [Nat.mod_eq_of_lt htnp,Nat.mod_eq_of_lt hh] using hv
    rcases harc with harc | harc <;> omega

/-- Translate a pole-free residue interval up any number of periods. -/
theorem residue_arc_noCut_period {o h a b i : ℕ} (hp : 5≤p)
    (hh : h<p) (hroot : 4*(h:ZMod p)=(o:ZMod p))
    (hab : a≤b) (hb : b<p) (harc : b<h ∨ h≤a) :
    NoCut (Singular p o) (a+i*p) (b+i*p) := by
  have base := residue_arc_noCut hp hh hroot hab hb harc
  intro t hat htb hs
  have H : Singular (p:ℤ) o (t-(i:ℤ)*p) := by
    have H:=singular_periodic (p:ℤ) o (t-(i:ℤ)*p) i
    apply H.mp
    convert hs using 1 <;> ring
  apply base (t-(i:ℤ)*p) (by push_cast at hat;omega) (by push_cast at htb;omega) H

/-- Both pole cumulatives, including squared poles and endpoint conventions,
transport across a core-boundary change on one unwrapped residue arc. -/
theorem pole_prefixes_residue_arc {Fr : Frame} {o h a b i : ℕ}
    (hL : LamData Fr o) (hp : 5≤p) (hh : h<p)
    (hroot : 4*(h:ZMod p)=(o:ZMod p)) (hab : a≤b) (hb : b<p)
    (harc : b<h ∨ h≤a) :
    polePrefix Fr p o (a+i*p)=polePrefix Fr p o (b+i*p) ∧
    poleSquarePrefix Fr p o (a+i*p)=poleSquarePrefix Fr p o (b+i*p) := by
  have hno:=residue_arc_noCut_period (i:=i) hp hh hroot hab hb harc
  exact ⟨polePrefix_nocut hL (by omega) hno,
    poleSquarePrefix_nocut hL (by omega) hno⟩


section Response
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
noncomputable def quadraticResponse (Q : Matrix ι ι K) (u : ι→K) : K :=
  dotProduct u (Q⁻¹ *ᵥ u)

theorem quadraticResponse_of_solution (Q : Matrix ι ι K) (u v : ι→K)
    (hQ : IsUnit Q.det) (hv : Q *ᵥ v=u) :
    quadraticResponse Q u=dotProduct u v := by
  have he : Q⁻¹ *ᵥ u=v := by
    rw [←hv,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hQ,Matrix.one_mulVec]
  simp only [quadraticResponse,he]

def sourceCompletion (Q : Matrix ι ι K) (b : ι→K) (d : K) :
    Matrix (ι⊕Unit) (ι⊕Unit) K := fun i j=>match i,j with
      | Sum.inl a,Sum.inl c=>Q a c
      | Sum.inl a,Sum.inr _=>b a
      | Sum.inr _,Sum.inl c=>b c
      | Sum.inr _,Sum.inr _=>d

/-- A source coordinate whose predicted solution is zero can be added or removed
without altering the inverse quadratic response. The diagonal may contain U. -/
theorem completion_quadraticResponse (Q : Matrix ι ι K) (b u v : ι→K) (d s : K)
    (hQ : IsUnit Q.det) (hcomplete : IsUnit (sourceCompletion Q b d).det)
    (hv : ∀i,∑j,Q i j*v j=u i) (hs : ∑i,b i*v i=s) :
    quadraticResponse (sourceCompletion Q b d) (Sum.elim u (fun _=>s))=
      quadraticResponse Q u := by
  have H:=bordered_response_zero Q b u v d s hv hs
  dsimp only at H
  have hv0 : Q *ᵥ v=u := funext hv
  have hv1 : sourceCompletion Q b d *ᵥ (Sum.elim v (fun _=>0))=
      Sum.elim u (fun _=>s) := funext H.1
  rw [quadraticResponse_of_solution _ _ _ hcomplete hv1,
      quadraticResponse_of_solution _ _ _ hQ hv0]
  exact H.2
end Response

#print axioms completion_quadraticResponse
#print axioms free_residue_core_prefix
#print axioms source_residue_core_prefix
#print axioms pole_prefixes_residue_arc
end CatalanCore.Arith.Hybrid
