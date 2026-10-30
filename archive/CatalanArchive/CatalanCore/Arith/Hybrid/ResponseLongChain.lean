module
public import CatalanCore.Arith.Hybrid.ResponseLongEq
public import CatalanCore.Arith.Hybrid.ChainPoleReduction
@[expose] public section
open Finset Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid
open ChainClasses

/-! # Free-long response, bridge to the reduced pole model

`poleRed` is the reduced (over `𝔽_p(U)`) pole-model matrix of a node family, `poleL` its
reduced cumulative.  The main theorem `response_long_core` is generic in the two node families
(the source chain and the chain of another residue) and in the unwrapped-arc hypotheses. -/

section Defs
variable (Fr : Frame) (p o : ℕ) [Fact p.Prime]

/-- Reduced pole model of a node family: `rfC (p²Mn mod p) + U·1`. -/
noncomputable def poleRed {ι : Type} [DecidableEq ι] (a : ι → ℕ) :
    Matrix ι ι (RatFunc (ZMod p)) :=
  Matrix.of fun i j => rfC p (red p (poleScaledEntry Fr p o (a i) (a j))) +
    if i = j then rfX p else 0

/-- Reduced cumulative `p · polePrefix`. -/
noncomputable def poleL (x : ℕ) : RatFunc (ZMod p) :=
  rfC p (red p ((p:ℚ) * polePrefix Fr p o x))
end Defs

section Unit
variable {p : ℕ} [Fact p.Prime]

/-- `det (M + U·1)` over `𝔽_p(U)` is a unit: it is a monic characteristic polynomial. -/
theorem isUnit_det_const_add_X {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι (ZMod p)) :
    IsUnit (Matrix.of (fun i j => rfC p (M i j) + if i = j then rfX p else 0)).det := by
  set P : Matrix ι ι (ZMod p)[X] :=
    M.map Polynomial.C + (Polynomial.X : (ZMod p)[X]) • (1 : Matrix ι ι (ZMod p)[X]) with hP
  have h1 : Matrix.of (fun i j => rfC p (M i j) + if i = j then rfX p else 0) =
      P.map (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hP, rfC, rfX, Matrix.one_apply]
    · simp [hP, rfC, hij, Matrix.one_apply]
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, isUnit_iff_ne_zero, ne_eq,
    map_eq_zero_iff _ (RatFunc.algebraMap_injective (ZMod p)), hP, Rect.det_map_C_add_X]
  exact (Matrix.charpoly_monic _).ne_zero

theorem isUnit_det_poleRed {Fr : Frame} {o : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) : IsUnit (poleRed Fr p o a).det :=
  isUnit_det_const_add_X (fun i j => red p (poleScaledEntry Fr p o (a i) (a j)))
end Unit

section Entries
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The exact pole entry is `p`-integral (same-residue core nodes). -/
theorem poleScaledEntry_mem (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) {a b : ℕ}
    (ha : a<N) (hb : b<N) (hc : a%p=b%p) : poleScaledEntry Fr p o a b ∈ S p := by
  have hNp : N<p*p := by omega
  have H := poleScaledEntry_second_order hL hp (ha.trans hNp) (hb.trans hNp) hc
  have h1 := Mn_square_mem hL hp hN ha hb
  have h2 := ((Good.natCast (ℓ:=p) p).mul H).mem
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have e : poleScaledEntry Fr p o a b =
      (p:ℚ)^2*Fr.Mn a b - (p:ℚ)*(((p:ℚ)^2*Fr.Mn a b-poleScaledEntry Fr p o a b)/p) := by
    field_simp; ring
  rw [e]
  exact (S p).sub_mem h1 (by simpa using h2)

/-- The reduced commutator identity: `16 m · red(pse a b) = L b - L a` for `b - a = m p`. -/
theorem pole_comm_red (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) {a b : ℕ}
    (ha : a<N) (hb : b<N) (hmod : a%p=b%p) (m : ℤ) (hm : (b:ℤ)-a=m*p) :
    (16:RatFunc (ZMod p)) * (m:RatFunc (ZMod p)) *
        rfC p (red p (poleScaledEntry Fr p o a b)) =
      poleL Fr p o b - poleL Fr p o a := by
  have hn : Good p Fr.norm (16:ZMod p) := by rw [hL.norm_eq]; exact Good.ofNat 16
  have hn0 : Fr.norm ≠ 0 := by rw [hL.norm_eq]; norm_num
  have hpse := poleScaledEntry_mem hL hp hN ha hb hmod
  have hG : Good p (Fr.norm * (m:ℚ) * poleScaledEntry Fr p o a b)
      (16 * (m:ZMod p) * red p (poleScaledEntry Fr p o a b)) :=
    (hn.mul (Good.intCast m)).mul (good_red hpse)
  have hG2 : Good p ((p:ℚ) * polePrefix Fr p o b - (p:ℚ) * polePrefix Fr p o a)
      (red p ((p:ℚ) * polePrefix Fr p o b) - red p ((p:ℚ) * polePrefix Fr p o a)) :=
    (good_red (p_polePrefix_mem hL hN hb)).sub (good_red (p_polePrefix_mem hL hN ha))
  have hE := pole_comm (Fr := Fr) (o := o) hn0 a b m hm
  have key : (16:ZMod p) * (m:ZMod p) * red p (poleScaledEntry Fr p o a b) =
      red p ((p:ℚ) * polePrefix Fr p o b) - red p ((p:ℚ) * polePrefix Fr p o a) := by
    have h1 := hG.eq
    rw [hE] at h1
    rw [← h1]
    exact hG2.eq
  have := congrArg (rfCH p) key
  simp only [map_mul, map_sub, map_intCast, map_ofNat] at this
  simpa only [poleL, rfC_eq] using this

end Entries





section Response
variable (Fr : Frame) (p o : ℕ) [Fact p.Prime]

/-- Source moments `A = L(z) - ∑ g L`, `B = 1 - ∑ g` with `g = Q⁻¹ b` of the source chain `a`. -/
noncomputable def sourceA {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (z : ℕ) :
    RatFunc (ZMod p) :=
  poleL Fr p o z - ∑ i, ((poleRed Fr p o a)⁻¹ *ᵥ
    (fun i => rfC p (red p (poleScaledEntry Fr p o (a i) z)))) i * poleL Fr p o (a i)

noncomputable def sourceB {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℕ) (z : ℕ) :
    RatFunc (ZMod p) :=
  1 - ∑ i, ((poleRed Fr p o a)⁻¹ *ᵥ
    (fun i => rfC p (red p (poleScaledEntry Fr p o (a i) z)))) i

/-- The reduced response `c̄ = ūᵀ Q̄⁻¹ ū`, `ū = A - B L`, of the chain with nodes `a`. -/
noncomputable def cResp {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → ℕ)
    (A B : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  quadraticResponse (poleRed Fr p o a) (fun i => A - B * poleL Fr p o (a i))
end Response

section Transport
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- Same period level, other residue. -/
def lvlShift (p c x : ℕ) : ℕ := c + (x / p) * p

theorem dec_mod {x m : ℕ} (hx : x % p = m) : m + (x / p) * p = x := by
  have := Nat.mod_add_div x p
  rw [hx, mul_comm] at this
  exact this

theorem lvlShift_mod {c : ℕ} (hc : c < p) (x : ℕ) : lvlShift p c x % p = c := by
  unfold lvlShift
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]

theorem add_mul_div_lt {m n : ℕ} (hm : m < p) : (m + n * p) / p = n := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt hm, zero_add]

theorem lvlShift_sub {c c0 : ℕ} {x y : ℕ} (hx : x % p = c0) (hy : y % p = c0) :
    ((lvlShift p c y : ℕ) : ℤ) - (lvlShift p c x : ℕ) = (y : ℤ) - x := by
  have hx' := dec_mod hx
  have hy' := dec_mod hy
  unfold lvlShift
  generalize x / p = i at hx'
  generalize y / p = j at hy'
  subst hx' hy'
  push_cast
  ring

theorem pole_prefix_lvlShift (hL : LamData Fr o) (hp : 5≤p) {h c c0 : ℕ} (hh : h<p)
    (hroot : 4*(h:ZMod p)=(o:ZMod p)) (hc : c<p) (hc0 : c0<p)
    (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0)) {x : ℕ} (hx : x%p=c0) :
    polePrefix Fr p o (lvlShift p c x) = polePrefix Fr p o x ∧
    poleSquarePrefix Fr p o (lvlShift p c x) = poleSquarePrefix Fr p o x := by
  have e : c0 + (x/p)*p = x := dec_mod hx
  unfold lvlShift
  rcases le_total c0 c with hle | hle
  · have H := pole_prefixes_residue_arc (Fr:=Fr) (o:=o) (h:=h) (a:=c0) (b:=c) (i:=x/p)
      hL hp hh hroot hle hc (by omega)
    rw [e] at H
    exact ⟨H.1.symm, H.2.symm⟩
  · have H := pole_prefixes_residue_arc (Fr:=Fr) (o:=o) (h:=h) (a:=c) (b:=c0) (i:=x/p)
      hL hp hh hroot hle hc0 (by omega)
    rw [e] at H
    exact ⟨H.1, H.2⟩

theorem poleL_lvlShift (hL : LamData Fr o) (hp : 5≤p) {h c c0 : ℕ} (hh : h<p)
    (hroot : 4*(h:ZMod p)=(o:ZMod p)) (hc : c<p) (hc0 : c0<p)
    (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0)) {x : ℕ} (hx : x%p=c0) :
    poleL Fr p o (lvlShift p c x) = poleL Fr p o x := by
  unfold poleL
  rw [(pole_prefix_lvlShift hL hp hh hroot hc hc0 harc hx).1]

theorem poleRed_lvlShift (hL : LamData Fr o) (hp : 5≤p) {h c c0 : ℕ} (hh : h<p)
    (hroot : 4*(h:ZMod p)=(o:ZMod p)) (hc : c<p) (hc0 : c0<p)
    (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0)) {κ : Type} [DecidableEq κ] (e : κ → ℕ)
    (he : ∀ i, e i % p = c0) :
    poleRed Fr p o (fun i => lvlShift p c (e i)) = poleRed Fr p o e := by
  ext i j
  simp only [poleRed, Matrix.of_apply]
  have H := poleScaledEntry_transport (Fr:=Fr) (p:=p) (o:=o) (a:=e i) (b:=e j)
    (a':=lvlShift p c (e i)) (b':=lvlShift p c (e j))
    (lvlShift_sub (he i) (he j)).symm
    (pole_prefix_lvlShift hL hp hh hroot hc hc0 harc (he i)).1.symm
    (pole_prefix_lvlShift hL hp hh hroot hc hc0 harc (he j)).1.symm
    (pole_prefix_lvlShift hL hp hh hroot hc hc0 harc (he i)).2.symm
  rw [H]

end Transport

section Reindex
variable {K : Type*} [Field K] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- The response only depends on the set of node values. -/
theorem quadraticResponse_of_range (a : ι → ℕ) (a' : ι' → ℕ) (ha : Function.Injective a)
    (ha' : Function.Injective a') (hr : ∀ x, (∃ i, a i = x) ↔ (∃ i, a' i = x))
    (E : ℕ → ℕ → K) (X : K) (V : ℕ → K) :
    quadraticResponse (Matrix.of fun i j : ι' => E (a' i) (a' j) + if i = j then X else 0)
        (fun i => V (a' i)) =
      quadraticResponse (Matrix.of fun i j : ι => E (a i) (a j) + if i = j then X else 0)
        (fun i => V (a i)) := by
  choose f hf using fun i => (hr (a i)).1 ⟨i, rfl⟩
  have hinj : Function.Injective f := by
    intro i j hij
    apply ha
    rw [← hf i, ← hf j, hij]
  have hsurj : Function.Surjective f := by
    intro i'
    obtain ⟨i, hi⟩ := (hr (a' i')).2 ⟨i', rfl⟩
    exact ⟨i, ha' ((hf i).trans hi)⟩
  let e : ι ≃ ι' := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have key : ∀ i, a' (e i) = a i := fun i => hf i
  refine quadraticResponse_reindex e _ _ _ _ ?_ ?_
  · intro i j
    simp [key, e.injective.eq_iff]
  · intro i
    simp [key]

end Reindex

section Core
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- **Free-long response, generic core.**  A source chain `a` (nodes `z - k_i p` of the residue
`c0` of the zone node `z = c0 + q p`) and the chain `a'` of another residue `c` in the same
unwrapped arc, whose core nodes are `c + i p` for `i < q` and possibly `i = q`: the reduced
quadratic responses `ū Q̄⁻¹ ū`, `ū = A - B L`, agree, with `A, B` the source moments. -/
theorem response_long_core (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    {h : ℕ} (hh : h<p) (hroot : 4*(h:ZMod p)=(o:ZMod p))
    {r z c c0 q : ℕ} {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (a : ι → ℕ) (k : ι → ℤ) (a' : ι' → ℕ)
    (hc : c<p) (hc0 : c0<p) (hz : z=c0+q*p) (hrz : r≤z) (hzN : z<N) (hwidth : N<r+p)
    (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0))
    (hchain : ∀ i, c+i*p<r ↔ i<q ∨ (i=q ∧ c+q*p<r))
    (ha : Function.Injective a) (hk : ∀ i, (z:ℤ)-a i=k i*p)
    (hrange : ∀ x, (∃ i, a i=x) ↔ x%p=c0 ∧ x<r)
    (ha' : Function.Injective a') (hrange' : ∀ x, (∃ i, a' i=x) ↔ x%p=c ∧ x<r) :
    cResp Fr p o a' (sourceA Fr p o a z) (sourceB Fr p o a z) =
      cResp Fr p o a (sourceA Fr p o a z) (sourceB Fr p o a z) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hzmod : z % p = c0 := by
    rw [hz, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc0]
  have hzdiv : z / p = q := by rw [hz]; exact add_mul_div_lt hc0
  have haN : ∀ i, a i < N := fun i => by have := ((hrange _).1 ⟨i, rfl⟩).2; omega
  have hamod : ∀ i, a i % p = c0 := fun i => ((hrange _).1 ⟨i, rfl⟩).1
  have hazr : ∀ i, a i < z := fun i => by have := ((hrange _).1 ⟨i, rfl⟩).2; omega
  -- source data
  set b : ι → RatFunc (ZMod p) := fun i => rfC p (red p (poleScaledEntry Fr p o (a i) z)) with hb
  set Q := poleRed Fr p o a with hQdef
  set d : RatFunc (ZMod p) := rfC p (red p (poleScaledEntry Fr p o z z)) + rfX p with hd
  set acomp : ι ⊕ Unit → ℕ := Sum.elim a (fun _ => z) with hacomp
  have hSC : sourceCompletion Q b d = poleRed Fr p o acomp := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [sourceCompletion, poleRed, hQdef, hb, hd, hacomp,
        poleScaledEntry_symm (Fr:=Fr) (p:=p) (o:=o)]
  have hQ : IsUnit Q.det := isUnit_det_poleRed a
  have hCu : IsUnit (sourceCompletion Q b d).det := by rw [hSC]; exact isUnit_det_poleRed _
  have hcomm : ∀ i j, (16:RatFunc (ZMod p)) * ((k i : RatFunc (ZMod p)) - k j) * Q i j =
      poleL Fr p o (a j) - poleL Fr p o (a i) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have H := pole_comm_red hL hp hN (haN i) (haN j) ((hamod i).trans (hamod j).symm)
        (k i - k j) (by have := hk i; have := hk j; push_cast; linarith)
      simpa [hQdef, poleRed, hij] using H
  have hsource : ∀ i, (16:RatFunc (ZMod p)) * (k i : RatFunc (ZMod p)) * b i =
      poleL Fr p o z - poleL Fr p o (a i) := fun i =>
    pole_comm_red hL hp hN (haN i) hzN ((hamod i).trans hzmod.symm) (k i) (hk i)
  have H := response_source_completion Q b (fun i => (k i : RatFunc (ZMod p)))
    (fun i => poleL Fr p o (a i)) 16 (poleL Fr p o z) d hcomm hsource hQ hCu
  -- the transported family
  let V : ℕ → RatFunc (ZMod p) := fun x =>
    sourceA Fr p o a z - sourceB Fr p o a z * poleL Fr p o x
  have hV : ∀ x, x % p = c0 → V (lvlShift p c x) = V x := fun x hx => by
    simp only [V, poleL_lvlShift hL hp hh hroot hc hc0 harc hx]
  have hdiv : ∀ x, x % p = c0 → (x / p < q ↔ ∃ i, a i = x) := by
    intro x hx
    constructor
    · intro hxq
      refine (hrange x).2 ⟨hx, ?_⟩
      have := (source_residue_core_prefix hc0 hz hrz hzN hwidth (x / p)).2 hxq
      rwa [dec_mod hx] at this
    · rintro ⟨i, rfl⟩
      have h2 := (source_residue_core_prefix hc0 hz hrz hzN hwidth (a i / p)).1
        (by rw [dec_mod (hamod i)]; exact ((hrange _).1 ⟨i, rfl⟩).2)
      exact h2
  have hfree : ∀ x, (∃ i, a' i = x) ↔
      x % p = c ∧ (x / p < q ∨ (x / p = q ∧ c + q * p < r)) := by
    intro x
    rw [hrange']
    constructor
    · rintro ⟨hx, hxr⟩
      exact ⟨hx, (hchain (x / p)).1 (by rwa [dec_mod hx])⟩
    · rintro ⟨hx, hxq⟩
      exact ⟨hx, by have := (hchain (x / p)).2 hxq; rwa [dec_mod hx] at this⟩
  have hshift_mod := lvlShift_mod (p:=p) hc
  have hmod0 : ∀ x : ℕ, (c0 + x * p) % p = c0 := fun x => by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc0]
  by_cases hq : c + q * p < r
  · -- completed case
    have hinj : Function.Injective acomp := by
      intro u v huv
      rcases u with u | u <;> rcases v with v | v <;>
        simp only [hacomp, Sum.elim_inl, Sum.elim_inr] at huv
      · rw [ha huv]
      · exact absurd huv (ne_of_lt (hazr u))
      · exact absurd huv.symm (ne_of_lt (hazr v))
      · rfl
    have hmod' : ∀ w, acomp w % p = c0 := by
      intro w; rcases w with i | u
      · exact hamod i
      · exact hzmod
    have hrng : ∀ x, (∃ w, lvlShift p c (acomp w) = x) ↔ ∃ i, a' i = x := by
      intro x
      rw [hfree]
      constructor
      · rintro ⟨w, rfl⟩
        rcases w with i | u
        · have hs := (hdiv (a i) (hamod i)).2 ⟨i, rfl⟩
          refine ⟨hshift_mod _, Or.inl ?_⟩
          unfold lvlShift
          rw [add_mul_div_lt hc]; exact hs
        · refine ⟨hshift_mod _, Or.inr ⟨?_, hq⟩⟩
          simp only [hacomp, Sum.elim_inr]
          unfold lvlShift
          rw [add_mul_div_lt hc, hzdiv]
      · rintro ⟨hx, hxq⟩
        rcases hxq with hxq | ⟨hxq, -⟩
        · obtain ⟨i, hi⟩ := (hdiv (c0 + (x / p) * p) (hmod0 _)).1 (by
            rw [add_mul_div_lt hc0]; exact hxq)
          refine ⟨Sum.inl i, ?_⟩
          simp only [hacomp, Sum.elim_inl, hi]
          unfold lvlShift
          rw [add_mul_div_lt hc0]; exact dec_mod hx
        · refine ⟨Sum.inr (), ?_⟩
          simp only [hacomp, Sum.elim_inr]
          unfold lvlShift
          rw [hzdiv, ← hxq]; exact dec_mod hx
    have hinj2 : Function.Injective (fun w => lvlShift p c (acomp w)) := by
      intro u v huv
      apply hinj
      have h1 := dec_mod (hmod' u)
      have h2 := dec_mod (hmod' v)
      simp only [lvlShift] at huv
      have : acomp u / p = acomp v / p :=
        Nat.eq_of_mul_eq_mul_right hp0 (Nat.add_left_cancel huv)
      rw [← h1, ← h2, this]
    have step1 := quadraticResponse_of_range (K := RatFunc (ZMod p))
      (fun w => lvlShift p c (acomp w)) a' hinj2 ha' hrng
      (fun x y => rfC p (red p (poleScaledEntry Fr p o x y))) (rfX p) V
    have step2 : quadraticResponse (poleRed Fr p o (fun w => lvlShift p c (acomp w)))
        (fun w => V (lvlShift p c (acomp w))) =
        quadraticResponse (poleRed Fr p o acomp) (fun w => V (acomp w)) := by
      rw [poleRed_lvlShift hL hp hh hroot hc hc0 harc acomp hmod']
      congr 1
      funext w
      exact hV _ (hmod' w)
    have step3 : (fun w => V (acomp w)) = Sum.elim
        (fun i => (poleL Fr p o z - ∑ k, (Q⁻¹ *ᵥ b) k * poleL Fr p o (a k)) -
          (1 - ∑ k, (Q⁻¹ *ᵥ b) k) * poleL Fr p o (a i))
        (fun _ => (poleL Fr p o z - ∑ k, (Q⁻¹ *ᵥ b) k * poleL Fr p o (a k)) -
          (1 - ∑ k, (Q⁻¹ *ᵥ b) k) * poleL Fr p o z) := by
      funext w; rcases w with i | u <;> rfl
    unfold cResp
    refine Eq.trans step1 (Eq.trans step2 ?_)
    rw [step3, ← hSC]
    exact H
  · -- plain relabelling case
    have hinj2 : Function.Injective (fun i => lvlShift p c (a i)) := by
      intro u v huv
      apply ha
      have h1 := dec_mod (hamod u)
      have h2 := dec_mod (hamod v)
      simp only [lvlShift] at huv
      have : a u / p = a v / p := Nat.eq_of_mul_eq_mul_right hp0 (Nat.add_left_cancel huv)
      rw [← h1, ← h2, this]
    have hrng : ∀ x, (∃ i, lvlShift p c (a i) = x) ↔ ∃ i, a' i = x := by
      intro x
      rw [hfree]
      constructor
      · rintro ⟨i, rfl⟩
        have hs := (hdiv (a i) (hamod i)).2 ⟨i, rfl⟩
        refine ⟨hshift_mod _, Or.inl ?_⟩
        unfold lvlShift
        rw [add_mul_div_lt hc]; exact hs
      · rintro ⟨hx, hxq⟩
        rcases hxq with hxq | ⟨-, hxq⟩
        · obtain ⟨i, hi⟩ := (hdiv (c0 + (x / p) * p) (hmod0 _)).1 (by
            rw [add_mul_div_lt hc0]; exact hxq)
          refine ⟨i, ?_⟩
          rw [hi]
          unfold lvlShift
          rw [add_mul_div_lt hc0]; exact dec_mod hx
        · exact absurd hxq hq
    have step1 := quadraticResponse_of_range (K := RatFunc (ZMod p))
      (fun i => lvlShift p c (a i)) a' hinj2 ha' hrng
      (fun x y => rfC p (red p (poleScaledEntry Fr p o x y))) (rfX p) V
    have step2 : quadraticResponse (poleRed Fr p o (fun i => lvlShift p c (a i)))
        (fun i => V (lvlShift p c (a i))) =
        quadraticResponse (poleRed Fr p o a) (fun i => V (a i)) := by
      rw [poleRed_lvlShift hL hp hh hroot hc hc0 harc a hamod]
      congr 1
      funext i
      exact hV _ (hamod i)
    unfold cResp
    exact Eq.trans step1 step2

end Core

section Actual
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The node map of the actual chain of `z`: injective, onto the core nodes of the residue. -/
theorem chain_family {r z : ℕ} (hz : r ≤ z) :
    Function.Injective (fun i : ChainIndex p r z => (chainNode i).val) ∧
    (∀ x, (∃ i : ChainIndex p r z, (chainNode i).val = x) ↔ x % p = z % p ∧ x < r) ∧
    (∀ i : ChainIndex p r z, (z : ℤ) - (chainNode i).val = i.val * p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact chainNode_injective (Fact.out : p.Prime).pos (Fin.ext hij)
  · intro x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨chainNode_mod i, (chainNode i).isLt⟩
    · rintro ⟨hx, hxr⟩
      obtain ⟨i, hi⟩ := chain_image_of_mod (p := p) hz ⟨x, hxr⟩ hx
      exact ⟨i, by rw [hi]⟩
  · intro i
    rw [chainNode_cast]; ring

/-- **`response_long_eq`, free residues.**  For a long residue `c` in the same unwrapped arc as the
source residue `c0` of `z = c0 + q p` (zone node, `r ≤ z < N < r + p`) and not occupied by any
node of `[r, N)`, the reduced response of the actual chain of `c` (here: of any `z' ≥ r` with
`z' ≡ c`) equals the source response `c̄_C`. -/
theorem response_long_eq_free (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    {h : ℕ} (hh : h<p) (hroot : 4*(h:ZMod p)=(o:ZMod p))
    {r z z' c c0 q : ℕ} (hc : c<p) (hc0 : c0<p) (hz : z=c0+q*p) (hrz : r≤z) (hzN : z<N)
    (hwidth : N<r+p) (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0))
    (hfree : ∀ k, r≤k → k<N → k%p≠c) (hz' : r≤z') (hz'c : z'%p=c) :
    cResp Fr p o (fun i : ChainIndex p r z' => (chainNode i).val)
        (sourceA Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z)
        (sourceB Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z) =
      cResp Fr p o (fun i : ChainIndex p r z => (chainNode i).val)
        (sourceA Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z)
        (sourceB Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z) := by
  have hzmod : z % p = c0 := by
    rw [hz, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc0]
  obtain ⟨hi, hr, hk⟩ := chain_family (p := p) hrz
  obtain ⟨hi', hr', -⟩ := chain_family (p := p) hz'
  refine response_long_core hL hp hN hh hroot _ (fun i : ChainIndex p r z => i.val) _ hc hc0 hz
    hrz hzN hwidth harc ?_ hi hk (by simpa only [hzmod] using hr) hi'
    (by simpa only [hz'c] using hr')
  intro i
  exact free_residue_core_prefix hc hc0 hz hrz hzN hfree i

/-- **`response_long_eq`, occupied residues of the same period level.**  If `w = c + q p` is a zone
node with the same period index `q` as `z`, the chain of `w` has the source response. -/
theorem response_long_eq_occupied (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p)
    {h : ℕ} (hh : h<p) (hroot : 4*(h:ZMod p)=(o:ZMod p))
    {r z w c c0 q : ℕ} (hc : c<p) (hc0 : c0<p) (hz : z=c0+q*p) (hw : w=c+q*p)
    (hrz : r≤z) (hzN : z<N) (hrw : r≤w) (hwN : w<N)
    (hwidth : N<r+p) (harc : (c<h ∧ c0<h) ∨ (h≤c ∧ h≤c0)) :
    cResp Fr p o (fun i : ChainIndex p r w => (chainNode i).val)
        (sourceA Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z)
        (sourceB Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z) =
      cResp Fr p o (fun i : ChainIndex p r z => (chainNode i).val)
        (sourceA Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z)
        (sourceB Fr p o (fun i : ChainIndex p r z => (chainNode i).val) z) := by
  have hzmod : z % p = c0 := by
    rw [hz, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc0]
  have hwmod : w % p = c := by
    rw [hw, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  obtain ⟨hi, hr, hk⟩ := chain_family (p := p) hrz
  obtain ⟨hi', hr', -⟩ := chain_family (p := p) hrw
  refine response_long_core hL hp hN hh hroot _ (fun i : ChainIndex p r z => i.val) _ hc hc0 hz
    hrz hzN hwidth harc ?_ hi hk (by simpa only [hzmod] using hr) hi'
    (by simpa only [hwmod] using hr')
  intro i
  have := source_residue_core_prefix hc hw hrw hwN hwidth i
  rw [this]
  constructor
  · exact Or.inl
  · rintro (h1 | ⟨-, h2⟩)
    · exact h1
    · omega

end Actual
#print axioms response_long_eq_free
#print axioms response_long_eq_occupied
end CatalanCore.Arith.Hybrid
