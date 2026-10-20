module
public import CatalanCore.Arith.Hybrid.RegularLoewner
public import CatalanCore.Arith.Hybrid.LamPoleData
public import CatalanCore.Arith.Hybrid.PeriodicChain
@[expose] public section
open Finset CatalanCore
namespace CatalanCore.Arith.Hybrid
open ChainClasses
variable {p o : ℕ} [Fact p.Prime] {Fr : Frame}

noncomputable def poleDelta (Fr : Frame) (p o k : ℕ) : ℚ :=
  Fr.Delta k-regularDelta p o k
noncomputable def poleDsq (Fr : Frame) (p o k : ℕ) : ℚ :=
  Fr.Dsq k-regularDsq p o k

lemma poleDelta_support (hL : LamData Fr o) {k : ℕ} (hk : 1≤k)
    (hs : ¬Singular p o k) : poleDelta Fr p o k=0 := by
  have h1 : ¬(p:ℤ)∣k:=fun h=>hs (Or.inl h)
  have h4 : ¬(p:ℤ)∣4*(k:ℤ)-o:=fun h=>hs (Or.inr h)
  rw [poleDelta,hL.delta_eq k hk]
  simp only [regularDelta,regularInverse,if_neg h1,if_neg h4,Int.cast_sub,Int.cast_mul,
    Int.cast_natCast,Int.cast_ofNat,div_eq_mul_inv]
  ring

lemma poleDsq_support (hL : LamData Fr o) {k : ℕ} (hk : 1≤k)
    (hs : ¬Singular p o k) : poleDsq Fr p o k=0 := by
  have h1 : ¬(p:ℤ)∣k:=fun h=>hs (Or.inl h)
  have h4 : ¬(p:ℤ)∣4*(k:ℤ)-o:=fun h=>hs (Or.inr h)
  rw [poleDsq,hL.dsq_eq k hk]
  simp only [regularDsq,regularInverse,if_neg h1,if_neg h4,Int.cast_sub,Int.cast_mul,
    Int.cast_natCast,Int.cast_ofNat,div_eq_mul_inv,inv_pow]
  ring

/-- The exact singular model of the scaled core. Its difference from the
actual same-residue core starts at order p^2. -/
noncomputable def poleScaledEntry (Fr : Frame) (p o a b : ℕ) : ℚ :=
  (p:ℚ)^2*(Fr.Mn a b-regularLoewner Fr.norm p o a b)

noncomputable def polePrefix (Fr : Frame) (p o a : ℕ) : ℚ :=
  ∑k∈Icc 1 a,poleDelta Fr p o k

noncomputable def poleSquarePrefix (Fr : Frame) (p o a : ℕ) : ℚ :=
  ∑k∈Icc 1 a,poleDsq Fr p o k

lemma polePrefix_sub {a b : ℕ} (hab : a≤b) :
    polePrefix Fr p o b-polePrefix Fr p o a=∑k∈Ioc a b,poleDelta Fr p o k := by
  have he (n : ℕ) : Icc 1 n=Ioc 0 n := by ext k;simp only [mem_Icc,mem_Ioc];omega
  unfold polePrefix
  rw [he,he,←Finset.sum_Ioc_consecutive _ (Nat.zero_le a) hab]
  ring

theorem polePrefix_nocut (hL : LamData Fr o) {a b : ℕ}
    (hab : a≤b) (hc : NoCut (Singular p o) a b) :
    polePrefix Fr p o a=polePrefix Fr p o b :=
  Periodic.prefix_nocut (N:=b+1) (poleDelta Fr p o) (Singular p o)
    hab (by omega) (fun k hk _ hs=>poleDelta_support hL hk hs) hc

theorem poleSquarePrefix_nocut (hL : LamData Fr o) {a b : ℕ}
    (hab : a≤b) (hc : NoCut (Singular p o) a b) :
    poleSquarePrefix Fr p o a=poleSquarePrefix Fr p o b :=
  Periodic.prefix_nocut (N:=b+1) (poleDsq Fr p o) (Singular p o)
    hab (by omega) (fun k hk _ hs=>poleDsq_support hL hk hs) hc

lemma poleScaledEntry_ordered {a b : ℕ} (hab : a<b) :
    poleScaledEntry Fr p o a b=
      (p:ℚ)^2/Fr.norm/(b-a)*(polePrefix Fr p o b-polePrefix Fr p o a) := by
  rw [polePrefix_sub hab.le]
  unfold poleScaledEntry Frame.Mn regularLoewner
  simp only [if_neg hab.ne,min_eq_left hab.le,max_eq_right hab.le,poleDelta,
    Finset.sum_sub_distrib]
  ring

lemma poleScaledEntry_diagonal (a : ℕ) :
    poleScaledEntry Fr p o a a=-(p:ℚ)^2/Fr.norm*poleSquarePrefix Fr p o a := by
  unfold poleScaledEntry Frame.Mn regularLoewner poleSquarePrefix
  simp only [ite_true,poleDsq,Finset.sum_sub_distrib]
  ring

lemma poleScaledEntry_symm (a b : ℕ) :
    poleScaledEntry Fr p o a b=poleScaledEntry Fr p o b a := by
  unfold poleScaledEntry
  rw [Mn_symm,regularLoewner_symm]

/-- Exact, characteristic-zero transport. No choice of a residue-field lift
or differentiation of an inverse matrix is required. -/
theorem poleScaledEntry_transport {a b a' b' : ℕ}
    (hd : (b:ℤ)-a=(b':ℤ)-a')
    (hVa : polePrefix Fr p o a=polePrefix Fr p o a')
    (hVb : polePrefix Fr p o b=polePrefix Fr p o b')
    (hWa : poleSquarePrefix Fr p o a=poleSquarePrefix Fr p o a') :
    poleScaledEntry Fr p o a b=poleScaledEntry Fr p o a' b' := by
  rcases lt_trichotomy a b with h|rfl|h
  · have h' : a'<b' := by omega
    have he : (b:ℚ)-a=(b':ℚ)-a' := by exact_mod_cast hd
    rw [poleScaledEntry_ordered h,poleScaledEntry_ordered h',he,hVa,hVb]
  · have he : b'=a' := by omega
    subst b'
    rw [poleScaledEntry_diagonal,poleScaledEntry_diagonal,hWa]
  · have h' : b'<a' := by omega
    have he : (a:ℚ)-b=(a':ℚ)-b' := by
      have H : (a:ℤ)-b=(a':ℤ)-b' := by omega
      exact_mod_cast H
    rw [poleScaledEntry_symm a b,poleScaledEntry_symm a' b',
      poleScaledEntry_ordered h,poleScaledEntry_ordered h',he,hVa,hVb]

theorem poleScaledEntry_second_order (hL : LamData Fr o) (hp : 5≤p)
    {a b : ℕ} (ha : a<p*p) (hb : b<p*p) (hc : a%p=b%p) :
    Good p (((p:ℚ)^2*Fr.Mn a b-poleScaledEntry Fr p o a b)/(p:ℚ)) 0 := by
  have h4:=four_ne_zmod p hp
  have h16 : (16:ZMod p)≠0 := by convert mul_ne_zero h4 h4 using 1 <;> norm_num
  have hn : Good p Fr.norm (16:ZMod p) := by rw [hL.norm_eq];exact Good.ofNat 16
  have H:=good_scaled_regularLoewner_same_class hn h16 o h4 ha hb hc
  apply H.congr'
  have hp0 : (p:ℚ)≠0:=by exact_mod_cast (Fact.out:p.Prime).ne_zero
  unfold poleScaledEntry
  field_simp
  <;> ring
end CatalanCore.Arith.Hybrid
