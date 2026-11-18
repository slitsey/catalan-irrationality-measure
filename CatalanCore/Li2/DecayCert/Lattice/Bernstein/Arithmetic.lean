module
public import CatalanCore.Li2.DecayCert.Rounded.Arithmetic
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert
namespace BernsteinGrid

/-- Endpoints are numerators; no dyadic scale is multiplied inside integer hot loops. -/
def Encloses (S : ℤ) (b : ℤ×ℤ) (x : ℚ) : Prop :=
  (b.1:ℚ)≤(S:ℚ)*x ∧ (S:ℚ)*x≤(b.2:ℚ)

theorem ediv_mul_le (a D : ℤ) (hD : 0<D) : (a/D)*D≤a := by
  have hr := Int.emod_nonneg a hD.ne'
  have he := Int.emod_add_ediv_mul a D
  omega

theorem le_neg_ediv_mul (a D : ℤ) (hD : 0<D) : a≤(-((-a)/D))*D := by
  have h := ediv_mul_le (-a) D hD
  nlinarith

theorem rounded_bounds (S D lo hi : ℤ) (x : ℚ) (hD : 0<D)
    (hl : (lo:ℚ)≤(D:ℚ)*((S:ℚ)*x))
    (hu : (D:ℚ)*((S:ℚ)*x)≤(hi:ℚ)) :
    Encloses S (lo/D,-((-hi)/D)) x := by
  have hd : (0:ℚ)<(D:ℚ) := by exact_mod_cast hD
  have hli : ((lo/D:ℤ):ℚ)*(D:ℚ)≤(lo:ℚ) := by exact_mod_cast ediv_mul_le lo D hD
  have hui : (hi:ℚ)≤((-((-hi)/D):ℤ):ℚ)*(D:ℚ) := by exact_mod_cast le_neg_ediv_mul hi D hD
  constructor
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      ((lo/D:ℤ):ℚ)*(D:ℚ)≤(lo:ℚ) := hli
      _≤(D:ℚ)*((S:ℚ)*x) := hl
      _=((S:ℚ)*x)*(D:ℚ) := by ring
  · apply (mul_le_mul_iff_left₀ hd).mp
    calc
      ((S:ℚ)*x)*(D:ℚ)=(D:ℚ)*((S:ℚ)*x) := by ring
      _≤(hi:ℚ) := hu
      _≤((-((-hi)/D):ℤ):ℚ)*(D:ℚ) := hui

theorem mul_const_bounds (c a b x : ℚ) (h : a≤x ∧ x≤b) :
    min (c*a) (c*b)≤c*x ∧ c*x≤max (c*a) (c*b) := by
  by_cases hc : 0≤c
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left h.1 hc),
      (mul_le_mul_of_nonneg_left h.2 hc).trans (le_max_right _ _)⟩
  · have hc' : c≤0 := le_of_not_ge hc
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left h.2 hc'),
      (mul_le_mul_of_nonpos_left h.1 hc').trans (le_max_left _ _)⟩

theorem mul_int_bounds (S A : ℤ) (b : ℤ×ℤ) (x : ℚ)
    (hb : Encloses S b x) :
    (min (A*b.1) (A*b.2):ℤ)≤(A:ℚ)*((S:ℚ)*x) ∧
    (A:ℚ)*((S:ℚ)*x)≤(max (A*b.1) (A*b.2):ℤ) := by
  have h := mul_const_bounds (A:ℚ) (b.1:ℚ) (b.2:ℚ) ((S:ℚ)*x) hb
  norm_cast at h ⊢

def affineBoxRow (m k : ℕ) (A B D c : ℤ) (u v : ℤ×ℤ) : ℤ×ℤ :=
  let lo := ((m-k:ℕ):ℤ)*min (A*u.1) (A*u.2)+(k:ℤ)*min (B*v.1) (B*v.2)
  let hi := ((m-k:ℕ):ℤ)*max (A*u.1) (A*u.2)+(k:ℤ)*max (B*v.1) (B*v.2)
  (lo/((m:ℤ)*D)+c,-((-hi)/((m:ℤ)*D))+c)

theorem affineBoxRow_sound (S : ℤ) (m k : ℕ) (A B D c : ℤ)
    (u v : ℤ×ℤ) (x y : ℚ) (hS : 0<S) (hm : 0<m) (hD : 0<D)
    (hu : Encloses S u x) (hv : Encloses S v y) :
    Encloses S (affineBoxRow m k A B D c u v)
      ((c:ℚ)/(S:ℚ)+
        (((m-k:ℕ):ℚ)*(A:ℚ)*x+(k:ℚ)*(B:ℚ)*y)/((m:ℚ)*(D:ℚ))) := by
  let lo := ((m-k:ℕ):ℤ)*min (A*u.1) (A*u.2)+(k:ℤ)*min (B*v.1) (B*v.2)
  let hi := ((m-k:ℕ):ℤ)*max (A*u.1) (A*u.2)+(k:ℤ)*max (B*v.1) (B*v.2)
  let value : ℚ := (((m-k:ℕ):ℚ)*(A:ℚ)*x+(k:ℚ)*(B:ℚ)*y)/((m:ℚ)*(D:ℚ))
  have hux := mul_int_bounds S A u x hu
  have hvy := mul_int_bounds S B v y hv
  have hl := add_le_add
    (mul_le_mul_of_nonneg_left hux.1 (Nat.cast_nonneg (m-k): (0:ℚ)≤((m-k:ℕ):ℚ)))
    (mul_le_mul_of_nonneg_left hvy.1 (Nat.cast_nonneg k : (0:ℚ)≤(k:ℚ)))
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left hux.2 (Nat.cast_nonneg (m-k): (0:ℚ)≤((m-k:ℕ):ℚ)))
    (mul_le_mul_of_nonneg_left hvy.2 (Nat.cast_nonneg k : (0:ℚ)≤(k:ℚ)))
  have hmz : (0:ℤ)<(m:ℤ) := by exact_mod_cast hm
  have hmQ : (0:ℚ)<(m:ℚ) := by exact_mod_cast hm
  have hDQ : (0:ℚ)<(D:ℚ) := by exact_mod_cast hD
  have hden : (m:ℚ)*(D:ℚ)≠0 := (mul_pos hmQ hDQ).ne'
  have he : (m:ℚ)*(D:ℚ)*((S:ℚ)*value)=
      ((m-k:ℕ):ℚ)*((A:ℚ)*((S:ℚ)*x))+(k:ℚ)*((B:ℚ)*((S:ℚ)*y)) := by
    dsimp only [value]
    field_simp
    <;> ring
  have hlo : (lo:ℚ)≤(((m:ℤ)*D:ℤ):ℚ)*((S:ℚ)*value) := by
    push_cast
    rw [he]
    simpa only [lo,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hl
  have hhi : (((m:ℤ)*D:ℤ):ℚ)*((S:ℚ)*value)≤(hi:ℚ) := by
    push_cast
    rw [he]
    simpa only [hi,Int.cast_add,Int.cast_mul,Int.cast_natCast] using hh
  have hr := rounded_bounds S ((m:ℤ)*D) lo hi value (mul_pos hmz hD) hlo hhi
  have hs : (S:ℚ)≠0 := by exact_mod_cast hS.ne'
  have hc : (S:ℚ)*((c:ℚ)/(S:ℚ)+value)=(c:ℚ)+(S:ℚ)*value := by
    field_simp
    <;> ring
  change Encloses S (lo/((m:ℤ)*D)+c,-((-hi)/((m:ℤ)*D))+c) ((c:ℚ)/(S:ℚ)+value)
  dsimp only [Encloses] at hr ⊢
  rw [hc]
  push_cast at hr ⊢
  exact ⟨by linarith [hr.1],by linarith [hr.2]⟩

#print axioms rounded_bounds
#print axioms mul_int_bounds
#print axioms affineBoxRow_sound
end BernsteinGrid
end CatalanCore.Li2.DecayCert
