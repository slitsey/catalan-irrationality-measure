module
public import CatalanFrames.Fifths.ContourInstances
public import CatalanFrames.Fifths.Roots
@[expose] public section
open CatalanCore
namespace CatalanFrames.Fifths
/-- Arithmetic frame identities with modulus and offset explicit. This is not yet ContentData. -/
structure ShiftData (Fr : Frame) (M u : ℕ) : Prop where
  hM : 2 ≤ M
  hu0 : 1 ≤ u
  hu1 : u < M
  norm_eq : Fr.norm = (M : ℚ)^2
  delta : ∀ k, 0 < k → Fr.Delta k = 1/(k : ℚ)-(M : ℚ)/((M*k-u : ℕ) : ℚ)
  dsq : ∀ k, 0 < k → Fr.Dsq k = 1/(k : ℚ)^2-(M : ℚ)^2/((M*k-u : ℕ) : ℚ)^2

lemma cast_linear {M u k : ℕ} (hu : u < M) (hk : 0 < k) :
    ((M*k-u : ℕ) : ℚ) = (M : ℚ)*k-u := by
  have hmk : M ≤ M*k := by simpa using Nat.mul_le_mul_left M (show 1 ≤ k by omega)
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

lemma ShiftData.of_frame {M u : ℕ} (hM : 2 ≤ M) (hu0 : 1 ≤ u) (hu1 : u < M)
    (s xs δ0 : ℚ) (n0 : ℕ) (hs : s = ((M : ℚ)-u)/M) (hs0 : 0 < s) (hs1 : s < 1) :
    ShiftData (Thirds.thirdsFrame s ((M : ℚ)^2) xs δ0 n0 hs0 hs1 (by positivity)) M u where
  hM := hM
  hu0 := hu0
  hu1 := hu1
  norm_eq := rfl
  delta := by
    intro k hk
    have hMp : 0 < (M : ℚ) := by exact_mod_cast (show 0 < M by omega)
    have hshift_eq : (k : ℚ)-1+s = ((M : ℚ)*k-u)/M := by
      rw [hs]
      field_simp [hMp.ne']
      <;> ring
    rw [Thirds.Delta_eq,cast_linear hu1 hk,hshift_eq]
    simp only [one_div_div]
  dsq := by
    intro k hk
    have hMp : 0 < (M : ℚ) := by exact_mod_cast (show 0 < M by omega)
    have hshift_eq : (k : ℚ)-1+s = ((M : ℚ)*k-u)/M := by
      rw [hs]
      field_simp [hMp.ne']
      <;> ring
    rw [Thirds.Dsq_eq,cast_linear hu1 hk,hshift_eq]
    simp only [div_pow,one_div_div]
/-- A sharper growth choice avoids the unnecessary false6≤5 corner at N=1. -/
lemma phi_le_sharp {M u k N : ℕ} (hu0 : 1 ≤ u) (hk : k ≤ N) :
    k*(M*k-u) ≤ N*(M*N-1) := by
  have hm := Nat.mul_le_mul_left M hk
  have hd : M*k-u ≤ M*N-1 := by omega
  exact Nat.mul_le_mul hk hd
lemma sharp_Ebd_cubic {M : ℕ} (hM : 1 ≤ M) (N : ℕ) :
    N*(M*N-1)+N ≤ M*N^3 := by
  cases N with
  | zero => simp
  | succ n =>
    have hm : 1 ≤ M*(n+1) := by nlinarith
    have he := Nat.sub_add_cancel hm
    have hEq : (n+1)*(M*(n+1)-1)+(n+1) = M*(n+1)^2 := by
      calc (n+1)*(M*(n+1)-1)+(n+1) = (n+1)*((M*(n+1)-1)+1) := by ring
        _ = (n+1)*(M*(n+1)) := by rw [he]
        _ = M*(n+1)^2 := by ring
    rw [hEq]
    exact Nat.mul_le_mul_left M (Nat.pow_le_pow_right (by omega) (by omega : 2 ≤ 3))

/-- Safe finite-prime clearer for2,3,5; its localization proof remains an explicit next gate. -/
def small5 (h : ℕ) : ℕ :=
  5*2^Nat.log 2 (5*h)*3^Nat.log 3 (5*h)*5^Nat.log 5 (5*h)
lemma small5_poly (h : ℕ) : small5 h ≤ 625*(h+1)^3 := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp [small5]
  · have h2 := Nat.pow_log_le_self 2 (by omega : 5*h ≠ 0)
    have h3 := Nat.pow_log_le_self 3 (by omega : 5*h ≠ 0)
    have h5 := Nat.pow_log_le_self 5 (by omega : 5*h ≠ 0)
    unfold small5
    calc 5*2^Nat.log 2 (5*h)*3^Nat.log 3 (5*h)*5^Nat.log 5 (5*h)
        ≤ 5*(5*h)*(5*h)*(5*h) := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 5 h2) h3) h5
      _ ≤ 625*(h+1)^3 := by nlinarith

lemma fifths1_data : ShiftData fifths1 5 4 := by
  simpa only [fifths1,Nat.cast_ofNat,show (5 : ℚ)^2 = 25 by norm_num] using
    (ShiftData.of_frame (M := 5) (u := 4) (by norm_num) (by norm_num) (by norm_num)
      (1/5) (3/5) (1/4) 1 (by norm_num) (by norm_num) (by norm_num))
lemma fifths2_data : ShiftData fifths2 5 3 := by
  simpa only [fifths2,Nat.cast_ofNat,show (5 : ℚ)^2 = 25 by norm_num] using
    (ShiftData.of_frame (M := 5) (u := 3) (by norm_num) (by norm_num) (by norm_num)
      (2/5) (7/10) (1/4) 1 (by norm_num) (by norm_num) (by norm_num))
lemma fifths3_data : ShiftData fifths3 5 2 := by
  simpa only [fifths3,Nat.cast_ofNat,show (5 : ℚ)^2 = 25 by norm_num] using
    (ShiftData.of_frame (M := 5) (u := 2) (by norm_num) (by norm_num) (by norm_num)
      (3/5) (3/10) (1/4) 0 (by norm_num) (by norm_num) (by norm_num))
lemma fifths4_data : ShiftData fifths4 5 1 := by
  simpa only [fifths4,Nat.cast_ofNat,show (5 : ℚ)^2 = 25 by norm_num] using
    (ShiftData.of_frame (M := 5) (u := 1) (by norm_num) (by norm_num) (by norm_num)
      (4/5) (2/5) (1/4) 0 (by norm_num) (by norm_num) (by norm_num))
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_data
#print axioms CatalanFrames.Fifths.fifths2_data
#print axioms CatalanFrames.Fifths.fifths3_data
#print axioms CatalanFrames.Fifths.fifths4_data
#print axioms CatalanFrames.Fifths.sharp_Ebd_cubic
#print axioms CatalanFrames.Fifths.small5_poly
