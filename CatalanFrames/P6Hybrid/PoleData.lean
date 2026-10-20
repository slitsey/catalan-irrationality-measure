module
public import CatalanCore.Arith.Hybrid.PeriodicEntries
public import CatalanFrames.P6Hybrid.Level

@[expose] public section
open CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open CatalanFrames.P6

def p6Singular (p : ℕ) (t : ℤ) : Prop :=
  (p:ℤ)∣t ∨ (p:ℤ)∣3*t-2 ∨ (p:ℤ)∣2*t-1

lemma linear_pole_periodic (p a b t j : ℤ) :
    p∣a*(t+j*p)-b ↔ p∣a*t-b := by
  have he : a*(t+j*p)-b=(a*t-b)+(a*j)*p := by ring
  rw [he]
  constructor
  · rintro ⟨k,hk⟩;exact ⟨k-a*j,by linear_combination hk⟩
  · rintro ⟨k,hk⟩;exact ⟨k+a*j,by linear_combination hk⟩

lemma p6Singular_periodic (p : ℕ) (t j : ℤ) :
    p6Singular p (t+j*p) ↔ p6Singular p t := by
  unfold p6Singular
  have h0 := linear_pole_periodic p 1 0 t j
  have h3 := linear_pole_periodic p 3 2 t j
  have h2 := linear_pole_periodic p 2 1 t j
  simp only [one_mul,sub_zero] at h0
  rw [h0,h3,h2]

variable {p N : ℕ} [Fact p.Prime]

lemma p6_regular_indices {k : ℕ} (hk : 1≤k) (hs : ¬p6Singular p k) :
    ¬p∣k ∧ ¬p∣3*k-2 ∧ ¬p∣2*k-1 := by
  have e3 : ((3*k-2:ℕ):ℤ)=3*(k:ℤ)-2 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  have e2 : ((2*k-1:ℕ):ℤ)=2*(k:ℤ)-1 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  refine ⟨?_,?_,?_⟩
  · intro h;apply hs;exact Or.inl (by exact_mod_cast h)
  · intro h;apply hs;apply Or.inr;apply Or.inl;rw [←e3];exact_mod_cast h
  · intro h;apply hs;apply Or.inr;apply Or.inr;rw [←e2];exact_mod_cast h

lemma regular_inverse_good {n : ℕ} (h : ¬p∣n) :
    Good p (1/(n:ℚ)) ((n:ZMod p)⁻¹) := by
  have hn : (n:ZMod p)≠0 := by rwa [Ne,ZMod.natCast_eq_zero_iff]
  simpa only [one_div] using (Good.one (ℓ:=p)).div (Good.natCast n) hn

lemma p6_regular_delta {k : ℕ} (hk : 1≤k) (hs : ¬p6Singular p k) :
    p6Frame.Delta k∈S p := by
  obtain ⟨h1,h3,h2⟩:=p6_regular_indices hk hs
  have g1:=regular_inverse_good h1
  have g3:=regular_inverse_good h3
  have g2:=regular_inverse_good h2
  have H:=((g1.add ((Good.ofNat (ℓ:=p) 6).mul g3)).sub
    ((Good.ofNat (ℓ:=p) 6).mul g2)).mem
  have e3 : ((3*k-2:ℕ):ℚ)=3*(k:ℚ)-2 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  have e2 : ((2*k-1:ℕ):ℚ)=2*(k:ℚ)-1 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  convert H using 1
  rw [Delta_eq k hk,e3,e2]
  ring

lemma p6_regular_dsq {k : ℕ} (hk : 1≤k) (hs : ¬p6Singular p k) :
    p6Frame.Dsq k∈S p := by
  obtain ⟨h1,h3,h2⟩:=p6_regular_indices hk hs
  have g1:=regular_inverse_good h1
  have g3:=regular_inverse_good h3
  have g2:=regular_inverse_good h2
  have H:=(((g1.pow' 2).add ((Good.ofNat (ℓ:=p) 18).mul (g3.pow' 2))).sub
    ((Good.ofNat (ℓ:=p) 12).mul (g2.pow' 2))).mem
  have e3 : ((3*k-2:ℕ):ℚ)=3*(k:ℚ)-2 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  have e2 : ((2*k-1:ℕ):ℚ)=2*(k:ℚ)-1 := by rw [Nat.cast_sub (by omega)];push_cast;ring
  convert H using 1
  rw [Dsq_eq k hk,e3,e2]
  simp only [div_pow,one_pow]
  ring

/-- Actual P6 data for the frame-free periodic-chain theorem. -/
noncomputable def p6PoleData (hp : 5≤p) (hN : 3*N<p^2) :
    Periodic.PoleData p6Frame p N where
  singular := p6Singular p
  periodic := p6Singular_periodic p
  norm_mem := (Good.natCast (ℓ:=p) 36).mem
  norm_ne := by
    have h36 : (36:ZMod p)≠0 := by
      rw [←Nat.cast_ofNat (R:=ZMod p) (n:=36),Ne,ZMod.natCast_eq_zero_iff]
      intro hd
      have pp : p.Prime:=Fact.out
      have h6 : p∣6 := (pp.dvd_mul.mp (by simpa using hd : p∣6*6)).elim id id
      have hh : p∣2 ∨ p∣3 := pp.dvd_mul.mp (by simpa using h6 : p∣2*3)
      rcases hh with h|h <;> have := Nat.le_of_dvd (by norm_num) h <;> omega
    simpa [p6Frame,red] using h36
  delta_mem := by
    intro k hk hkN
    apply mem_S.mpr
    simpa only [pow_one] using Basic.mem_locRing.mp (p6_hD p 1 N k hN hk hkN.le)
  dsq_mem := by
    intro k hk hkN
    apply mem_S.mpr
    simpa only [Nat.mul_one] using Basic.mem_locRing.mp (p6_hD2 p 1 N k hN hk hkN.le)
  regular_delta := fun k hk _ hs=>p6_regular_delta hk hs
  regular_dsq := fun k hk _ hs=>p6_regular_dsq hk hs

end CatalanFrames.P6Hybrid
