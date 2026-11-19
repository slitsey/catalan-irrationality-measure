module
public import CatalanCore.Li2.Content.Primitive
public import CatalanCore.Li2.Content.Rate
public import CatalanCore.Li2.Uniform.Candidate
public import CatalanCore.Li2.DecayCert.TableSound
public import CatalanCore.Li2.NV.Band
public import CatalanCore.Li2.NVMod.Assembly
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2
noncomputable section

theorem rational_input (a b : ℤ) (hb : 0<b) (ha : a≠0) (h2 : 2*|a|≤b) :
    |a|<b ∧ NVMod.Allowed ((a:ℚ)/b) ∧
      (((a:ℚ)/b:ℚ):ℝ)=(a:ℝ)/b ∧ |(((a:ℚ)/b:ℚ):ℝ)|<1 ∧
      Int.sign (((a:ℚ)/b:ℚ).num)=Int.sign a ∧
      Real.log (1/|(((a:ℚ)/b:ℚ):ℝ)|)=Real.log ((b:ℝ)/|(a:ℝ)|) := by
  have hapos : 0 < |a| := abs_pos.mpr ha
  have hab : |a|<b := by omega
  have hbQ : (0:ℚ)<b := by exact_mod_cast hb
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have h2Q : 2*|(a:ℚ)|≤(b:ℚ) := by exact_mod_cast h2
  have hhalf : |(a:ℚ)/b|≤1/2 := by
    rw [abs_div,abs_of_pos hbQ]
    apply (div_le_iff₀ hbQ).mpr
    linarith
  have hz0 : (a:ℚ)/b≠0 := div_ne_zero (by exact_mod_cast ha) (ne_of_gt hbQ)
  have hz1 : (a:ℚ)/b≠1 := by
    intro hh
    rw [hh] at hhalf
    norm_num at hhalf
  have hZ : (a:ℚ)/b∉NVMod.Z0 := by
    intro hh
    simp only [NVMod.Z0,Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with hh|hh|hh|hh <;> rw [hh] at hhalf <;> norm_num at hhalf
  have hcast : (((a:ℚ)/b:ℚ):ℝ)=(a:ℝ)/b := by push_cast;rfl
  have habs : |(((a:ℚ)/b:ℚ):ℝ)|<1 := by
    exact_mod_cast (lt_of_le_of_lt hhalf (by norm_num : (1/2:ℚ)<1))
  have hsign : Int.sign (((a:ℚ)/b:ℚ).num)=Int.sign a := by
    rcases lt_trichotomy a 0 with hneg|hzero|hpos
    · have hzneg : (a:ℚ)/b<0 := div_neg_of_neg_of_pos (by exact_mod_cast hneg) hbQ
      have hnneg : ((a:ℚ)/b:ℚ).num<0 := by
        apply lt_of_not_ge
        intro hn
        exact (not_le_of_gt hzneg) (Rat.num_nonneg.mp hn)
      rw [Int.sign_eq_neg_one_of_neg hnneg,Int.sign_eq_neg_one_of_neg hneg]
    · exact False.elim (ha hzero)
    · have hzpos : (0:ℚ)<(a:ℚ)/b := div_pos (by exact_mod_cast hpos) hbQ
      rw [Int.sign_eq_one_of_pos (Rat.num_pos.mpr hzpos),Int.sign_eq_one_of_pos hpos]
  refine ⟨hab,⟨hz0,hz1,hZ⟩,hcast,habs,hsign,?_⟩
  rw [hcast,abs_div,abs_of_pos hbR,one_div_div]

private theorem decay_from_table_sound (T : Uniform.NodeTable) (H : Uniform.TableSound T)
    (a b : ℤ) (hb : 0<b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D : ℝ) (hρ : 0<ρ)
    (hD : Uniform.Candidate T (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D) :
    CatalanCore.Uniform.HasScaledDecay (li2Family ((a:ℚ)/b)) scale D ρ := by
  have hi := rational_input a b hb ha h2
  apply Uniform.D_ge_of_candidate T H ((a:ℚ)/b) hi.2.1.1 hi.2.2.2.1 ρ D hρ
  rw [hi.2.2.2.2.1,hi.2.2.2.2.2]
  exact hD

private theorem measure_from_scaled (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b)
    (ha : a≠0) (h2 : 2*|a|≤b) (ρ D μ : ℝ) (hρ : 0<ρ)
    (hD : CatalanCore.Uniform.HasScaledDecay (li2Family ((a:ℚ)/b)) scale D ρ)
    (hη : 0<D+cRate a b) (hμ : ρ*max (2/(D+cRate a b)) (39/98)<μ)
    (nvCerts : NVMod.AllConstantsChecked 12) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-μ)<
      |(∑' k : ℕ,((a:ℝ)/b)^(k+1)/((k:ℝ)+1)^2)-(p:ℝ)/q| := by
  have hi := rational_input a b hb ha h2
  have hprim := Content.primitive_decay a b hb hab ha hi.1 D ρ hD
  have hK := NVMod.constants_nonzero_of_checked 12 nvCerts ((a:ℚ)/b) hi.2.1
  obtain ⟨B⟩ := NV.bandNV_li2 ((a:ℚ)/b) hi.2.1.1 hi.2.1.2.1 12 hK
  have B13 : CatalanCore.Measure.BandNV (primitiveFamily ((a:ℚ)/b)) id (1/13) (4/3) := by
    convert B using 1 <;> norm_num
  have hAdm : ∀ᶠ n : ℕ in Filter.atTop,(primitiveFamily ((a:ℚ)/b)).Adm (id n) := by
    exact Filter.eventually_ge_atTop 1
  have hdeg : ∀ n : ℕ,((primitiveFamily ((a:ℚ)/b)).deg (id n):ℝ)≤2*n := by
    intro n
    simp [primitiveFamily,Nat.cast_mul]
  have hmu : ρ*max ((2:ℝ)/((D+cRate a b)-0)) (1/(2*((4/3:ℝ)-1/13)))<μ := by
    have he : (1:ℝ)/(2*((4/3:ℝ)-1/13))=39/98 := by norm_num
    simpa only [sub_zero,he] using hμ
  have hm := CatalanCore.Measure.measure_of_bandNV (Fam:=primitiveFamily ((a:ℚ)/b))
    (Λ:=0) (D:=D+cRate a b) (ρ:=ρ) (κ:=2) (μ:=μ) (α:=1/13) (β:=4/3)
    (id : ℕ→ℕ) scale (fun _=>rfl) hAdm
    (Content.primitive_content ((a:ℚ)/b)) hprim hη hρ (by norm_num : (0:ℝ)<2)
    (by norm_num : (0:ℝ)<1/13 ∧ (1/13:ℝ)<4/3) hdeg B13 hmu
  simpa only [primitiveFamily,value,Rat.cast_div,Rat.cast_intCast] using hm


theorem decay_certs_to_scaled (T : Uniform.NodeTable)
    (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D : ℝ) (hρ : 0<ρ)
    (hD : Uniform.Candidate T (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (cert : DecayCert.DecayCertificates T) :
    CatalanCore.Uniform.HasScaledDecay (li2Family ((a:ℚ)/b)) scale D ρ := by
  exact decay_from_table_sound T (DecayCert.tableSoundOfCertificates T cert) a b hb ha h2 ρ D hρ hD

theorem li2_measure_general_of_certs (T : Uniform.NodeTable)
    (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D μ : ℝ) (hρ : 0<ρ)
    (hD : Uniform.Candidate T (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (hη : 0<D+cRate a b) (hμ : ρ*max (2/(D+cRate a b)) (39/98)<μ)
    (decayCerts : DecayCert.DecayCertificates T) (nvCerts : NVMod.AllConstantsChecked 12) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-μ)<
      |(∑' k : ℕ,((a:ℝ)/b)^(k+1)/((k:ℝ)+1)^2)-(p:ℝ)/q| := by
  exact measure_from_scaled a b hb hab ha h2 ρ D μ hρ
    (decay_certs_to_scaled T a b hb hab ha h2 ρ D hρ hD decayCerts) hη hμ nvCerts


/-- The measure bound from any sound decay table (certified on any mix of routes). -/
theorem li2_measure_general_of_tableSound (T : Uniform.NodeTable) (H : Uniform.TableSound T)
    (a b : ℤ) (hb : 0<b) (hab : IsCoprime a b) (ha : a≠0) (h2 : 2*|a|≤b)
    (ρ D μ : ℝ) (hρ : 0<ρ)
    (hD : Uniform.Candidate T (Int.sign a) (Real.log ((b:ℝ)/|(a:ℝ)|)) ρ D)
    (hη : 0<D+cRate a b) (hμ : ρ*max (2/(D+cRate a b)) (39/98)<μ)
    (nvCerts : NVMod.AllConstantsChecked 12) :
    ∀ᶠ q : ℕ in Filter.atTop,∀ p : ℤ,(q:ℝ)^(-μ)<
      |(∑' k : ℕ,((a:ℝ)/b)^(k+1)/((k:ℝ)+1)^2)-(p:ℝ)/q| :=
  measure_from_scaled a b hb hab ha h2 ρ D μ hρ
    (decay_from_table_sound T H a b hb ha h2 ρ D hρ hD) hη hμ nvCerts

#print axioms rational_input
#print axioms li2_measure_general_of_tableSound
#print axioms decay_certs_to_scaled
#print axioms li2_measure_general_of_certs
end
end CatalanCore.Li2

