module
public import CatalanCore.Li2.DecayCert.RealCells
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
structure SignPartition (α β : ℝ) where
  gaps : ℕ
  gaps_pos : 0 < gaps
  node : ℕ → ℝ
  first : node 0=α
  last : node gaps=β
  increasing : ∀ i j, i < j → j ≤ gaps → node i < node j
  positive : ℕ → Bool
  alternating : ∀ i, i+1 < gaps → positive (i+1)= !positive i
  delta : ℕ → ℝ
  delta_pos : ∀ i, 0 < i → i < gaps → 0 < delta i
  separated : ∀ i, 0 < i → i < gaps →
    2*delta i < min (node i-node (i-1)) (node (i+1)-node i)
def SignPartition.rootCount {α β : ℝ} (s : SignPartition α β) : ℕ := s.gaps-1
def SignPartition.rootCell {α β : ℝ} (s : SignPartition α β)
    (i : Fin s.rootCount) : Set ℝ := Icc (s.node (i+1)-s.delta (i+1)) (s.node (i+1)+s.delta (i+1))
def SignPartition.signAway {α β : ℝ} (s : SignPartition α β) (f : ℝ → ℝ) : Prop :=
  ∀ i, i < s.gaps → ∀ x ∈ Icc (s.node i) (s.node (i+1)),
    (∀ j : Fin s.rootCount, x ∉ s.rootCell j) →
    if s.positive i then 0 ≤ f x else f x ≤ 0
noncomputable def SignPartition.plusIntegral {α β : ℝ} (s : SignPartition α β)
    (f : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range s.gaps, if s.positive i then ∫ x in s.node i..s.node (i+1), f x else 0
noncomputable def SignPartition.rootError {α β : ℝ} (s : SignPartition α β)
    (ep em : Fin s.rootCount → ℝ) : ℝ :=
  ∑ i : Fin s.rootCount, (2*s.delta ((i:ℕ)+1)*ep i+s.delta ((i:ℕ)+1)*em i)


theorem integral_three_piece_upper (g : ℝ → ℝ) (l a b r E₁ E₂ : ℝ)
    (hla : l ≤ a) (hab : a ≤ b) (hbr : b ≤ r)
    (hg : ContinuousOn g (Icc l r))
    (hleft : ∀ x ∈ Ioo l a,g x ≤ E₁) (hmiddle : ∀ x ∈ Ioo a b,g x ≤ 0)
    (hright : ∀ x ∈ Ioo b r,g x ≤ E₂) :
    (∫ x in l..r,g x) ≤ (a-l)*E₁+(r-b)*E₂ := by
  have hint (c d : ℝ) (hlc : l ≤ c) (hcd : c ≤ d) (hdr : d ≤ r) :
      IntervalIntegrable g volume c d :=
    (hg.mono (Icc_subset_Icc hlc hdr)).intervalIntegrable_of_Icc hcd
  have h₁ := intervalIntegral.integral_mono_on_of_le_Ioo hla
    (hint l a le_rfl hla (hab.trans hbr))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => E₁) volume l a) hleft
  have h₂ := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (hint a b hla hab hbr)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume a b) hmiddle
  have h₃ := intervalIntegral.integral_mono_on_of_le_Ioo hbr
    (hint b r (hla.trans hab) hbr le_rfl)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => E₂) volume b r) hright
  simp only [intervalIntegral.integral_const,smul_eq_mul,mul_zero] at h₁ h₂ h₃
  have hs₁ := intervalIntegral.integral_add_adjacent_intervals
    (hint l a le_rfl hla (hab.trans hbr)) (hint a b hla hab hbr)
  have hs₂ := intervalIntegral.integral_add_adjacent_intervals
    (hint l b le_rfl (hla.trans hab) hbr) (hint b r (hla.trans hab) hbr le_rfl)
  linarith

theorem SignPartition.node_le {α β : ℝ} (s : SignPartition α β) (i j : ℕ)
    (hij : i ≤ j) (hj : j ≤ s.gaps) : s.node i ≤ s.node j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact le_rfl
  · exact (s.increasing i j hij hj).le

theorem SignPartition.interior_delta_lt {α β : ℝ} (s : SignPartition α β)
    (k : ℕ) (hk : 0 < k ∧ k < s.gaps) :
    0 < s.delta k ∧ s.delta k < s.node k-s.node (k-1) ∧
      s.delta k < s.node (k+1)-s.node k := by
  have hp := s.delta_pos k hk.1 hk.2
  have hh := s.separated k hk.1 hk.2
  have h₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have h₂ := lt_of_lt_of_le hh (min_le_right _ _)
  exact ⟨hp,by linarith,by linarith⟩

noncomputable def SignPartition.innerLeft {α β : ℝ} (s : SignPartition α β) (i : ℕ) : ℝ :=
  s.node i+(if 0 < i then s.delta i else 0)
noncomputable def SignPartition.innerRight {α β : ℝ} (s : SignPartition α β) (i : ℕ) : ℝ :=
  s.node (i+1)-(if i+1 < s.gaps then s.delta (i+1) else 0)

theorem SignPartition.inner_order {α β : ℝ} (s : SignPartition α β) (i : ℕ) (hi : i < s.gaps) :
    s.node i ≤ s.innerLeft i ∧ s.innerLeft i < s.innerRight i ∧
      s.innerRight i ≤ s.node (i+1) := by
  have hgap := s.increasing i (i+1) (by omega) (by omega)
  let dl := if 0 < i then s.delta i else 0
  let dr := if i+1 < s.gaps then s.delta (i+1) else 0
  have hl : 0 ≤ dl ∧ 2*dl < s.node (i+1)-s.node i := by
    by_cases h : 0 < i
    · dsimp only [dl]
      rw [ite_eq_left h]
      exact ⟨(s.delta_pos i h hi).le,lt_of_lt_of_le (s.separated i h hi) (min_le_right _ _)⟩
    · simp only [dl,ite_eq_right h]
      exact ⟨le_rfl,by linarith⟩
  have hr : 0 ≤ dr ∧ 2*dr < s.node (i+1)-s.node i := by
    by_cases h : i+1 < s.gaps
    · dsimp only [dr]
      rw [ite_eq_left h]
      have hd := lt_of_lt_of_le (s.separated (i+1) (by omega) h) (min_le_left _ _)
      have he : i+1-1=i := by omega
      rw [he] at hd
      exact ⟨(s.delta_pos (i+1) (by omega) h).le,hd⟩
    · simp only [dr,ite_eq_right h]
      exact ⟨le_rfl,by linarith⟩
  change s.node i ≤ s.node i+dl ∧ s.node i+dl < s.node (i+1)-dr ∧
    s.node (i+1)-dr ≤ s.node (i+1)
  exact ⟨by linarith [hl.1],by linarith [hl.2,hr.2],by linarith [hr.1]⟩

theorem SignPartition.inner_avoids {α β : ℝ} (s : SignPartition α β)
    (i : ℕ) (hi : i < s.gaps) (x : ℝ) (hx : x ∈ Ioo (s.innerLeft i) (s.innerRight i)) :
    ∀ j : Fin s.rootCount,x ∉ s.rootCell j := by
  intro j hm
  let k := (j:ℕ)+1
  have hk : 0 < k ∧ k < s.gaps := by
    have hh := j.isLt
    dsimp [rootCount] at hh
    dsimp [k]
    omega
  have hd := s.interior_delta_lt k hk
  have ho := s.inner_order i hi
  have hxx : s.node i < x ∧ x < s.node (i+1) :=
    ⟨ho.1.trans_lt hx.1,hx.2.trans_le ho.2.2⟩
  change s.node k-s.delta k ≤ x ∧ x ≤ s.node k+s.delta k at hm
  by_cases hki : k ≤ i
  · rcases hki.eq_or_lt with he | he
    · have hk0 : 0 < i := by omega
      have hl : s.innerLeft i=s.node i+s.delta i := by simp [innerLeft,hk0]
      rw [hl] at hx
      rw [he] at hm
      linarith [hx.1,hm.2]
    · have hn := s.node_le (k+1) i (by omega) (by omega)
      linarith [hd.2.2,hm.2,hxx.1]
  · have hik : i < k := by omega
    by_cases he : k=i+1
    · have hkg : i+1 < s.gaps := by omega
      have hr : s.innerRight i=s.node (i+1)-s.delta (i+1) := by simp [innerRight,hkg]
      rw [hr] at hx
      rw [he] at hm
      linarith [hx.2,hm.1]
    · have hn := s.node_le (i+1) (k-1) (by omega) (by omega)
      linarith [hd.2.1,hm.1,hxx.2]

noncomputable def SignPartition.rootAt {α β : ℝ} (s : SignPartition α β)
    (e : Fin s.rootCount → ℝ) (k : ℕ) : ℝ :=
  if h : 0 < k ∧ k < s.gaps then e ⟨k-1,by dsimp [rootCount]; omega⟩ else 0

theorem SignPartition.rootAt_nonneg {α β : ℝ} (s : SignPartition α β)
    (e : Fin s.rootCount → ℝ) (he : ∀ j,0 ≤ e j) (k : ℕ) : 0 ≤ s.rootAt e k := by
  unfold rootAt
  split_ifs <;> first | exact he _ | exact le_rfl

theorem SignPartition.rootAt_boundary {α β : ℝ} (s : SignPartition α β)
    (e : Fin s.rootCount → ℝ) : s.rootAt e 0=0 ∧ s.rootAt e s.gaps=0 := by
  simp [rootAt]

theorem SignPartition.rootAt_interior {α β : ℝ} (s : SignPartition α β)
    (e : Fin s.rootCount → ℝ) (j : Fin s.rootCount) : s.rootAt e ((j:ℕ)+1)=e j := by
  have hk : 0 < (j:ℕ)+1 ∧ (j:ℕ)+1 < s.gaps := by
    have hh := j.isLt
    dsimp [rootCount] at hh
    omega
  simp [rootAt,hk]

noncomputable def SignPartition.gapError {α β : ℝ} (s : SignPartition α β)
    (ep em : Fin s.rootCount → ℝ) (i : ℕ) : ℝ :=
  (s.innerLeft i-s.node i)*(if s.positive i then s.rootAt em i else s.rootAt ep i)+
  (s.node (i+1)-s.innerRight i)*(if s.positive i then s.rootAt em (i+1) else s.rootAt ep (i+1))

theorem SignPartition.node_bounds {α β : ℝ} (s : SignPartition α β) (i : ℕ) (hi : i ≤ s.gaps) :
    α ≤ s.node i ∧ s.node i ≤ β := by
  have h₁ := s.node_le 0 i (by omega) hi
  have h₂ := s.node_le i s.gaps hi le_rfl
  rw [s.first] at h₁
  rw [s.last] at h₂
  exact ⟨h₁,h₂⟩

theorem SignPartition.gap_pos_upper {α β : ℝ} (s : SignPartition α β)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc α β)) (hsgn : s.signAway f)
    (ep em : Fin s.rootCount → ℝ) (hep : ∀ j,0 ≤ ep j) (hem : ∀ j,0 ≤ em j)
    (hp : ∀ j,∀ x ∈ s.rootCell j,f x ≤ ep j)
    (hm : ∀ j,∀ x ∈ s.rootCell j,-f x ≤ em j)
    (i : ℕ) (hi : i < s.gaps) :
    (∫ x in s.node i..s.node (i+1),pos (f x)) ≤
      (if s.positive i then ∫ x in s.node i..s.node (i+1),f x else 0)+s.gapError ep em i := by
  have ho := s.inner_order i hi
  have hnodes : s.node i ≤ s.node (i+1) := s.node_le i (i+1) (by omega) (by omega)
  have hfg : ContinuousOn f (Icc (s.node i) (s.node (i+1))) :=
    hf.mono (Icc_subset_Icc (s.node_bounds i (by omega)).1 (s.node_bounds (i+1) (by omega)).2)
  let g : ℝ → ℝ := fun x => if s.positive i then pos (-f x) else pos (f x)
  have hg : ContinuousOn g (Icc (s.node i) (s.node (i+1))) := by
    cases hpi : s.positive i
    · simpa [g,hpi,pos] using hfg.sup (continuousOn_const (c:=(0:ℝ)))
    · simpa [g,hpi,pos] using hfg.neg.sup (continuousOn_const (c:=(0:ℝ)))
  have hleft (x : ℝ) (hx : x ∈ Ioo (s.node i) (s.innerLeft i)) :
      g x ≤ if s.positive i then s.rootAt em i else s.rootAt ep i := by
    have hip : 0 < i := by
      by_contra hh
      have he : i=0 := by omega
      subst i
      simp [innerLeft] at hx
    let j : Fin s.rootCount := ⟨i-1,by dsimp [rootCount]; omega⟩
    have hji : (j:ℕ)+1=i := by dsimp [j]; omega
    have hxroot : x ∈ s.rootCell j := by
      change s.node ((j:ℕ)+1)-s.delta ((j:ℕ)+1) ≤ x ∧
        x ≤ s.node ((j:ℕ)+1)+s.delta ((j:ℕ)+1)
      rw [hji]
      have hd := s.delta_pos i hip hi
      have ha : s.innerLeft i=s.node i+s.delta i := by simp [innerLeft,hip]
      rw [ha] at hx
      exact ⟨by linarith [hx.1],hx.2.le⟩
    have he₁ : s.rootAt ep i=ep j := by rw [← hji,rootAt_interior]
    have he₂ : s.rootAt em i=em j := by rw [← hji,rootAt_interior]
    cases hpi : s.positive i
    · simpa [g,hpi,he₁,pos] using max_le (hp j x hxroot) (hep j)
    · simpa [g,hpi,he₂,pos] using max_le (hm j x hxroot) (hem j)
  have hright (x : ℝ) (hx : x ∈ Ioo (s.innerRight i) (s.node (i+1))) :
      g x ≤ if s.positive i then s.rootAt em (i+1) else s.rootAt ep (i+1) := by
    have hip : i+1 < s.gaps := by
      by_contra hh
      have hr : s.innerRight i=s.node (i+1) := by simp [innerRight,hh]
      rw [hr] at hx
      linarith [hx.1,hx.2]
    let j : Fin s.rootCount := ⟨i,by dsimp [rootCount]; omega⟩
    have hxroot : x ∈ s.rootCell j := by
      change s.node (i+1)-s.delta (i+1) ≤ x ∧ x ≤ s.node (i+1)+s.delta (i+1)
      have hd := s.delta_pos (i+1) (by omega) hip
      have hr : s.innerRight i=s.node (i+1)-s.delta (i+1) := by simp [innerRight,hip]
      rw [hr] at hx
      exact ⟨hx.1.le,by linarith [hx.2]⟩
    have he₁ : s.rootAt ep (i+1)=ep j := rootAt_interior s ep j
    have he₂ : s.rootAt em (i+1)=em j := rootAt_interior s em j
    cases hpi : s.positive i
    · simpa [g,hpi,he₁,pos] using max_le (hp j x hxroot) (hep j)
    · simpa [g,hpi,he₂,pos] using max_le (hm j x hxroot) (hem j)
  have hmid (x : ℝ) (hx : x ∈ Ioo (s.innerLeft i) (s.innerRight i)) : g x ≤ 0 := by
    have hxnode : x ∈ Icc (s.node i) (s.node (i+1)) :=
      ⟨ho.1.trans hx.1.le,hx.2.le.trans ho.2.2⟩
    have hs := hsgn i hi x hxnode (s.inner_avoids i hi x hx)
    cases hpi : s.positive i
    · simp [hpi] at hs
      simpa [g,hpi,pos] using max_le hs (le_refl (0:ℝ))
    · simp [hpi] at hs
      simpa [g,hpi,pos] using max_le (by linarith : -f x ≤ 0) (le_refl (0:ℝ))
  have hb := integral_three_piece_upper g _ _ _ _ _ _ ho.1 ho.2.1.le ho.2.2 hg hleft hmid hright
  have hiF : IntervalIntegrable f volume (s.node i) (s.node (i+1)) := hfg.intervalIntegrable_of_Icc hnodes
  have hiG : IntervalIntegrable g volume (s.node i) (s.node (i+1)) := hg.intervalIntegrable_of_Icc hnodes
  have hid : (fun x => pos (f x))=(fun x => (if s.positive i then f x else 0)+g x) := by
    funext x
    cases hpi : s.positive i
    · simp [g,hpi]
    · by_cases hfx : 0 ≤ f x
      · simp [g,hpi,pos,max_eq_left hfx,max_eq_right (by linarith : -f x ≤ 0)]
      · simp [g,hpi,pos,max_eq_right (by linarith : f x ≤ 0),max_eq_left (by linarith : 0 ≤ -f x)]
  have hif : IntervalIntegrable (fun x => if s.positive i then f x else 0) volume (s.node i) (s.node (i+1)) := by
    cases hpi : s.positive i <;> simp only [hpi,Bool.false_eq_true,ite_false,ite_true]
    · exact intervalIntegrable_const
    · exact hiF
  have he : (∫ x in s.node i..s.node (i+1),pos (f x))=
      (if s.positive i then ∫ x in s.node i..s.node (i+1),f x else 0)+
        (∫ x in s.node i..s.node (i+1),g x) := by
    rw [hid,intervalIntegral.integral_add hif hiG]
    cases hpi : s.positive i <;> simp [hpi]
  rw [he]
  dsimp only [gapError]
  linarith

theorem SignPartition.gapError_expand {α β : ℝ} (s : SignPartition α β)
    (ep em : Fin s.rootCount → ℝ) (i : ℕ) (hi : i < s.gaps) :
    s.gapError ep em i=
      s.delta i*(if s.positive i then s.rootAt em i else s.rootAt ep i)+
      s.delta (i+1)*(if s.positive i then s.rootAt em (i+1) else s.rootAt ep (i+1)) := by
  by_cases hl : 0 < i
  · by_cases hr : i+1 < s.gaps
    · dsimp [gapError,innerLeft,innerRight]
      simp only [ite_eq_left hl,ite_eq_left hr]
      ring
    · have he : i+1=s.gaps := by omega
      simp [gapError,innerLeft,innerRight,hl,hr,he,rootAt]
  · have he : i=0 := by omega
    subst i
    by_cases hr : 1 < s.gaps
    · simp [gapError,innerLeft,innerRight,hr,rootAt]
    · have hg : s.gaps=1 := by have := s.gaps_pos; omega
      simp [gapError,innerLeft,innerRight,hg,rootAt]

theorem SignPartition.sum_gapError {α β : ℝ} (s : SignPartition α β)
    (ep em : Fin s.rootCount → ℝ) :
    (∑ i ∈ Finset.range s.gaps,s.gapError ep em i)=
      ∑ j ∈ Finset.range s.rootCount,s.delta (j+1)*(s.rootAt ep (j+1)+s.rootAt em (j+1)) := by
  let E := fun k i : ℕ => s.delta k*(if s.positive i then s.rootAt em k else s.rootAt ep k)
  have hg : s.gaps=s.rootCount+1 := by dsimp [rootCount]; have := s.gaps_pos; omega
  have hleft : (∑ i ∈ Finset.range s.gaps,E i i)=
      ∑ j ∈ Finset.range s.rootCount,E (j+1) (j+1) := by
    rw [hg,Finset.sum_range_succ']
    have hz : E 0 0=0 := by simp [E,rootAt]
    rw [hz,add_zero]
  have hright : (∑ i ∈ Finset.range s.gaps,E (i+1) i)=
      ∑ j ∈ Finset.range s.rootCount,E (j+1) j := by
    rw [hg,Finset.sum_range_succ]
    have hz : E (s.rootCount+1) s.rootCount=0 := by rw [← hg]; simp [E,rootAt]
    rw [hz,add_zero]
  have he : (∑ i ∈ Finset.range s.gaps,s.gapError ep em i)=
      (∑ i ∈ Finset.range s.gaps,E i i)+(∑ i ∈ Finset.range s.gaps,E (i+1) i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact s.gapError_expand ep em i (Finset.mem_range.mp hi)
  rw [he,hleft,hright,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hAlt := s.alternating j (by have := Finset.mem_range.mp hj; dsimp [rootCount] at this; omega)
  cases hpi : s.positive j
  · have hpj : s.positive (j+1)=true := by simpa [hpi] using hAlt
    simp only [E,hpi,hpj,Bool.false_eq_true,ite_false,ite_true]
    ring
  · have hpj : s.positive (j+1)=false := by simpa [hpi] using hAlt
    simp only [E,hpi,hpj,Bool.false_eq_true,ite_false,ite_true]
    ring

theorem SignPartition.sum_gapError_le {α β : ℝ} (s : SignPartition α β)
    (ep em : Fin s.rootCount → ℝ) (hep : ∀ j,0 ≤ ep j) :
    (∑ i ∈ Finset.range s.gaps,s.gapError ep em i) ≤ s.rootError ep em := by
  rw [s.sum_gapError ep em,← Fin.sum_univ_eq_sum_range]
  dsimp only [rootError]
  apply Finset.sum_le_sum
  intro j hj
  rw [s.rootAt_interior ep j,s.rootAt_interior em j]
  have hk : (j:ℕ)+1 < s.gaps := by have := j.isLt; dsimp [rootCount] at this; omega
  have hd := s.delta_pos ((j:ℕ)+1) (by omega) hk
  nlinarith [mul_nonneg hd.le (hep j)]

theorem int_pos_le_signPattern (α β : ℝ) (hαβ : α ≤ β) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc α β)) (s : SignPartition α β)
    (hsgn : s.signAway f) (ep em : Fin s.rootCount → ℝ)
    (hep : ∀ i,0 ≤ ep i) (hem : ∀ i,0 ≤ em i)
    (hp : ∀ i,∀ x ∈ s.rootCell i,f x ≤ ep i)
    (hm : ∀ i,∀ x ∈ s.rootCell i,-f x ≤ em i) :
    (∫ x in α..β,pos (f x)) ≤ s.plusIntegral f+s.rootError ep em := by
  have hpos : ContinuousOn (fun x => pos (f x)) (Icc α β) := by
    simpa only [pos] using hf.sup (continuousOn_const (c:=(0:ℝ)))
  have hint (i : ℕ) (hi : i < s.gaps) :
      IntervalIntegrable (fun x => pos (f x)) volume (s.node i) (s.node (i+1)) :=
    (hpos.mono (Icc_subset_Icc (s.node_bounds i (by omega)).1
      (s.node_bounds (i+1) (by omega)).2)).intervalIntegrable_of_Icc
        (s.node_le i (i+1) (by omega) (by omega))
  have hs := intervalIntegral.sum_integral_adjacent_intervals hint
  rw [s.first,s.last] at hs
  have hsum : (∑ i ∈ Finset.range s.gaps,∫ x in s.node i..s.node (i+1),pos (f x)) ≤
      ∑ i ∈ Finset.range s.gaps,
        ((if s.positive i then ∫ x in s.node i..s.node (i+1),f x else 0)+s.gapError ep em i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact s.gap_pos_upper f hf hsgn ep em hep hem hp hm i (Finset.mem_range.mp hi)
  rw [Finset.sum_add_distrib] at hsum
  change _ ≤ s.plusIntegral f+_ at hsum
  rw [hs] at hsum
  have herr := s.sum_gapError_le ep em hep
  linarith

#print axioms int_pos_le_signPattern
end CatalanCore.Li2.DecayCert
