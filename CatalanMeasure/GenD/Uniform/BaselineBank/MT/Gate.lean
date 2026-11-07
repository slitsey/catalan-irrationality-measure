module

public import CatalanMeasure.GenD.Uniform.BaselineBank.MT.Instance

@[expose] public section
set_option Elab.async false

/-!
# The B = 540 gate for Ledger2 + MT (1), and the drop-in interface for M and Z (lane G5f)

* `gain3 = mtGain + gain2 = 20.2223...` (`mtGain = 35863749/400000000 = 0.08966`, the certified MT (1) area).
* `gate_of_remaining3`: the remaining families (Theorem M, Theorem Z, ...) must add area `>= 1.3860`.
* `gate_of_families_windows`: the general final statement.  A new family is any `lb : NullityLB design`
  (for instance the `NullityLB` of `W/HYPlus` or `W/ZoneZ`, taken as a parameter); it enters by supplying
  windows `w` with `WinCert lb w`.  Given an ordered window list whose members are each certified against
  one family of the list and whose total area is `>= 21.6083`, the payment hypotheses hold, the decay rate
  `eta = 29.596` is admissible, and the denominator growth bound follows.
* `wins3_cert_ext`: the windows `wins3` stay certified when further families are added to the list.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger3
open CatalanMeasure.GenD D58 Filter CatalanMeasure.Parametric OAI.InternalCatalan
open CatalanMeasure.GenD.Uniform.LedgerW CatalanMeasure.GenD.Uniform.Arithmetic CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.GenD.Uniform.Bank540.Ledger2
noncomputable section

/-- The windows of `wins3` remain certified when more families are appended. -/
theorem wins3_cert_ext (ex : List (NullityLB design)) :
    ∀ w ∈ wins3, ∃ lb ∈ fams3 ++ ex, WinCert lb w := by
  intro w hw
  obtain ⟨lb, hlb, h⟩ := wins3_cert w hw
  exact ⟨lb, List.mem_append_left _ hlb, h⟩

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger3
