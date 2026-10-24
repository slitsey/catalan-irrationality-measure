module

public import CatalanArchive.CatalanMeasure.GenD.D58.Bank592
public import CatalanMeasure.GenD.D58.Circle
public import CatalanMeasure.GenD.D58.Certified

@[expose] public section

/-!
# D58 circle certificate: instantiation check

`measure_592/590_of_certificates` with `g = 401/2500`, `rc = 1001/1000`, `C = 3`, `wc = 52788/1000`:
`hg0 hg1 ha4 hr1 hr2 hcirc hwc` are all discharged; what remains are the first/second population
hypotheses only.
-/

namespace CatalanMeasure.GenD
namespace D58

noncomputable def circ_check_592 := @measure_592_of_certificates (401 / 2500) (1001 / 1000) 3 (52788 / 1000)
  circ_hg0 circ_hg1 circ_ha4 circ_hr1 circ_hr2 circ_hcirc circ_hwc160

noncomputable def circ_check_590 := @measure_590_of_certificates (401 / 2500) (1001 / 1000) 3 (52788 / 1000)
  circ_hg0 circ_hg1 circ_ha4 circ_hr1 circ_hr2 circ_hcirc circ_hwc640

#print axioms circ_hcirc
#print axioms circ_hwc160
#print axioms circ_hwc640
#check @circ_check_592
#check @circ_check_590

end D58
end CatalanMeasure.GenD
