module
public import CatalanMeasure.Parametric.TwentyBase.Row1
public import CatalanMeasure.Parametric.TwentyBase.Row2
public import CatalanMeasure.Parametric.TwentyBase.Row3
public import CatalanMeasure.Parametric.TwentyBase.Row4
public import CatalanMeasure.Parametric.TwentyBase.Row5
public import CatalanMeasure.Parametric.TwentyBase.Row6
public import CatalanMeasure.Parametric.TwentyBase.Row7
public import CatalanMeasure.Parametric.TwentyBase.Row8
public import CatalanMeasure.Parametric.TwentyBase.Row9
public import CatalanMeasure.Parametric.TwentyBase.Row10
public import CatalanMeasure.Parametric.TwentyBase.Row11
public import CatalanMeasure.Parametric.TwentyBase.Row12
public import CatalanMeasure.Parametric.TwentyBase.Row13
public import CatalanMeasure.Parametric.TwentyBase.Row14
public import CatalanMeasure.Parametric.TwentyBase.Row15
public import CatalanMeasure.Parametric.TwentyBase.Row16
public import CatalanMeasure.Parametric.TwentyBase.Row17
public import CatalanMeasure.Parametric.TwentyBase.Row18
public import CatalanMeasure.Parametric.TwentyBase.Row19
public import CatalanMeasure.Parametric.TwentyBase.Row20
@[expose] public section
namespace CatalanMeasure.Parametric.TwentyBase
theorem actual_base_entries (r : Fin 21) (k : Fin 20) :
    baseFilteredContraction twenty 1009 r.val k=literalBaseEntry r k :=by
  fin_cases r
  · exact actual_base_row0 k
  · exact actual_base_row1 k
  · exact actual_base_row2 k
  · exact actual_base_row3 k
  · exact actual_base_row4 k
  · exact actual_base_row5 k
  · exact actual_base_row6 k
  · exact actual_base_row7 k
  · exact actual_base_row8 k
  · exact actual_base_row9 k
  · exact actual_base_row10 k
  · exact actual_base_row11 k
  · exact actual_base_row12 k
  · exact actual_base_row13 k
  · exact actual_base_row14 k
  · exact actual_base_row15 k
  · exact actual_base_row16 k
  · exact actual_base_row17 k
  · exact actual_base_row18 k
  · exact actual_base_row19 k
  · exact actual_base_row20 k
end CatalanMeasure.Parametric.TwentyBase
