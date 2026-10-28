module

public import CatalanCore.Uniform.Content.UFFamily2.Lu

@[expose] public section

open CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily2

set_option profiler true
set_option profiler.threshold 200

namespace CatalanCore.Uniform.Content.UFFamily2.Data.Thirds0

-- thirds class 1: q=3 o=2 p%q=1 nrm=1 u0s=[2, 3]
def t0 : JType := { nodes := [(0, 1)], zone := (1, 4) }
def t1 : JType := { nodes := [(0, 0), (1, 1), (2, 4), (3, 7)], zone := (4, 10) }
def t2 : JType := { nodes := [(0, 0), (1, 1), (2, 4)], zone := (3, 7) }
def t3 : JType := { nodes := [(0, 1), (1, 4)], zone := (2, 7) }
def t4 : JType := { nodes := [(0, 0), (1, 1)], zone := (2, 4) }
def t5 : JType := { nodes := [], zone := (0, 1) }
def t6 : JType := { nodes := [], zone := (0, 0) }
def t7 : JType := { nodes := [(0, 0)], zone := (1, 1) }
def t8 : JType := { nodes := [(0, 1), (1, 4), (2, 7)], zone := (3, 10) }
def Dn_t0_u2 : ℤ := 4
def lu_t0_u2 : LuData where
  LM := [[1]]
  UM := [[44]]
  LA := [[1, 0], [-1, 44]]
  UA := [[44, -12], [0, -472]]
  LB := [[1, 0], [-1, 44]]
  UB := [[44, 4], [0, 172]]
  a := -472
  b := 172
theorem intOK_t0_u2 : IntOK 3 2 1 (1 : ℚ) 2 t0 Dn_t0_u2 := by decide +kernel
theorem ok_t0_u2 : lu_t0_u2.ok t0.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t0 Dn_t0_u2) Dn_t0_u2 = true := by decide +kernel
def Dn_t0_u3 : ℤ := 4
def lu_t0_u3 : LuData where
  LM := [[1]]
  UM := [[48]]
  LA := [[1, 0], [-1, 48]]
  UA := [[48, -12], [0, -516]]
  LB := [[1, 0], [-1, 48]]
  UB := [[48, 4], [0, 188]]
  a := -516
  b := 188
theorem intOK_t0_u3 : IntOK 3 2 1 (1 : ℚ) 3 t0 Dn_t0_u3 := by decide +kernel
theorem ok_t0_u3 : lu_t0_u3.ok t0.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t0 Dn_t0_u3) Dn_t0_u3 = true := by decide +kernel
def Dn_t1_u2 : ℤ := 35280
def lu_t1_u2 : LuData where
  LM := [[1, 0, 0, 0], [1, 1, 0, 0], [47, 11, 64, 0], [2751326, 643413, 360752, 4873680]]
  UM := [[70560, -70560, -39690, -27580], [0, 282240, -48510, -33670], [0, 0, 21322350, -1578290], [0, 0, 0, 1704631163830]]
  LA := [[1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [47, 11, 64, 0, 0], [2751326, 643413, 360752, 4873680, 0], [6991558508589, 1634312141532, 916240016158, 635728633596, 15341680474470]]
  UA := [[70560, -70560, -39690, -27580, 0], [0, 282240, -48510, -33670, -70560], [0, 0, 21322350, -1578290, -5856480], [0, 0, 0, 1704631163830, -477283998240], [0, 0, 0, 0, -1537081751147465880]]
  LB := [[1, 0, 0, 0, 0], [1, 1, 0, 0, 0], [47, 11, 64, 0, 0], [2751326, 643413, 360752, 4873680, 0], [6991558508589, 1634312141532, 916240016158, 635728633596, 15341680474470]]
  UB := [[70560, -70560, -39690, -27580, 35280], [0, 282240, -48510, -33670, 70560], [0, 0, 21322350, -1578290, 4304160], [0, 0, 0, 1704631163830, 304437152880], [0, 0, 0, 0, 900328657638891600]]
  a := -232503596923819131406440000
  b := 136186413740431660090800000
theorem intOK_t1_u2 : IntOK 3 2 1 (1 : ℚ) 2 t1 Dn_t1_u2 := by decide +kernel
theorem ok_t1_u2 : lu_t1_u2.ok t1.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t1 Dn_t1_u2) Dn_t1_u2 = true := by decide +kernel
def Dn_t1_u3 : ℤ := 35280
def lu_t1_u3 : LuData where
  LM := [[1, 0, 0, 0], [2, 3, 0, 0], [103, 24, 232, 0], [3303334, 768737, 430448, 10090584]]
  UM := [[105840, -70560, -39690, -27580], [0, 1023120, -105840, -73430], [0, 0, 88292610, -3766420], [0, 0, 0, 3955800557030]]
  LA := [[1, 0, 0, 0, 0], [2, 3, 0, 0, 0], [103, 24, 232, 0, 0], [3303334, 768737, 430448, 10090584, 0], [9197726421897, 2138964666796, 1197495094774, 830357294508, 35602205013270]]
  UA := [[105840, -70560, -39690, -27580, 0], [0, 1023120, -105840, -73430, -211680], [0, 0, 88292610, -3766420, -20109600], [0, 0, 0, 3955800557030, -923305965120], [0, 0, 0, 0, -3323215002501245880]]
  LB := [[1, 0, 0, 0, 0], [2, 3, 0, 0, 0], [103, 24, 232, 0, 0], [3303334, 768737, 430448, 10090584, 0], [9197726421897, 2138964666796, 1197495094774, 830357294508, 35602205013270]]
  UB := [[105840, -70560, -39690, -27580, 35280], [0, 1023120, -105840, -73430, 176400], [0, 0, 88292610, -3766420, 12665520], [0, 0, 0, 3955800557030, 514844673840], [0, 0, 0, 0, 1727546886771123600]]
  a := -502679470923345955546440000
  b := 261313924733660469106800000
theorem intOK_t1_u3 : IntOK 3 2 1 (1 : ℚ) 3 t1 Dn_t1_u3 := by decide +kernel
theorem ok_t1_u3 : lu_t1_u3.ok t1.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t1 Dn_t1_u3) Dn_t1_u3 = true := by decide +kernel
def Dn_t2_u2 : ℤ := 1008
def lu_t2_u2 : LuData where
  LM := [[1, 0, 0], [1, 1, 0], [47, 11, 64]]
  UM := [[2016, -2016, -1134], [0, 8064, -1386], [0, 0, 609210]]
  LA := [[1, 0, 0, 0], [1, 1, 0, 0], [47, 11, 64, 0], [2751326, 643413, 360752, 4873680]]
  UA := [[2016, -2016, -1134, 0], [0, 8064, -1386, -2016], [0, 0, 609210, -167328], [0, 0, 0, -13636685664]]
  LB := [[1, 0, 0, 0], [1, 1, 0, 0], [47, 11, 64, 0], [2751326, 643413, 360752, 4873680]]
  UB := [[2016, -2016, -1134, 1008], [0, 8064, -1386, 2016], [0, 0, 609210, 122976], [0, 0, 0, 8698204368]]
  a := -432992043203328
  b := 276185385092736
theorem intOK_t2_u2 : IntOK 3 2 1 (1 : ℚ) 2 t2 Dn_t2_u2 := by decide +kernel
theorem ok_t2_u2 : lu_t2_u2.ok t2.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t2 Dn_t2_u2) Dn_t2_u2 = true := by decide +kernel
def Dn_t2_u3 : ℤ := 1008
def lu_t2_u3 : LuData where
  LM := [[1, 0, 0], [2, 3, 0], [103, 24, 232]]
  UM := [[3024, -2016, -1134], [0, 29232, -3024], [0, 0, 2522646]]
  LA := [[1, 0, 0, 0], [2, 3, 0, 0], [103, 24, 232, 0], [3303334, 768737, 430448, 10090584]]
  UA := [[3024, -2016, -1134, 0], [0, 29232, -3024, -6048], [0, 0, 2522646, -574560], [0, 0, 0, -26380170432]]
  LB := [[1, 0, 0, 0], [2, 3, 0, 0], [103, 24, 232, 0], [3303334, 768737, 430448, 10090584]]
  UB := [[3024, -2016, -1134, 1008], [0, 29232, -3024, 5040], [0, 0, 2522646, 361872], [0, 0, 0, 14709847824]]
  a := -837623171556864
  b := 467067088107648
theorem intOK_t2_u3 : IntOK 3 2 1 (1 : ℚ) 3 t2 Dn_t2_u3 := by decide +kernel
theorem ok_t2_u3 : lu_t2_u3.ok t2.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t2 Dn_t2_u3) Dn_t2_u3 = true := by decide +kernel
def Dn_t3_u2 : ℤ := 112
def lu_t3_u2 : LuData where
  LM := [[1, 0], [-1, 44]]
  UM := [[1232, 28], [0, 52024]]
  LA := [[1, 0, 0], [-1, 44, 0], [-1505, -668, 104048]]
  UA := [[1232, 28, -336], [0, 52024, -13216], [0, 0, -30502976]]
  LB := [[1, 0, 0], [-1, 44, 0], [-1505, -668, 104048]]
  UB := [[1232, 28, 112], [0, 52024, 4816], [0, 0, 11410000]]
  a := -427041664
  b := 159740000
theorem intOK_t3_u2 : IntOK 3 2 1 (1 : ℚ) 2 t3 Dn_t3_u2 := by decide +kernel
theorem ok_t3_u2 : lu_t3_u2.ok t3.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t3 Dn_t3_u2) Dn_t3_u2 = true := by decide +kernel
def Dn_t3_u3 : ℤ := 112
def lu_t3_u3 : LuData where
  LM := [[1, 0], [-1, 48]]
  UM := [[1344, 28], [0, 62132]]
  LA := [[1, 0, 0], [-1, 48, 0], [-1649, -732, 124264]]
  UA := [[1344, 28, -336], [0, 62132, -14448], [0, 0, -36499680]]
  LB := [[1, 0, 0], [-1, 48, 0], [-1649, -732, 124264]]
  UB := [[1344, 28, 112], [0, 62132, 5264], [0, 0, 13650896]]
  a := -510995520
  b := 191112544
theorem intOK_t3_u3 : IntOK 3 2 1 (1 : ℚ) 3 t3 Dn_t3_u3 := by decide +kernel
theorem ok_t3_u3 : lu_t3_u3.ok t3.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t3 Dn_t3_u3) Dn_t3_u3 = true := by decide +kernel
def Dn_t4_u2 : ℤ := 8
def lu_t4_u2 : LuData where
  LM := [[1, 0], [1, 1]]
  UM := [[16, -16], [0, 64]]
  LA := [[1, 0, 0], [1, 1, 0], [47, 11, 64]]
  UA := [[16, -16, 0], [0, 64, -16], [0, 0, -1328]]
  LB := [[1, 0, 0], [1, 1, 0], [47, 11, 64]]
  UB := [[16, -16, 8], [0, 64, 16], [0, 0, 976]]
  a := -21248
  b := 15616
theorem intOK_t4_u2 : IntOK 3 2 1 (1 : ℚ) 2 t4 Dn_t4_u2 := by decide +kernel
theorem ok_t4_u2 : lu_t4_u2.ok t4.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t4 Dn_t4_u2) Dn_t4_u2 = true := by decide +kernel
def Dn_t4_u3 : ℤ := 8
def lu_t4_u3 : LuData where
  LM := [[1, 0], [2, 3]]
  UM := [[24, -16], [0, 232]]
  LA := [[1, 0, 0], [2, 3, 0], [103, 24, 232]]
  UA := [[24, -16, 0], [0, 232, -48], [0, 0, -4560]]
  LB := [[1, 0, 0], [2, 3, 0], [103, 24, 232]]
  UB := [[24, -16, 8], [0, 232, 40], [0, 0, 2872]]
  a := -36480
  b := 22976
theorem intOK_t4_u3 : IntOK 3 2 1 (1 : ℚ) 3 t4 Dn_t4_u3 := by decide +kernel
theorem ok_t4_u3 : lu_t4_u3.ok t4.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t4 Dn_t4_u3) Dn_t4_u3 = true := by decide +kernel
def Dn_t5_u2 : ℤ := 1
def lu_t5_u2 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[-3]]
  LB := [[1]]
  UB := [[1]]
  a := -3
  b := 1
theorem intOK_t5_u2 : IntOK 3 2 1 (1 : ℚ) 2 t5 Dn_t5_u2 := by decide +kernel
theorem ok_t5_u2 : lu_t5_u2.ok t5.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t5 Dn_t5_u2) Dn_t5_u2 = true := by decide +kernel
def Dn_t5_u3 : ℤ := 1
def lu_t5_u3 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[-3]]
  LB := [[1]]
  UB := [[1]]
  a := -3
  b := 1
theorem intOK_t5_u3 : IntOK 3 2 1 (1 : ℚ) 3 t5 Dn_t5_u3 := by decide +kernel
theorem ok_t5_u3 : lu_t5_u3.ok t5.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t5 Dn_t5_u3) Dn_t5_u3 = true := by decide +kernel
def Dn_t6_u2 : ℤ := 1
def lu_t6_u2 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[0]]
  LB := [[1]]
  UB := [[1]]
  a := 0
  b := 1
theorem intOK_t6_u2 : IntOK 3 2 1 (1 : ℚ) 2 t6 Dn_t6_u2 := by decide +kernel
theorem ok_t6_u2 : lu_t6_u2.ok t6.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t6 Dn_t6_u2) Dn_t6_u2 = true := by decide +kernel
def Dn_t6_u3 : ℤ := 1
def lu_t6_u3 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[0]]
  LB := [[1]]
  UB := [[1]]
  a := 0
  b := 1
theorem intOK_t6_u3 : IntOK 3 2 1 (1 : ℚ) 3 t6 Dn_t6_u3 := by decide +kernel
theorem ok_t6_u3 : lu_t6_u3.ok t6.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t6 Dn_t6_u3) Dn_t6_u3 = true := by decide +kernel
def Dn_t7_u2 : ℤ := 1
def lu_t7_u2 : LuData where
  LM := [[1]]
  UM := [[2]]
  LA := [[1, 0], [1, 1]]
  UA := [[2, 0], [0, -2]]
  LB := [[1, 0], [1, 1]]
  UB := [[2, 1], [0, 2]]
  a := -4
  b := 4
theorem intOK_t7_u2 : IntOK 3 2 1 (1 : ℚ) 2 t7 Dn_t7_u2 := by decide +kernel
theorem ok_t7_u2 : lu_t7_u2.ok t7.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t7 Dn_t7_u2) Dn_t7_u2 = true := by decide +kernel
def Dn_t7_u3 : ℤ := 1
def lu_t7_u3 : LuData where
  LM := [[1]]
  UM := [[3]]
  LA := [[1, 0], [2, 3]]
  UA := [[3, 0], [0, -6]]
  LB := [[1, 0], [2, 3]]
  UB := [[3, 1], [0, 5]]
  a := -6
  b := 5
theorem intOK_t7_u3 : IntOK 3 2 1 (1 : ℚ) 3 t7 Dn_t7_u3 := by decide +kernel
theorem ok_t7_u3 : lu_t7_u3.ok t7.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t7 Dn_t7_u3) Dn_t7_u3 = true := by decide +kernel
def Dn_t8_u2 : ℤ := 35280
def lu_t8_u2 : LuData where
  LM := [[1, 0, 0], [-1, 44, 0], [-1505, -668, 104048]]
  UM := [[388080, 8820, 5670], [0, 16387560, 105210], [0, 0, 38519277930]]
  LA := [[1, 0, 0, 0], [-1, 44, 0, 0], [-1505, -668, 104048, 0], [-204157021, -90290868, -57423562, 19259638965]]
  UA := [[388080, 8820, 5670, -105840], [0, 16387560, 105210, -4163040], [0, 0, 38519277930, -9608437440], [0, 0, 0, -1761592021044660]]
  LB := [[1, 0, 0, 0], [-1, 44, 0, 0], [-1505, -668, 104048, 0], [-204157021, -90290868, -57423562, 19259638965]]
  UB := [[388080, 8820, 5670, 35280], [0, 16387560, 105210, 1517040], [0, 0, 38519277930, 3594150000], [0, 0, 0, 667066037893920]]
  a := -4894231112068378878000
  b := 1853309573080677936000
theorem intOK_t8_u2 : IntOK 3 2 1 (1 : ℚ) 2 t8 Dn_t8_u2 := by decide +kernel
theorem ok_t8_u2 : lu_t8_u2.ok t8.nodes.length (mkFib 3 2 1 (1 : ℚ) 2 t8 Dn_t8_u2) Dn_t8_u2 = true := by decide +kernel
def Dn_t8_u3 : ℤ := 35280
def lu_t8_u3 : LuData where
  LM := [[1, 0, 0], [-1, 48, 0], [-1649, -732, 124264]]
  UM := [[423360, 8820, 5670], [0, 19571580, 115290], [0, 0, 50388419970]]
  LA := [[1, 0, 0, 0], [-1, 48, 0, 0], [-1649, -732, 124264, 0], [-245094269, -108410644, -68951050, 25194209985]]
  UA := [[423360, 8820, 5670, -105840], [0, 19571580, 115290, -4551120], [0, 0, 50388419970, -11497399200], [0, 0, 0, -2308249800303300]]
  LB := [[1, 0, 0, 0], [-1, 48, 0, 0], [-1649, -732, 124264, 0], [-245094269, -108410644, -68951050, 25194209985]]
  UB := [[423360, 8820, 5670, 35280], [0, 19571580, 115290, 1658160], [0, 0, 50388419970, 4300032240], [0, 0, 0, 873947481896160]]
  a := -6413010420182658390000
  b := 2428088288952101328000
theorem intOK_t8_u3 : IntOK 3 2 1 (1 : ℚ) 3 t8 Dn_t8_u3 := by decide +kernel
theorem ok_t8_u3 : lu_t8_u3.ok t8.nodes.length (mkFib 3 2 1 (1 : ℚ) 3 t8 Dn_t8_u3) Dn_t8_u3 = true := by decide +kernel
-- pair t0 t4 : u0 2,3 cross 3716096, 4997376 ; bezout -5203*c0 + 3869*c1 = 256
theorem bez_t0_t4 : (-5203 : ℤ) * (lu_t0_u2.b * lu_t4_u2.a - lu_t0_u2.a * lu_t4_u2.b) + (3869 : ℤ) * (lu_t0_u3.b * lu_t4_u3.a - lu_t0_u3.a * lu_t4_u3.b) = 256 := by decide +kernel
-- pair t0 t7 : u0 2,3 cross 1200, 1452 ; bezout 23*c0 + -19*c1 = 12
theorem bez_t0_t7 : (23 : ℤ) * (lu_t0_u2.b * lu_t7_u2.a - lu_t0_u2.a * lu_t7_u2.b) + (-19 : ℤ) * (lu_t0_u3.b * lu_t7_u3.a - lu_t0_u3.a * lu_t7_u3.b) = 12 := by decide +kernel
-- pair t1 t2 : u0 2,3 cross 5246461909847968704568967762165437440000, 15902438328279976406139067857894097920000 ; bezout -85897310075120862587*c0 + 28338859498426696420*c1 = 85400990608389120000
theorem bez_t1_t2 : (-85897310075120862587 : ℤ) * (lu_t1_u2.b * lu_t2_u2.a - lu_t1_u2.a * lu_t2_u2.b) + (28338859498426696420 : ℤ) * (lu_t1_u3.b * lu_t2_u3.a - lu_t1_u3.a * lu_t2_u3.b) = 85400990608389120000 := by decide +kernel
-- pair t1 t8 : u0 2,3 cross -235626641214831939028126722512981925814560000000, -455258785810176841641493418375778336379680000000 ; bezout -778114433223253260654450*c0 + 402725869540109211388637*c1 = 130770266869095840000000
theorem bez_t1_t8 : (-778114433223253260654450 : ℤ) * (lu_t1_u2.b * lu_t8_u2.a - lu_t1_u2.a * lu_t8_u2.b) + (402725869540109211388637 : ℤ) * (lu_t1_u3.b * lu_t8_u3.a - lu_t1_u3.a * lu_t8_u3.b) = 130770266869095840000000 := by decide +kernel
-- pair t2 t3 : u0 2,3 cross -48776517441183161032704, -78588894332872686034944 ; bezout -369560348435*c0 + 229369135856*c1 = 100370866176
theorem bez_t2_t3 : (-369560348435 : ℤ) * (lu_t2_u2.b * lu_t3_u2.a - lu_t2_u2.a * lu_t3_u2.b) + (229369135856 : ℤ) * (lu_t2_u3.b * lu_t3_u3.a - lu_t2_u3.a * lu_t3_u3.b) = 100370866176 := by decide +kernel
-- pair t2 t4 : u0 2,3 cross 893216684212715520, 2206622615523508224 ; bezout -27398263*c0 + 11090517*c1 = 4096770048
theorem bez_t2_t4 : (-27398263 : ℤ) * (lu_t2_u2.b * lu_t4_u2.a - lu_t2_u2.a * lu_t4_u2.b) + (11090517 : ℤ) * (lu_t2_u3.b * lu_t4_u3.a - lu_t2_u3.a * lu_t4_u3.b) = 4096770048 := by decide +kernel
-- pair t2 t8 : u0 2,3 cross -549246805682964510946059882259200000, -961483089546580089616197088451328000 ; bezout -5330604869275737*c0 + 3045105762794504*c1 = 2352884435129088000
theorem bez_t2_t8 : (-5330604869275737 : ℤ) * (lu_t2_u2.b * lu_t8_u2.a - lu_t2_u2.a * lu_t8_u2.b) + (3045105762794504 : ℤ) * (lu_t2_u3.b * lu_t8_u3.a - lu_t2_u3.a * lu_t8_u3.b) = 2352884435129088000 := by decide +kernel
-- pair t3 t0 : u0 2,3 cross -1946113792, -2546914944 ; bezout -64262*c0 + 49103*c1 = 6272
theorem bez_t3_t0 : (-64262 : ℤ) * (lu_t3_u2.b * lu_t0_u2.a - lu_t3_u2.a * lu_t0_u2.b) + (49103 : ℤ) * (lu_t3_u3.b * lu_t0_u3.a - lu_t3_u3.a * lu_t0_u3.b) = 6272 := by decide +kernel
-- pair t3 t2 : u0 2,3 cross 48776517441183161032704, 78588894332872686034944 ; bezout 369560348435*c0 + -229369135856*c1 = 100370866176
theorem bez_t3_t2 : (369560348435 : ℤ) * (lu_t3_u2.b * lu_t2_u2.a - lu_t3_u2.a * lu_t2_u2.b) + (-229369135856 : ℤ) * (lu_t3_u3.b * lu_t2_u3.a - lu_t3_u3.a * lu_t2_u3.b) = 100370866176 := by decide +kernel
-- pair t3 t4 : u0 2,3 cross 3274527105024, 4768847462400 ; bezout 1561801*c0 + -1072410*c1 = 1204224
theorem bez_t3_t4 : (1561801 : ℤ) * (lu_t3_u2.b * lu_t4_u2.a - lu_t3_u2.a * lu_t4_u2.b) + (-1072410 : ℤ) * (lu_t3_u3.b * lu_t4_u3.a - lu_t3_u3.a * lu_t4_u3.b) = 1204224 := by decide +kernel
-- pair t4 t0 : u0 2,3 cross -3716096, -4997376 ; bezout 5203*c0 + -3869*c1 = 256
theorem bez_t4_t0 : (5203 : ℤ) * (lu_t4_u2.b * lu_t0_u2.a - lu_t4_u2.a * lu_t0_u2.b) + (-3869 : ℤ) * (lu_t4_u3.b * lu_t0_u3.a - lu_t4_u3.a * lu_t0_u3.b) = 256 := by decide +kernel
-- pair t4 t3 : u0 2,3 cross -3274527105024, -4768847462400 ; bezout -1561801*c0 + 1072410*c1 = 1204224
theorem bez_t4_t3 : (-1561801 : ℤ) * (lu_t4_u2.b * lu_t3_u2.a - lu_t4_u2.a * lu_t3_u2.b) + (1072410 : ℤ) * (lu_t4_u3.b * lu_t3_u3.a - lu_t4_u3.a * lu_t3_u3.b) = 1204224 := by decide +kernel
-- pair t5 t6 : u0 2,3 cross 3, 3 ; bezout 0*c0 + 1*c1 = 3
theorem bez_t5_t6 : (0 : ℤ) * (lu_t5_u2.b * lu_t6_u2.a - lu_t5_u2.a * lu_t6_u2.b) + (1 : ℤ) * (lu_t5_u3.b * lu_t6_u3.a - lu_t5_u3.a * lu_t6_u3.b) = 3 := by decide +kernel
-- pair t5 t7 : u0 2,3 cross 8, 9 ; bezout -1*c0 + 1*c1 = 1
theorem bez_t5_t7 : (-1 : ℤ) * (lu_t5_u2.b * lu_t7_u2.a - lu_t5_u2.a * lu_t7_u2.b) + (1 : ℤ) * (lu_t5_u3.b * lu_t7_u3.a - lu_t5_u3.a * lu_t7_u3.b) = 1 := by decide +kernel
-- pair t6 t5 : u0 2,3 cross -3, -3 ; bezout 0*c0 + -1*c1 = 3
theorem bez_t6_t5 : (0 : ℤ) * (lu_t6_u2.b * lu_t5_u2.a - lu_t6_u2.a * lu_t5_u2.b) + (-1 : ℤ) * (lu_t6_u3.b * lu_t5_u3.a - lu_t6_u3.a * lu_t5_u3.b) = 3 := by decide +kernel
-- pair t7 t0 : u0 2,3 cross -1200, -1452 ; bezout -23*c0 + 19*c1 = 12
theorem bez_t7_t0 : (-23 : ℤ) * (lu_t7_u2.b * lu_t0_u2.a - lu_t7_u2.a * lu_t0_u2.b) + (19 : ℤ) * (lu_t7_u3.b * lu_t0_u3.a - lu_t7_u3.a * lu_t0_u3.b) = 12 := by decide +kernel
-- pair t7 t5 : u0 2,3 cross -8, -9 ; bezout 1*c0 + -1*c1 = 1
theorem bez_t7_t5 : (1 : ℤ) * (lu_t7_u2.b * lu_t5_u2.a - lu_t7_u2.a * lu_t5_u2.b) + (-1 : ℤ) * (lu_t7_u3.b * lu_t5_u3.a - lu_t7_u3.a * lu_t5_u3.b) = 1 := by decide +kernel
-- pair t8 t1 : u0 2,3 cross 235626641214831939028126722512981925814560000000, 455258785810176841641493418375778336379680000000 ; bezout 778114433223253260654450*c0 + -402725869540109211388637*c1 = 130770266869095840000000
theorem bez_t8_t1 : (778114433223253260654450 : ℤ) * (lu_t8_u2.b * lu_t1_u2.a - lu_t8_u2.a * lu_t1_u2.b) + (-402725869540109211388637 : ℤ) * (lu_t8_u3.b * lu_t1_u3.a - lu_t8_u3.a * lu_t1_u3.b) = 130770266869095840000000 := by decide +kernel
-- pair t8 t2 : u0 2,3 cross 549246805682964510946059882259200000, 961483089546580089616197088451328000 ; bezout 5330604869275737*c0 + -3045105762794504*c1 = 2352884435129088000
theorem bez_t8_t2 : (5330604869275737 : ℤ) * (lu_t8_u2.b * lu_t2_u2.a - lu_t8_u2.a * lu_t2_u2.b) + (-3045105762794504 : ℤ) * (lu_t8_u3.b * lu_t2_u3.a - lu_t8_u3.a * lu_t2_u3.b) = 2352884435129088000 := by decide +kernel
-- pair t8 t3 : u0 2,3 cross -9635926153699470065805504000, -15135501719372483598206400000 ; bezout 92454634998648*c0 + -58860687404497*c1 = 38423222208000
theorem bez_t8_t3 : (92454634998648 : ℤ) * (lu_t8_u2.b * lu_t3_u2.a - lu_t8_u2.a * lu_t3_u2.b) + (-58860687404497 : ℤ) * (lu_t8_u3.b * lu_t3_u3.a - lu_t8_u3.a * lu_t3_u3.b) = 38423222208000 := by decide +kernel

end CatalanCore.Uniform.Content.UFFamily2.Data.Thirds0
