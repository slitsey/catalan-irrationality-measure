module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Shape
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r16_0.In
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.LatticeGate
def decodePairs : List ℤ → List ℤ
  | a::e::rest => a*2^e.toNat :: decodePairs rest
  | _ => []
def denominators : Array ℤ := (decodePairs (raw_ints% [1,96,1,0,1,1,1,2,1,3,5,1,5,2,25,4,125,4,12509999259123,0,20849998765205,0,37529997777369,0,62549996295615,0,112589993332107,0,187649988886845,0,562949966660535,0,187649988886845,2,562949966660535,1,562949966660535,2,3490289793295317,0,562949966660535,3,1163429931098439,3,3490289793295317,3,33739468001854731,0,17451448966476585,3,9695249425820325,4,81627745165777575,1,114278843232088605,1,29085748277460975,3,18355669120180035,4,3231749808606775,7,17451448966476585,5,281162233348789425,1,87257244832382925,3,281162233348789425,2,87257244832382925,4,708528828038949351,1,17451448966476585,7,2601558595928453875,0,87257244832382925,5,3542644140194746755,0,2530460100139104825,1,2530460100139104825,2,708528828038949351,4,6376759452350544159,1,1910089236879195255,3,17015162742314670375,0,31883797261752720795,0,47752230921979881375,0,3542644140194746755,4,506092020027820965,7,47752230921979881375,1,113870704506259717125,0,31883797261752720795,2,17015162742314670375,3,19737588781085017635,3,2530460100139104825,6,11842553268651010581,4,37956901502086572375,3,19737588781085017635,4,26089916204882494575,4,756607569941592342675,0,59212766343255052905,4,493439719527125440875,1,547888240302532386075,1,73220087413702484775,4,174601746909598232925,3,3542644140194746755,9,453964541964955405605,2,2530460100139104825,10,1480319158581376322625,1,398091982953883971069,3,432708677123786925075,3,493439719527125440875,3,31883797261752720795,7,2269822709824777028025,1,571971239876270073375,3,1222212228367187630475,2,3177751793754687839235,1,453964541964955405605,4,15653949722929496745,9,2037020380611979384125,2,1105811063760788808525,3,5296252989591146398725,1,679006793537326461375,4,873008734547991164625,4,15888758968773439196175,0,2269822709824777028025,3,18798788083933409744925,0,1222212228367187630475,4,37529997777369,29,19737588781085017635,10,3317433191282366425575,3,2269822709824777028025,4,56396364251800229234775,0,9952299573847099276725,3,187649988886845,29,59212766343255052905,11,16587165956411832127875,3,169189092755400687704325,0,6376759452350544159,15,493439719527125440875,9,562949966660535,29,19737588781085017635,17,453964541964955405605,13,296063831716275264525,15,3317433191282366425575,13,407404076122395876825,17,87257244832382925,30,101218404005564193,30,17451448966476585,33,98687943905425088175,21,101218404005564193,31,15888758968773439196175,14,1315839252072334509,28,1990459914769419855345,18,17451448966476585,35,56396364251800229234775,15,3542644140194746755,29,3317433191282366425575,20,113870704506259717125,25,87257244832382925,36,6111061141835938152375,20,2269822709824777028025,22,9952299573847099276725,20,101218404005564193,37,2269822709824777028025,23,2269822709824777028025,24,493439719527125440875,27,15888758968773439196175,22,65710334858450947875,30,3177751793754687839235,25,2269822709824777028025,26,2530460100139104825,36,3542644140194746755,39,1253252538928893982995,32,6579196260361672545,40,3317433191282366425575,32,112589993332107,57,15917410307326627125,40,16587165956411832127875,31,321041921737003202475,37,190657079958756691125,38,174601746909598232925,40,3045078339517575,57,34920349381919646585,44,1480319158581376322625,39,2037020380611979384125,41,562949966660535,64,2269822709824777028025,43,1028509589088797445,55,756607569941592342675,46,29085748277460975,61,571971239876270073375,47,164479906509041813625,49,98687943905425088175,50,2269822709824777028025,46,17451448966476585,63,87257244832382925,61,708528828038949351,58,6111061141835938152375,45,15888758968773439196175,44,708528828038949351,60,59212766343255052905,54,18798788083933409744925,46,9952299573847099276725,47,663486638256473285115,51,9952299573847099276725,48,2530460100139104825,60,679006793537326461375,52,6376759452350544159,59,59212766343255052905,56,1222212228367187630475,52,453964541964955405605,55,493439719527125440875,55,2269822709824777028025,53,493439719527125440875,56])).toArray
def denomAt (i : ℕ) : ℤ := denominators[i]?.getD 0
def parentScale : ℤ := denomAt 0
def sharedTableCheck : Bool := decide (denominators.size=177 ∧ parentScale=2^96) && denominators.toList.all (fun n => decide (0<n))
def qv0 : ℚ := ((((raw_ints% [111])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 6:ℚ)
def qv1 : ℚ := ((((raw_ints% [0])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 1:ℚ)
def qv2 : ℚ := ((((raw_ints% [1])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 1:ℚ)
def qv3 : ℚ := ((((raw_ints% [-126394419613409])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv4 : ℚ := ((((raw_ints% [-14834150121739])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 15:ℚ)
def qv5 : ℚ := ((((raw_ints% [62647828584847])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv6 : ℚ := ((((raw_ints% [-18012308538811])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv7 : ℚ := ((((raw_ints% [8881974204685])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 13:ℚ)
def qv8 : ℚ := ((((raw_ints% [-7048322324077])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 13:ℚ)
def qv9 : ℚ := ((((raw_ints% [1897162012409])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 11:ℚ)
def qv10 : ℚ := ((((raw_ints% [-22627544362663])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv11 : ℚ := ((((raw_ints% [1867451061521])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 13:ℚ)
def qv12 : ℚ := ((((raw_ints% [-7562455312997])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv13 : ℚ := ((((raw_ints% [12844324792577])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv14 : ℚ := ((((raw_ints% [-2651310134551])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 15:ℚ)
def qv15 : ℚ := ((((raw_ints% [9242767752743])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv16 : ℚ := ((((raw_ints% [-3878880298709])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv17 : ℚ := ((((raw_ints% [6900528619919])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv18 : ℚ := ((((raw_ints% [-1956935787577])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv19 : ℚ := ((((raw_ints% [5295806451647])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv20 : ℚ := ((((raw_ints% [-1519794640529])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv21 : ℚ := ((((raw_ints% [38348715377])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 10:ℚ)
def qv22 : ℚ := ((((raw_ints% [-1804401936719])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv23 : ℚ := ((((raw_ints% [1091003915333])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv24 : ℚ := ((((raw_ints% [-482476234409])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 14:ℚ)
def qv25 : ℚ := ((((raw_ints% [863034492049])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv26 : ℚ := ((((raw_ints% [-2343406400471])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 15:ℚ)
def qv27 : ℚ := ((((raw_ints% [252927876997])).headD 0 * (2:ℤ)^5):ℚ)/(denomAt 15:ℚ)
def qv28 : ℚ := ((((raw_ints% [-159170489207])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 14:ℚ)
def qv29 : ℚ := ((((raw_ints% [508831728269])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 14:ℚ)
def qv30 : ℚ := ((((raw_ints% [-39247117579])).headD 0 * (2:ℤ)^5):ℚ)/(denomAt 13:ℚ)
def qv31 : ℚ := ((((raw_ints% [527237194787])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv32 : ℚ := ((((raw_ints% [-146023276877])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 12:ℚ)
def qv33 : ℚ := ((((raw_ints% [140114217653])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 15:ℚ)
def qv34 : ℚ := ((((raw_ints% [-12088134583])).headD 0 * (2:ℤ)^7):ℚ)/(denomAt 14:ℚ)
def qv35 : ℚ := ((((raw_ints% [-5])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv36 : ℚ := ((((raw_ints% [3])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv37 : ℚ := ((((raw_ints% [111])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 5:ℚ)
def qv38 : ℚ := ((((raw_ints% [5])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv39 : ℚ := ((((raw_ints% [-999])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 7:ℚ)
def qv40 : ℚ := ((((raw_ints% [1])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv41 : ℚ := ((((raw_ints% [-5377])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 8:ℚ)
def qv42 : ℚ := ((((raw_ints% [-1])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv43 : ℚ := ((((raw_ints% [40263869915405])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 13:ℚ)
def qv44 : ℚ := ((((raw_ints% [5690942847424603])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 17:ℚ)
def qv45 : ℚ := ((((raw_ints% [142187078588625841])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 24:ℚ)
def qv46 : ℚ := ((((raw_ints% [3450703603019116951])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 33:ℚ)
def qv47 : ℚ := ((((raw_ints% [2595672587078340151])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 32:ℚ)
def qv48 : ℚ := ((((raw_ints% [12042552488725415])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 19:ℚ)
def qv49 : ℚ := ((((raw_ints% [45323065219140753473])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv50 : ℚ := ((((raw_ints% [64130416744558663687])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 45:ℚ)
def qv51 : ℚ := ((((raw_ints% [4436591002007391059693])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 63:ℚ)
def qv52 : ℚ := ((((raw_ints% [17200215556799478187291])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 73:ℚ)
def qv53 : ℚ := ((((raw_ints% [7439068170384228400829])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 68:ℚ)
def qv54 : ℚ := ((((raw_ints% [1652971411648931997449])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 60:ℚ)
def qv55 : ℚ := ((((raw_ints% [63257838748197666275881])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 86:ℚ)
def qv56 : ℚ := ((((raw_ints% [44229502310722359254279])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 84:ℚ)
def qv57 : ℚ := ((((raw_ints% [36575115191964534668639])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 82:ℚ)
def qv58 : ℚ := ((((raw_ints% [14298988757114196399941])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 72:ℚ)
def qv59 : ℚ := ((((raw_ints% [114811400609427326969093])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 94:ℚ)
def qv60 : ℚ := ((((raw_ints% [105931673405300543611627])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 92:ℚ)
def qv61 : ℚ := ((((raw_ints% [520205210679058855520129])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 98:ℚ)
def qv62 : ℚ := ((((raw_ints% [31543239280220683624639])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 81:ℚ)
def qv63 : ℚ := ((((raw_ints% [15262784040830034879431])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 86:ℚ)
def qv64 : ℚ := ((((raw_ints% [27772343729077682180891])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 79:ℚ)
def qv65 : ℚ := ((((raw_ints% [5313631594042136316433])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 66:ℚ)
def qv66 : ℚ := ((((raw_ints% [14910899518242521407931])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 73:ℚ)
def qv67 : ℚ := ((((raw_ints% [426035613530685168751])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 52:ℚ)
def qv68 : ℚ := ((((raw_ints% [1167972311955740503117])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 59:ℚ)
def qv69 : ℚ := ((((raw_ints% [465760831896643340257])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 53:ℚ)
def qv70 : ℚ := ((((raw_ints% [40874221303360276543])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 43:ℚ)
def qv71 : ℚ := ((((raw_ints% [36046383395710983829])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv72 : ℚ := ((((raw_ints% [4914126456317810299])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv73 : ℚ := ((((raw_ints% [15677006348684761])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv74 : ℚ := ((((raw_ints% [646206203052889])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 14:ℚ)
def qv75 : ℚ := ((((raw_ints% [1664817941059])).headD 0 * (2:ℤ)^7):ℚ)/(denomAt 12:ℚ)
def qv76 : ℚ := ((((raw_ints% [632373975680423])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 14:ℚ)
def qv77 : ℚ := ((((raw_ints% [15013059434806393])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv78 : ℚ := ((((raw_ints% [4602361662777280361])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv79 : ℚ := ((((raw_ints% [3663787459866904883])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 34:ℚ)
def qv80 : ℚ := ((((raw_ints% [182307399171559405621])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 49:ℚ)
def qv81 : ℚ := ((((raw_ints% [101148566415268490239])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 47:ℚ)
def qv82 : ℚ := ((((raw_ints% [2962767851129536570301])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 62:ℚ)
def qv83 : ℚ := ((((raw_ints% [36803023956919860707])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 48:ℚ)
def qv84 : ℚ := ((((raw_ints% [12005606771965712121053])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 73:ℚ)
def qv85 : ℚ := ((((raw_ints% [54548658856324499261801])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 87:ℚ)
def qv86 : ℚ := ((((raw_ints% [107891955443146821633949])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 93:ℚ)
def qv87 : ℚ := ((((raw_ints% [3221599573978261956239])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 64:ℚ)
def qv88 : ℚ := ((((raw_ints% [14221081768176313010273])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 77:ℚ)
def qv89 : ℚ := ((((raw_ints% [381478605037852755803273])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 98:ℚ)
def qv90 : ℚ := ((((raw_ints% [225820530641541040963009])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 95:ℚ)
def qv91 : ℚ := ((((raw_ints% [236317045566432931974847])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 99:ℚ)
def qv92 : ℚ := ((((raw_ints% [218811209807555151142861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 95:ℚ)
def qv93 : ℚ := ((((raw_ints% [12368169555738633870209])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 76:ℚ)
def qv94 : ℚ := ((((raw_ints% [37155476518770244192979])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 85:ℚ)
def qv95 : ℚ := ((((raw_ints% [27760265241302679986287])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 83:ℚ)
def qv96 : ℚ := ((((raw_ints% [93887971054013654551049])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 93:ℚ)
def qv97 : ℚ := ((((raw_ints% [1931159667137399555429])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 61:ℚ)
def qv98 : ℚ := ((((raw_ints% [765393107271439235579])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 58:ℚ)
def qv99 : ℚ := ((((raw_ints% [7366668907265733093611])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 70:ℚ)
def qv100 : ℚ := ((((raw_ints% [387498533824040971669])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 55:ℚ)
def qv101 : ℚ := ((((raw_ints% [8565311472262342541])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 40:ℚ)
def qv102 : ℚ := ((((raw_ints% [543877782130415233])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 27:ℚ)
def qv103 : ℚ := ((((raw_ints% [382067871788411249])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 26:ℚ)
def qv104 : ℚ := ((((raw_ints% [535354974061758139])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 28:ℚ)
def qv105 : ℚ := ((((raw_ints% [21051133158080323])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv106 : ℚ := ((((raw_ints% [5007499906866049])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 18:ℚ)
def qv107 : ℚ := ((((raw_ints% [615582579148741])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 15:ℚ)
def qv108 : ℚ := ((((raw_ints% [1613940453171269])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 16:ℚ)
def qv109 : ℚ := ((((raw_ints% [295222857499526837])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 24:ℚ)
def qv110 : ℚ := ((((raw_ints% [1452203715720190093])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 33:ℚ)
def qv111 : ℚ := ((((raw_ints% [10361029319346614483])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 41:ℚ)
def qv112 : ℚ := ((((raw_ints% [2855049861660696685])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 36:ℚ)
def qv113 : ℚ := ((((raw_ints% [66871316264309335])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 23:ℚ)
def qv114 : ℚ := ((((raw_ints% [307575641104945967963])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 55:ℚ)
def qv115 : ℚ := ((((raw_ints% [182576261308184044241])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 51:ℚ)
def qv116 : ℚ := ((((raw_ints% [254970215518550901773])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 54:ℚ)
def qv117 : ℚ := ((((raw_ints% [8319464133398266296449])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 75:ℚ)
def qv118 : ℚ := ((((raw_ints% [2098819115471032931489])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 65:ℚ)
def qv119 : ℚ := ((((raw_ints% [6957764488958737517677])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 86:ℚ)
def qv120 : ℚ := ((((raw_ints% [33529751483920192922503])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 89:ℚ)
def qv121 : ℚ := ((((raw_ints% [223128091634021116603199])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 98:ℚ)
def qv122 : ℚ := ((((raw_ints% [5261249579096624759999])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 71:ℚ)
def qv123 : ℚ := ((((raw_ints% [15270894273602840139683])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 88:ℚ)
def qv124 : ℚ := ((((raw_ints% [127149551405884925628319])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 95:ℚ)
def qv125 : ℚ := ((((raw_ints% [207873447310802951790029])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 98:ℚ)
def qv126 : ℚ := ((((raw_ints% [1992484407983306689])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 38:ℚ)
def qv127 : ℚ := ((((raw_ints% [9487253546083374284857])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 78:ℚ)
def qv128 : ℚ := ((((raw_ints% [52701634585237243165523])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 93:ℚ)
def qv129 : ℚ := ((((raw_ints% [25593795564158353023659])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 87:ℚ)
def qv130 : ℚ := ((((raw_ints% [5408557561058123209831])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 73:ℚ)
def qv131 : ℚ := ((((raw_ints% [177397974010862063])).headD 0 * (2:ℤ)^7):ℚ)/(denomAt 46:ℚ)
def qv132 : ℚ := ((((raw_ints% [246816929619782937895])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 57:ℚ)
def qv133 : ℚ := ((((raw_ints% [162361570710138120353])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 53:ℚ)
def qv134 : ℚ := ((((raw_ints% [365371190957341543])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 29:ℚ)
def qv135 : ℚ := ((((raw_ints% [12286842511790275361])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv136 : ℚ := ((((raw_ints% [183295054856121151])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv137 : ℚ := ((((raw_ints% [32031121891084085])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 22:ℚ)
def qv138 : ℚ := ((((raw_ints% [625549138950791])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 15:ℚ)
def qv139 : ℚ := ((((raw_ints% [75626648758081])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 15:ℚ)
def qv140 : ℚ := ((((raw_ints% [3])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 3:ℚ)
def qv141 : ℚ := ((((raw_ints% [1189490431243153])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 17:ℚ)
def qv142 : ℚ := ((((raw_ints% [579727930920937753])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv143 : ℚ := ((((raw_ints% [421824526661726393])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 30:ℚ)
def qv144 : ℚ := ((((raw_ints% [162188795343566436803])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 56:ℚ)
def qv145 : ℚ := ((((raw_ints% [1783920769794833636231])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 67:ℚ)
def qv146 : ℚ := ((((raw_ints% [3942201929183662802239])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 74:ℚ)
def qv147 : ℚ := ((((raw_ints% [115076545074877175453929])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 97:ℚ)
def qv148 : ℚ := ((((raw_ints% [235598252396097634565417])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 101:ℚ)
def qv149 : ℚ := ((((raw_ints% [18528904900585711638083])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 91:ℚ)
def qv150 : ℚ := ((((raw_ints% [7225767882968175646439])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 80:ℚ)
def qv151 : ℚ := ((((raw_ints% [3297860986279963180787243])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 104:ℚ)
def qv152 : ℚ := ((((raw_ints% [227075069601595437937440799])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 113:ℚ)
def qv153 : ℚ := ((((raw_ints% [45806141052643145634967723])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 107:ℚ)
def qv154 : ℚ := ((((raw_ints% [22911766545824912294425981])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 106:ℚ)
def qv155 : ℚ := ((((raw_ints% [431955706245803467321518367])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 115:ℚ)
def qv156 : ℚ := ((((raw_ints% [1500343123201514987978296213])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 117:ℚ)
def qv157 : ℚ := ((((raw_ints% [8296858773943017239970066697])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 124:ℚ)
def qv158 : ℚ := ((((raw_ints% [2703903726262773737356522991])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 119:ℚ)
def qv159 : ℚ := ((((raw_ints% [4861896483136609111300786421])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 122:ℚ)
def qv160 : ℚ := ((((raw_ints% [49284865742764292607867738823])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 129:ℚ)
def qv161 : ℚ := ((((raw_ints% [27419897123139766362981348491])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 127:ℚ)
def qv162 : ℚ := ((((raw_ints% [6669722389484453881227644767])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 123:ℚ)
def qv163 : ℚ := ((((raw_ints% [45137608752242507088717328189])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 128:ℚ)
def qv164 : ℚ := ((((raw_ints% [2534257806612076615115953427])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 120:ℚ)
def qv165 : ℚ := ((((raw_ints% [228167860727336204190609469])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 114:ℚ)
def qv166 : ℚ := ((((raw_ints% [1197706522564394867524474453])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 118:ℚ)
def qv167 : ℚ := ((((raw_ints% [133562423222625200759455531])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 112:ℚ)
def qv168 : ℚ := ((((raw_ints% [65202823717715214394341715])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 109:ℚ)
def qv169 : ℚ := ((((raw_ints% [54886368032316797785861277])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 108:ℚ)
def qv170 : ℚ := ((((raw_ints% [85703548001028968967632447])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 110:ℚ)
def qv171 : ℚ := ((((raw_ints% [11227953072198124110547])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 90:ℚ)
def qv172 : ℚ := ((((raw_ints% [163857060364603404038101])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 102:ℚ)
def qv173 : ℚ := ((((raw_ints% [7])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 4:ℚ)
def qv174 : ℚ := ((((raw_ints% [53858647501806391742683])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 96:ℚ)
def qv175 : ℚ := ((((raw_ints% [315945640325694304298897231])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 116:ℚ)
def qv176 : ℚ := ((((raw_ints% [3112081412085817299014406059])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 121:ℚ)
def qv177 : ℚ := ((((raw_ints% [88837487830901003891077778281])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 133:ℚ)
def qv178 : ℚ := ((((raw_ints% [6990532537112691793233777655])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 125:ℚ)
def qv179 : ℚ := ((((raw_ints% [961861567603597054633203739291])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 134:ℚ)
def qv180 : ℚ := ((((raw_ints% [3508274337730603977791631273629])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 136:ℚ)
def qv181 : ℚ := ((((raw_ints% [387234146327342624889410113340609])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 146:ℚ)
def qv182 : ℚ := ((((raw_ints% [8163414160951329643040994071747])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 139:ℚ)
def qv183 : ℚ := ((((raw_ints% [9121584754443956214532079647882259])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 149:ℚ)
def qv184 : ℚ := ((((raw_ints% [274689247973793868567691415014347])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 145:ℚ)
def qv185 : ℚ := ((((raw_ints% [122240665892740137840041867923899589])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 161:ℚ)
def qv186 : ℚ := ((((raw_ints% [91917678996588250690921721775601411])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 160:ℚ)
def qv187 : ℚ := ((((raw_ints% [33626078112384218734401273597619651])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 153:ℚ)
def qv188 : ℚ := ((((raw_ints% [1143213320614120560440466719062173277])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 167:ℚ)
def qv189 : ℚ := ((((raw_ints% [527404436779188609197508087607815943])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 164:ℚ)
def qv190 : ℚ := ((((raw_ints% [545661884640393501486101958111174343])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 165:ℚ)
def qv191 : ℚ := ((((raw_ints% [568955564467459098033527513911576997])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 166:ℚ)
def qv192 : ℚ := ((((raw_ints% [1138985431556168888372394307937845969])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 169:ℚ)
def qv193 : ℚ := ((((raw_ints% [2006566341455998976176104092862544567])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 172:ℚ)
def qv194 : ℚ := ((((raw_ints% [7299838939979735535744057525047765371])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 175:ℚ)
def qv195 : ℚ := ((((raw_ints% [5724045652960166702706786628403335381])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 173:ℚ)
def qv196 : ℚ := ((((raw_ints% [12204410492609540250336465427370412167])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 176:ℚ)
def qv197 : ℚ := ((((raw_ints% [5987520764630777607662980266778044137])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 174:ℚ)
def qv198 : ℚ := ((((raw_ints% [1410216804160138516928000506654880189])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 171:ℚ)
def qv199 : ℚ := ((((raw_ints% [1192066844191228552903160419169176973])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 170:ℚ)
def qv200 : ℚ := ((((raw_ints% [259752553736965166000580445265409533])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 162:ℚ)
def qv201 : ℚ := ((((raw_ints% [908676551983537717017196457782555847])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 168:ℚ)
def qv202 : ℚ := ((((raw_ints% [20429852568890051357784595776810143])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 152:ℚ)
def qv203 : ℚ := ((((raw_ints% [47860030133146127440271191695998221])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 157:ℚ)
def qv204 : ℚ := ((((raw_ints% [3006969270250744887354571312060439])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 148:ℚ)
def qv205 : ℚ := ((((raw_ints% [4563600875410208291129697949847])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 138:ℚ)
def qv206 : ℚ := ((((raw_ints% [2834439850274321725291442063743721])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 148:ℚ)
def qv207 : ℚ := ((((raw_ints% [42511618113877009416314184998179963])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 157:ℚ)
def qv208 : ℚ := ((((raw_ints% [51249519799320277898808356960326561])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 158:ℚ)
def qv209 : ℚ := ((((raw_ints% [107417903843901317032256991863471])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 144:ℚ)
def qv210 : ℚ := ((((raw_ints% [47857438928986605859743392657474011])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 159:ℚ)
def qv211 : ℚ := ((((raw_ints% [8283082104760129377378070325946019])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 150:ℚ)
def qv212 : ℚ := ((((raw_ints% [226668071622810052185541403956350371])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 163:ℚ)
def qv213 : ℚ := ((((raw_ints% [18654736462969524989620140870750581])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 154:ℚ)
def qv214 : ℚ := ((((raw_ints% [21189297285076317540446926977375493])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 155:ℚ)
def qv215 : ℚ := ((((raw_ints% [28828200124771668359963416932077557])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 156:ℚ)
def qv216 : ℚ := ((((raw_ints% [9110818225817999161320419206823723])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 151:ℚ)
def qv217 : ℚ := ((((raw_ints% [31268551920993655855670094300409])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 143:ℚ)
def qv218 : ℚ := ((((raw_ints% [698590289664530910215637004249379])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 147:ℚ)
def qv219 : ℚ := ((((raw_ints% [7884643877579727296302083496273])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 142:ℚ)
def qv220 : ℚ := ((((raw_ints% [6455283742277787123610071111949])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 141:ℚ)
def qv221 : ℚ := ((((raw_ints% [771065452144866131657521546801])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 135:ℚ)
def qv222 : ℚ := ((((raw_ints% [2006396086407263750817706453139])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 137:ℚ)
def qv223 : ℚ := ((((raw_ints% [4926146789867574857294893522739])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 140:ℚ)
def qv224 : ℚ := ((((raw_ints% [9509739705986261977863478373])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 130:ℚ)
def qv225 : ℚ := ((((raw_ints% [13784414385669368746329581747])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 131:ℚ)
def qv226 : ℚ := ((((raw_ints% [18402840404171793812828759203])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 132:ℚ)
def qv227 : ℚ := ((((raw_ints% [2069687292682766893621017421])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 126:ℚ)
def qv228 : ℚ := ((((raw_ints% [19204943411746884195787873])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 111:ℚ)
def qv229 : ℚ := ((((raw_ints% [716393516970079559298331])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 105:ℚ)
def qv230 : ℚ := ((((raw_ints% [139127598284589214535809])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 103:ℚ)
def qv231 : ℚ := ((((raw_ints% [7491644711832130931653])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 100:ℚ)
def qv232 : ℚ := ((((raw_ints% [1581260522431670887])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 50:ℚ)
def qv233 : ℚ := ((((raw_ints% [61869513151203205723])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 69:ℚ)
def qv234 : ℚ := ((((raw_ints% [101702233653841853])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 39:ℚ)
def qv235 : ℚ := ((((raw_ints% [128143223585496697])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 37:ℚ)
def qv236 : ℚ := ((((raw_ints% [6285182677357])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 14:ℚ)
def qv237 : ℚ := ((((raw_ints% [525640950121])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 12:ℚ)
def qv238 : ℚ := ((((raw_ints% [-82839273676121])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 15:ℚ)
def qv239 : ℚ := ((((raw_ints% [3688181724229])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 9:ℚ)
def qv240 : ℚ := ((((raw_ints% [858760048831])).headD 0 * (2:ℤ)^12):ℚ)/(denomAt 15:ℚ)
def qv241 : ℚ := ((((raw_ints% [-3412358653145833])).headD 0 * (2:ℤ)^5):ℚ)/(denomAt 15:ℚ)
def qv242 : ℚ := ((((raw_ints% [-738212629066237])).headD 0 * (2:ℤ)^8):ℚ)/(denomAt 15:ℚ)
def qv243 : ℚ := ((((raw_ints% [1121984466834439])).headD 0 * (2:ℤ)^7):ℚ)/(denomAt 10:ℚ)
def qv244 : ℚ := ((((raw_ints% [3037413428531483])).headD 0 * (2:ℤ)^9):ℚ)/(denomAt 14:ℚ)
def qv245 : ℚ := ((((raw_ints% [-35215818119462671])).headD 0 * (2:ℤ)^11):ℚ)/(denomAt 15:ℚ)
def qv246 : ℚ := ((((raw_ints% [-6358396830981493])).headD 0 * (2:ℤ)^11):ℚ)/(denomAt 13:ℚ)
def qv247 : ℚ := ((((raw_ints% [79024582468577387])).headD 0 * (2:ℤ)^11):ℚ)/(denomAt 13:ℚ)
def qv248 : ℚ := ((((raw_ints% [27889755668625353])).headD 0 * (2:ℤ)^12):ℚ)/(denomAt 13:ℚ)
def qv249 : ℚ := ((((raw_ints% [-5670941492926463])).headD 0 * (2:ℤ)^20):ℚ)/(denomAt 15:ℚ)
def qv250 : ℚ := ((((raw_ints% [-204967668632342629])).headD 0 * (2:ℤ)^14):ℚ)/(denomAt 15:ℚ)
def qv251 : ℚ := ((((raw_ints% [919439019619375759])).headD 0 * (2:ℤ)^15):ℚ)/(denomAt 15:ℚ)
def qv252 : ℚ := ((((raw_ints% [52548319172503657])).headD 0 * (2:ℤ)^18):ℚ)/(denomAt 15:ℚ)
def qv253 : ℚ := ((((raw_ints% [-829607230681816949])).headD 0 * (2:ℤ)^17):ℚ)/(denomAt 15:ℚ)
def qv254 : ℚ := ((((raw_ints% [-77052634884141107])).headD 0 * (2:ℤ)^19):ℚ)/(denomAt 15:ℚ)
def qv255 : ℚ := ((((raw_ints% [54373876590331901])).headD 0 * (2:ℤ)^20):ℚ)/(denomAt 13:ℚ)
def qv256 : ℚ := ((((raw_ints% [40889824910982947])).headD 0 * (2:ℤ)^21):ℚ)/(denomAt 15:ℚ)
def qv257 : ℚ := ((((raw_ints% [-130603937551609033])).headD 0 * (2:ℤ)^22):ℚ)/(denomAt 15:ℚ)
def qv258 : ℚ := ((((raw_ints% [-2097262649607187])).headD 0 * (2:ℤ)^22):ℚ)/(denomAt 11:ℚ)
def qv259 : ℚ := ((((raw_ints% [22972263315913571])).headD 0 * (2:ℤ)^25):ℚ)/(denomAt 15:ℚ)
def qv260 : ℚ := ((((raw_ints% [192929292911587])).headD 0 * (2:ℤ)^24):ℚ)/(denomAt 9:ℚ)
def qv261 : ℚ := ((((raw_ints% [-23385746538472837])).headD 0 * (2:ℤ)^25):ℚ)/(denomAt 15:ℚ)
def qv262 : ℚ := ((((raw_ints% [-1674432171814139])).headD 0 * (2:ℤ)^26):ℚ)/(denomAt 15:ℚ)
def qv263 : ℚ := ((((raw_ints% [4188770310912307])).headD 0 * (2:ℤ)^27):ℚ)/(denomAt 15:ℚ)
def qv264 : ℚ := ((((raw_ints% [214185019732769])).headD 0 * (2:ℤ)^28):ℚ)/(denomAt 15:ℚ)
def qv265 : ℚ := ((((raw_ints% [-250298733405761])).headD 0 * (2:ℤ)^30):ℚ)/(denomAt 15:ℚ)
def qv266 : ℚ := ((((raw_ints% [-8159844299699])).headD 0 * (2:ℤ)^31):ℚ)/(denomAt 15:ℚ)
def qv267 : ℚ := ((((raw_ints% [11940179982361])).headD 0 * (2:ℤ)^31):ℚ)/(denomAt 14:ℚ)
def qv268 : ℚ := ((((raw_ints% [140114217653])).headD 0 * (2:ℤ)^34):ℚ)/(denomAt 15:ℚ)
def qv269 : ℚ := ((((raw_ints% [-12088134583])).headD 0 * (2:ℤ)^38):ℚ)/(denomAt 14:ℚ)

def first : QSegment := ⟨(qv0,qv1),(qv0,qv1),[qv2,qv3,qv4,qv5,qv6,qv7,qv8,qv9,qv10,qv11,qv12,qv13,qv14,qv15,qv16,qv17,qv18,qv19,qv20,qv21,qv22,qv23,qv24,qv25,qv26,qv27,qv28,qv29,qv30,qv31,qv32,qv33,qv34]⟩
def second : QSegment := ⟨(qv35,qv1),(qv36,qv1),[qv1,qv1]⟩
def Y : ℚ := qv37
def sourceRadius : ℚ := qv37
def phi : ℚ := qv38
def center : ℚ := qv39
def sourceZ : ℚ := qv40
def theta : ℚ := qv41
def firstTree : BernsteinTree := (.split qv1 (.split qv42 (.leaf 32 [qv43,qv44,qv45,qv46,qv47,qv48,qv49,qv50,qv51,qv52,qv53,qv54,qv55,qv56,qv57,qv58,qv59,qv60,qv61,qv62,qv63,qv64,qv65,qv66,qv67,qv68,qv69,qv70,qv71,qv72,qv73,qv74,qv75]) (.leaf 32 [qv75,qv76,qv77,qv78,qv79,qv80,qv81,qv82,qv83,qv84,qv85,qv86,qv87,qv88,qv89,qv90,qv91,qv92,qv93,qv94,qv95,qv96,qv97,qv98,qv99,qv100,qv101,qv102,qv103,qv104,qv105,qv106,qv107])) (.split qv40 (.leaf 32 [qv107,qv108,qv109,qv110,qv111,qv112,qv113,qv114,qv115,qv116,qv117,qv118,qv119,qv120,qv121,qv122,qv123,qv124,qv125,qv126,qv127,qv128,qv129,qv130,qv131,qv132,qv133,qv134,qv135,qv136,qv137,qv138,qv139]) (.split qv140 (.leaf 32 [qv139,qv141,qv142,qv143,qv144,qv145,qv146,qv147,qv148,qv149,qv150,qv151,qv152,qv153,qv154,qv155,qv156,qv157,qv158,qv159,qv160,qv161,qv162,qv163,qv164,qv165,qv166,qv167,qv168,qv169,qv170,qv171,qv172]) (.split qv173 (.leaf 32 [qv172,qv174,qv175,qv176,qv177,qv178,qv179,qv180,qv181,qv182,qv183,qv184,qv185,qv186,qv187,qv188,qv189,qv190,qv191,qv192,qv193,qv194,qv195,qv196,qv197,qv198,qv199,qv200,qv201,qv202,qv203,qv204,qv205]) (.leaf 32 [qv205,qv206,qv207,qv208,qv209,qv210,qv211,qv212,qv213,qv214,qv215,qv216,qv217,qv218,qv219,qv220,qv221,qv222,qv223,qv224,qv225,qv226,qv227,qv228,qv229,qv230,qv231,qv232,qv233,qv234,qv235,qv236,qv237])))))
def secondTree : BernsteinTree := (.leaf 1 [qv1,qv1])
def firstMonomial : List ℚ := [qv107,qv238,qv239,qv240,qv241,qv242,qv243,qv244,qv245,qv246,qv247,qv248,qv249,qv250,qv251,qv252,qv253,qv254,qv255,qv256,qv257,qv258,qv259,qv260,qv261,qv262,qv263,qv264,qv265,qv266,qv267,qv268,qv269]
def secondMonomial : List ℚ := [qv1,qv1]
def density : DensityWitness := ⟨[firstTree,secondTree]⟩
theorem bernList_split_of {p : List ℚ} {a b : ℚ} (mid : ℚ) (L R : BernsteinTree)
    (hm : a<mid ∧ mid<b) (hL : bernListCheck p a mid L=true) (hR : bernListCheck p mid b R=true) :
    bernListCheck p a b (.split mid L R)=true := by
  simpa only [bernListCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using (show (a<mid ∧ mid<b) ∧ bernListCheck p a mid L=true ∧ bernListCheck p mid b R=true from ⟨hm,hL,hR⟩)
theorem firstMonomial_spec : qDensityCoeffs first=firstMonomial := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf0 : bernListCheck firstMonomial (-1) qv42 (.leaf 32 [qv43,qv44,qv45,qv46,qv47,qv48,qv49,qv50,qv51,qv52,qv53,qv54,qv55,qv56,qv57,qv58,qv59,qv60,qv61,qv62,qv63,qv64,qv65,qv66,qv67,qv68,qv69,qv70,qv71,qv72,qv73,qv74,qv75])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf1 : bernListCheck firstMonomial qv42 qv1 (.leaf 32 [qv75,qv76,qv77,qv78,qv79,qv80,qv81,qv82,qv83,qv84,qv85,qv86,qv87,qv88,qv89,qv90,qv91,qv92,qv93,qv94,qv95,qv96,qv97,qv98,qv99,qv100,qv101,qv102,qv103,qv104,qv105,qv106,qv107])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf2 : bernListCheck firstMonomial qv1 qv40 (.leaf 32 [qv107,qv108,qv109,qv110,qv111,qv112,qv113,qv114,qv115,qv116,qv117,qv118,qv119,qv120,qv121,qv122,qv123,qv124,qv125,qv126,qv127,qv128,qv129,qv130,qv131,qv132,qv133,qv134,qv135,qv136,qv137,qv138,qv139])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf3 : bernListCheck firstMonomial qv40 qv140 (.leaf 32 [qv139,qv141,qv142,qv143,qv144,qv145,qv146,qv147,qv148,qv149,qv150,qv151,qv152,qv153,qv154,qv155,qv156,qv157,qv158,qv159,qv160,qv161,qv162,qv163,qv164,qv165,qv166,qv167,qv168,qv169,qv170,qv171,qv172])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf4 : bernListCheck firstMonomial qv140 qv173 (.leaf 32 [qv172,qv174,qv175,qv176,qv177,qv178,qv179,qv180,qv181,qv182,qv183,qv184,qv185,qv186,qv187,qv188,qv189,qv190,qv191,qv192,qv193,qv194,qv195,qv196,qv197,qv198,qv199,qv200,qv201,qv202,qv203,qv204,qv205])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf5 : bernListCheck firstMonomial qv173 1 (.leaf 32 [qv205,qv206,qv207,qv208,qv209,qv210,qv211,qv212,qv213,qv214,qv215,qv216,qv217,qv218,qv219,qv220,qv221,qv222,qv223,qv224,qv225,qv226,qv227,qv228,qv229,qv230,qv231,qv232,qv233,qv234,qv235,qv236,qv237])=true := by decide +kernel
def firstGeometry : Bool := decide (cqSq first.half≠0 ∧ 0<first.coeff.length ∧
  cqSq (cqAdd first.mid first.half)≤sourceRadius^2 ∧ cqSq (cqSub first.mid first.half)≤sourceRadius^2)
set_option trace.profiler true in
theorem firstGeometry_ok : firstGeometry=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_fast : bernListCheck (qDensityCoeffs first) (-1) 1 firstTree=true := by
  rw [firstMonomial_spec]
  exact (bernList_split_of _ _ _ (by decide +kernel) (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf0 firstDensity_leaf1) (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf2 (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf3 (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf4 firstDensity_leaf5))))
theorem firstDensity_ok : bernCheck first.density (-1) 1 firstTree=true := by
  rw [← qDensityCoeffs_spec first,← bernListCheck_eq]
  exact firstDensity_fast
#print axioms firstDensity_ok
theorem secondMonomial_spec : qDensityCoeffs second=secondMonomial := by decide +kernel
set_option trace.profiler true in
theorem secondDensity_leaf0 : bernListCheck secondMonomial (-1) 1 (.leaf 1 [qv1,qv1])=true := by decide +kernel
def secondGeometry : Bool := decide (cqSq second.half≠0 ∧ 0<second.coeff.length ∧
  cqSq (cqAdd second.mid second.half)≤sourceRadius^2 ∧ cqSq (cqSub second.mid second.half)≤sourceRadius^2)
set_option trace.profiler true in
theorem secondGeometry_ok : secondGeometry=true := by decide +kernel
set_option trace.profiler true in
theorem secondDensity_fast : bernListCheck (qDensityCoeffs second) (-1) 1 secondTree=true := by
  rw [secondMonomial_spec]
  exact secondDensity_leaf0
theorem secondDensity_ok : bernCheck second.density (-1) 1 secondTree=true := by
  rw [← qDensityCoeffs_spec second,← bernListCheck_eq]
  exact secondDensity_fast
#print axioms secondDensity_ok
theorem source_ok : sourceDataCheck [first,second] sourceRadius density=true := by
  simp only [sourceDataCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true]
  constructor
  · decide +kernel
  · intro j hj
    have hj' : j<2 := by simpa only [List.length_cons,List.length_nil] using List.mem_range.mp hj
    interval_cases j
    · change (firstGeometry && bernCheck first.density (-1) 1 firstTree)=true
      simp only [Bool.and_eq_true]
      exact ⟨firstGeometry_ok,firstDensity_ok⟩
    · change (secondGeometry && bernCheck second.density (-1) 1 secondTree)=true
      simp only [Bool.and_eq_true]
      exact ⟨secondGeometry_ok,secondDensity_ok⟩
noncomputable def input : LatticeInput :=
  ⟨datumOfSourceChecks [first,second] sourceRadius density source_ok,first,second,rfl,Y⟩
theorem datum_checked : datumCheck input.data density=true := source_ok
theorem shape_checked : latticeShapeCheck input=true := by decide +kernel
theorem first_positive : ∀x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
    (fun j : ℕ => (first.c j:ℝ)) (first.coeff.length-1) x :=
  (datum_source_data input.data density datum_checked first (lattice_first_mem input)).2.2
theorem second_positive : ∀x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
    (fun j : ℕ => (second.c j:ℝ)) (second.coeff.length-1) x :=
  (datum_source_data input.data density datum_checked second (lattice_second_mem input)).2.2
#print axioms source_ok
#print axioms datum_checked
#print axioms shape_checked
#print axioms first_positive
#print axioms second_positive
end CatalanCore.Li2.DecayCert.Simple.Data.L1_2_r16_0.In
