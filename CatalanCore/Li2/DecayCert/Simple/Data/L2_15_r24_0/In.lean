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
namespace CatalanCore.Li2.DecayCert.Simple.Data.L2_15_r24_0.In
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.LatticeGate
def decodePairs : List ℤ → List ℤ
  | a::e::rest => a*2^e.toNat :: decodePairs rest
  | _ => []
def denominators : Array ℤ := (decodePairs (raw_ints% [1,96,1,0,1,1,1,2,1,3,15,0,1,4,17,1,255,4,625,3,15625,6,284542392131875,0,7113559803296875,0,284542392131875,5,7113559803296875,1,284542392131875,6,1422711960659375,4,23437277597294375,0,7113559803296875,2,7113559803296875,3,7113559803296875,4,7113559803296875,5,4268135881978125,6,35567799016484375,3,351559163959415625,0,7113559803296875,6,35567799016484375,4,585931939932359375,0,35567799016484375,5,21340679409890625,6,1757795819797078125,0,35567799016484375,6,2929659699661796875,0,106703397049453125,6,8788979098985390625,0,2929659699661796875,2,2929659699661796875,3,1757795819797078125,4,8788979098985390625,2,2929659699661796875,4,1757795819797078125,5,8788979098985390625,3,2929659699661796875,5,1757795819797078125,6,8788979098985390625,4,2929659699661796875,6,8788979098985390625,5,148240780802886921875,2,5273387459391234375,7,8788979098985390625,7,5273387459391234375,8,26366937296956171875,6,26366937296956171875,7,13476434618444265625,8,26366937296956171875,10,741203904014434609375,6,373566767623275043125,7,202146519276663984375,8,2223611712043303828125,5,606439557829991953125,7,606439557829991953125,8,202146519276663984375,10,2030254171865625234375,7,2223611712043303828125,7,416363236515934571875,10,6670835136129911484375,6,1415025634936647890625,9,46695845952909380390625,4,741203904014434609375,10,6670835136129911484375,7,121287911565998390625,13,19716023846783960609375,6,79222568547986459903125,4,51712313975279073826875,6,59148071540351881828125,6,2223611712043303828125,11,9339169190581876078125,9,46695845952909380390625,7,6094043734460496915625,10,98580119233919803046875,6,15565281984303126796875,9,42248622528822772734375,8,86187189958798456378125,7,47881772199332475765625,8,25349173517293663640625,9,13058665145272493390625,10,59148071540351881828125,8,239408860996662378828125,6,34567054796309541328125,9,1292807849381976845671875,4,340212591942625485703125,6,21764441908787488984375,10,380237602759404954609375,6,2154679748969961409453125,4,143645316597997427296875,8,72166307381769042421875,10,295740357701759409140625,8,80656461191388929765625,10,718226582989987136484375,7,46695845952909380390625,11,6464039246909884228359375,4,2154679748969961409453125,6,718226582989987136484375,8,6464039246909884228359375,5,239408860996662378828125,10,15565281984303126796875,14,5941692641098984492734375,6,2154679748969961409453125,8,718226582989987136484375,10,5941692641098984492734375,7,1371159840253611806015625,10,8788979098985390625,29,295740357701759409140625,14,430935949793992281890625,14,380237602759404954609375,15,2929659699661796875,32,143645316597997427296875,17,5188427328101042265625,22,46695845952909380390625,19,2929659699661796875,33,18282131203381490746875,21,606439557829991953125,26,195879977179087400859375,18,5377097412759261984375,24,741203904014434609375,29,121287911565998390625,33,4245076904809943671875,28,1980564213699661497578125,20,76047520551880990921875,25,46695845952909380390625,27,1371159840253611806015625,23,126745867586468318203125,27,2154679748969961409453125,23,295740357701759409140625,26,718226582989987136484375,25,741203904014434609375,35,6464039246909884228359375,22,46695845952909380390625,34,9339169190581876078125,37,6464039246909884228359375,29,2929659699661796875,52,295740357701759409140625,37,76047520551880990921875,39,718226582989987136484375,37,5273387459391234375,55,6464039246909884228359375,35,143645316597997427296875,41,152351093361512422890625,41,1075419482551852396875,49,2154679748969961409453125,39,1334167027225982296875,50,202146519276663984375,53,26366937296956171875,56,2154679748969961409453125,41,67382173092221328125,56,1980564213699661497578125,42,1371159840253611806015625,43,5941692641098984492734375,41,430935949793992281890625,45,457053280084537268671875,45,2223611712043303828125,53,143645316597997427296875,47,15565281984303126796875,51,2154679748969961409453125,45,444722342408660765625,58,1371159840253611806015625,47,380237602759404954609375,49,239408860996662378828125,50,9576354439866495153125,55,6670835136129911484375,57,1037685465620208453125,60,380237602759404954609375,54,1757795819797078125,72,4286092140605208828125,62,59148071540351881828125,60,380237602759404954609375,58,9339169190581876078125,66,42248622528822772734375,64,46695845952909380390625,64,2929659699661796875,78,2154679748969961409453125,59,380237602759404954609375,62,121287911565998390625,74,126745867586468318203125,64,8788979098985390625,78,741203904014434609375,72,20012505408389734453125,68,148240780802886921875,76,457053280084537268671875,66,606439557829991953125,76,1980564213699661497578125,65,430935949793992281890625,68,1371159840253611806015625,68,46695845952909380390625,73,718226582989987136484375,70,46695845952909380390625,74,295740357701759409140625,72,380237602759404954609375,72])).toArray
def denomAt (i : ℕ) : ℤ := denominators[i]?.getD 0
def parentScale : ℤ := denomAt 0
def sharedTableCheck : Bool := decide (denominators.size=198 ∧ parentScale=2^96) && denominators.toList.all (fun n => decide (0<n))
def qv0 : ℚ := ((((raw_ints% [9])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 3:ℚ)
def qv1 : ℚ := ((((raw_ints% [0])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 1:ℚ)
def qv2 : ℚ := ((((raw_ints% [1998383])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 10:ℚ)
def qv3 : ℚ := ((((raw_ints% [-532342524019932952699])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv4 : ℚ := ((((raw_ints% [-17073727754835513887])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 38:ℚ)
def qv5 : ℚ := ((((raw_ints% [27417107631282172799])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 40:ℚ)
def qv6 : ℚ := ((((raw_ints% [-19986073860053211103])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 40:ℚ)
def qv7 : ℚ := ((((raw_ints% [105529495959083181469])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv8 : ℚ := ((((raw_ints% [-79335407381601513019])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv9 : ℚ := ((((raw_ints% [7017516991290703709])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 36:ℚ)
def qv10 : ℚ := ((((raw_ints% [-34248108274741311611])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv11 : ℚ := ((((raw_ints% [21335558951178308727])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv12 : ℚ := ((((raw_ints% [-13943817379501006531])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 41:ℚ)
def qv13 : ℚ := ((((raw_ints% [8799075195832866601])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 40:ℚ)
def qv14 : ℚ := ((((raw_ints% [-19446338820112298839])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv15 : ℚ := ((((raw_ints% [8791683709736894059])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv16 : ℚ := ((((raw_ints% [-3493752562478216543])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 39:ℚ)
def qv17 : ℚ := ((((raw_ints% [1649469838550431])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 27:ℚ)
def qv18 : ℚ := ((((raw_ints% [-2173569895573456519])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 42:ℚ)
def qv19 : ℚ := ((((raw_ints% [3220209687408779549])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv20 : ℚ := ((((raw_ints% [837337143634431133])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv21 : ℚ := ((((raw_ints% [-89451975420285573])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv22 : ℚ := ((((raw_ints% [395968309656710437])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 37:ℚ)
def qv23 : ℚ := ((((raw_ints% [-1906764658160204051])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 44:ℚ)
def qv24 : ℚ := ((((raw_ints% [2911258903849252013])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv25 : ℚ := ((((raw_ints% [-2610497898612188191])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 46:ℚ)
def qv26 : ℚ := ((((raw_ints% [57286428599628491])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv27 : ℚ := ((((raw_ints% [-5])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv28 : ℚ := ((((raw_ints% [3])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv29 : ℚ := ((((raw_ints% [1617])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 10:ℚ)
def qv30 : ℚ := ((((raw_ints% [4385787520191])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 16:ℚ)
def qv31 : ℚ := ((((raw_ints% [4850950453503])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv32 : ℚ := ((((raw_ints% [2111161517619])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv33 : ℚ := ((((raw_ints% [825734938413])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv34 : ℚ := ((((raw_ints% [128364058977])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 20:ℚ)
def qv35 : ℚ := ((((raw_ints% [1214549593257])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv36 : ℚ := ((((raw_ints% [35201082609])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 19:ℚ)
def qv37 : ℚ := ((((raw_ints% [1193806487643])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv38 : ℚ := ((((raw_ints% [127861734693])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv39 : ℚ := ((((raw_ints% [46829198031])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 13:ℚ)
def qv40 : ℚ := ((((raw_ints% [9])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv41 : ℚ := ((((raw_ints% [135])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 7:ℚ)
def qv42 : ℚ := ((((raw_ints% [-10201])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 8:ℚ)
def qv43 : ℚ := ((((raw_ints% [1])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 5:ℚ)
def qv44 : ℚ := ((((raw_ints% [-35159])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 9:ℚ)
def qv45 : ℚ := ((((raw_ints% [-1])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv46 : ℚ := ((((raw_ints% [86186871406249792461])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 45:ℚ)
def qv47 : ℚ := ((((raw_ints% [2529681874986109219903])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 48:ℚ)
def qv48 : ℚ := ((((raw_ints% [451539151106983319181181])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 59:ℚ)
def qv49 : ℚ := ((((raw_ints% [224277384835282726686319])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 55:ℚ)
def qv50 : ℚ := ((((raw_ints% [181529602777936146634861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 56:ℚ)
def qv51 : ℚ := ((((raw_ints% [22212729675241924142828939])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 77:ℚ)
def qv52 : ℚ := ((((raw_ints% [5042365947769682004841667])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 71:ℚ)
def qv53 : ℚ := ((((raw_ints% [102342578867977202463288839])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 92:ℚ)
def qv54 : ℚ := ((((raw_ints% [875944169819909967179216321])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 103:ℚ)
def qv55 : ℚ := ((((raw_ints% [1770581896925566047687211])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 64:ℚ)
def qv56 : ℚ := ((((raw_ints% [44712876455348066585522599])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 82:ℚ)
def qv57 : ℚ := ((((raw_ints% [5595258516287310592125946333])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 110:ℚ)
def qv58 : ℚ := ((((raw_ints% [1503542287550687734278122917])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 106:ℚ)
def qv59 : ℚ := ((((raw_ints% [87865812279806663785126773])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 91:ℚ)
def qv60 : ℚ := ((((raw_ints% [2168749183783164295287885443])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 107:ℚ)
def qv61 : ℚ := ((((raw_ints% [47931667074608989461617809])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 83:ℚ)
def qv62 : ℚ := ((((raw_ints% [84387964392032189320799293])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 90:ℚ)
def qv63 : ℚ := ((((raw_ints% [49722292956984948478461407])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 84:ℚ)
def qv64 : ℚ := ((((raw_ints% [286284754263718807248766553])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 96:ℚ)
def qv65 : ℚ := ((((raw_ints% [17839675484259672606819023])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 76:ℚ)
def qv66 : ℚ := ((((raw_ints% [1571936941879481803767367])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 65:ℚ)
def qv67 : ℚ := ((((raw_ints% [1034642944231650839362303])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 63:ℚ)
def qv68 : ℚ := ((((raw_ints% [12385148526219940299639])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 53:ℚ)
def qv69 : ℚ := ((((raw_ints% [5982544652866897775473])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 51:ℚ)
def qv70 : ℚ := ((((raw_ints% [41016446232459874109])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 35:ℚ)
def qv71 : ℚ := ((((raw_ints% [5830191862081545967919])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 51:ℚ)
def qv72 : ℚ := ((((raw_ints% [529298770175392580893819])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 60:ℚ)
def qv73 : ℚ := ((((raw_ints% [159499127932750315046131])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 55:ℚ)
def qv74 : ℚ := ((((raw_ints% [1414409930618140167743561])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 65:ℚ)
def qv75 : ℚ := ((((raw_ints% [25987521368125243202694167])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 80:ℚ)
def qv76 : ℚ := ((((raw_ints% [34683780189532401422743697])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 81:ℚ)
def qv77 : ℚ := ((((raw_ints% [40911426904321272688131649])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 84:ℚ)
def qv78 : ℚ := ((((raw_ints% [10255674672083464366755557])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 73:ℚ)
def qv79 : ℚ := ((((raw_ints% [112079979767673325427421229])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 94:ℚ)
def qv80 : ℚ := ((((raw_ints% [1654574436492835192559214607])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 107:ℚ)
def qv81 : ℚ := ((((raw_ints% [39486840458162565640635941])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 85:ℚ)
def qv82 : ℚ := ((((raw_ints% [2210249066148407176164642191])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 109:ℚ)
def qv83 : ℚ := ((((raw_ints% [211181462319905238649302233])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 95:ℚ)
def qv84 : ℚ := ((((raw_ints% [516069965928694877914786109])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 102:ℚ)
def qv85 : ℚ := ((((raw_ints% [675010417057236791366898471])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 104:ℚ)
def qv86 : ℚ := ((((raw_ints% [279091642895529387689345047])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 100:ℚ)
def qv87 : ℚ := ((((raw_ints% [64323898443115266238793227])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 92:ℚ)
def qv88 : ℚ := ((((raw_ints% [16332272788113783073411731])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 79:ℚ)
def qv89 : ℚ := ((((raw_ints% [15154236079399467254158769])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 77:ℚ)
def qv90 : ℚ := ((((raw_ints% [2120580141503294804746823])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 69:ℚ)
def qv91 : ℚ := ((((raw_ints% [1442483426561711118111])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 47:ℚ)
def qv92 : ℚ := ((((raw_ints% [184929343485236188538353])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 59:ℚ)
def qv93 : ℚ := ((((raw_ints% [2623526568687946711669])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 49:ℚ)
def qv94 : ℚ := ((((raw_ints% [256644620291548990939])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 43:ℚ)
def qv95 : ℚ := ((((raw_ints% [1])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 2:ℚ)
def qv96 : ℚ := ((((raw_ints% [2509365837143033107111])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 49:ℚ)
def qv97 : ℚ := ((((raw_ints% [169175162532038111109349])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 59:ℚ)
def qv98 : ℚ := ((((raw_ints% [100918994014986695188127])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 55:ℚ)
def qv99 : ℚ := ((((raw_ints% [1771227135527596224848783])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 69:ℚ)
def qv100 : ℚ := ((((raw_ints% [524999868911270859090287])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 62:ℚ)
def qv101 : ℚ := ((((raw_ints% [7440007249710327797245813])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 74:ℚ)
def qv102 : ℚ := ((((raw_ints% [46496436360567184882925957])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 92:ℚ)
def qv103 : ℚ := ((((raw_ints% [38409818740948078568713087])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 89:ℚ)
def qv104 : ℚ := ((((raw_ints% [1327417498083082480742923787])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 108:ℚ)
def qv105 : ℚ := ((((raw_ints% [241993651447751042194926311])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 101:ℚ)
def qv106 : ℚ := ((((raw_ints% [140937056652772881416724841])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 97:ℚ)
def qv107 : ℚ := ((((raw_ints% [2102214771374215745345769])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 72:ℚ)
def qv108 : ℚ := ((((raw_ints% [10044413250520776098400459])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 78:ℚ)
def qv109 : ℚ := ((((raw_ints% [53734367129464014190250039])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 93:ℚ)
def qv110 : ℚ := ((((raw_ints% [138378300012684766591455203])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 98:ℚ)
def qv111 : ℚ := ((((raw_ints% [22214280585383625713288411])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 87:ℚ)
def qv112 : ℚ := ((((raw_ints% [24666837537390352851921859])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 88:ℚ)
def qv113 : ℚ := ((((raw_ints% [20266332531527263007401297])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 86:ℚ)
def qv114 : ℚ := ((((raw_ints% [930905277050223901086659])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 66:ℚ)
def qv115 : ℚ := ((((raw_ints% [921536018336256631767749])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 67:ℚ)
def qv116 : ℚ := ((((raw_ints% [84212154976209140531807])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 58:ℚ)
def qv117 : ℚ := ((((raw_ints% [58691920492127744539753])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 57:ℚ)
def qv118 : ℚ := ((((raw_ints% [3659972725458907281169])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 52:ℚ)
def qv119 : ℚ := ((((raw_ints% [48455324798895836729])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 39:ℚ)
def qv120 : ℚ := ((((raw_ints% [3])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 3:ℚ)
def qv121 : ℚ := ((((raw_ints% [1361275486220518690459])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 50:ℚ)
def qv122 : ℚ := ((((raw_ints% [203426536951737308411549])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 61:ℚ)
def qv123 : ℚ := ((((raw_ints% [4357206634831467940135817])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 75:ℚ)
def qv124 : ℚ := ((((raw_ints% [88981746223298984809935793])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 99:ℚ)
def qv125 : ℚ := ((((raw_ints% [230456882268565812588232663])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 105:ℚ)
def qv126 : ℚ := ((((raw_ints% [4246926258877288235707383791])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 112:ℚ)
def qv127 : ℚ := ((((raw_ints% [10577333932213910320901689811])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 114:ℚ)
def qv128 : ℚ := ((((raw_ints% [5797413751797387323169519199])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 113:ℚ)
def qv129 : ℚ := ((((raw_ints% [14933801432297573191567464259])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 116:ℚ)
def qv130 : ℚ := ((((raw_ints% [39297181801784055680222423281])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 122:ℚ)
def qv131 : ℚ := ((((raw_ints% [28282849890195909233080583531])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 120:ℚ)
def qv132 : ℚ := ((((raw_ints% [1475533149050998405395159076479])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 127:ℚ)
def qv133 : ℚ := ((((raw_ints% [7866286399870511590951386466771])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 130:ℚ)
def qv134 : ℚ := ((((raw_ints% [11892862572063410325665994012463])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 132:ℚ)
def qv135 : ℚ := ((((raw_ints% [15248983704587404627422113074801])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 134:ℚ)
def qv136 : ℚ := ((((raw_ints% [16486789573111792827357664270259])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 136:ℚ)
def qv137 : ℚ := ((((raw_ints% [1489783176046241672553952181519])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 128:ℚ)
def qv138 : ℚ := ((((raw_ints% [11107563913244321102448125872781])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 133:ℚ)
def qv139 : ℚ := ((((raw_ints% [609924375093395136722333213347])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 126:ℚ)
def qv140 : ℚ := ((((raw_ints% [3197564645744780610160150981751])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 129:ℚ)
def qv141 : ℚ := ((((raw_ints% [192660909473490081603579203933])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 124:ℚ)
def qv142 : ℚ := ((((raw_ints% [18593561103171578773807563929])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 121:ℚ)
def qv143 : ℚ := ((((raw_ints% [5387730073468966082254047617])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 115:ℚ)
def qv144 : ℚ := ((((raw_ints% [1878357631668208324557664861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 111:ℚ)
def qv145 : ℚ := ((((raw_ints% [7])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 4:ℚ)
def qv146 : ℚ := ((((raw_ints% [9639130979876700514207271271])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 119:ℚ)
def qv147 : ℚ := ((((raw_ints% [383010787348218412376663598059])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 125:ℚ)
def qv148 : ℚ := ((((raw_ints% [8961158227446446336196915210801])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 135:ℚ)
def qv149 : ℚ := ((((raw_ints% [269357538528866987960992402308889])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 137:ℚ)
def qv150 : ℚ := ((((raw_ints% [409882269543415292993878597420229])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 138:ℚ)
def qv151 : ℚ := ((((raw_ints% [12299678364685885981308836985692521])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 141:ℚ)
def qv152 : ℚ := ((((raw_ints% [11941024654118525861729131302456809])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 142:ℚ)
def qv153 : ℚ := ((((raw_ints% [59619115150432317090412572906443569])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 145:ℚ)
def qv154 : ℚ := ((((raw_ints% [79317858019304761841255986243471391])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 146:ℚ)
def qv155 : ℚ := ((((raw_ints% [1107349127373873742297369633188243331])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 153:ℚ)
def qv156 : ℚ := ((((raw_ints% [2609135284732953600312074072932198063])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 156:ℚ)
def qv157 : ℚ := ((((raw_ints% [1733985875450085497498594880649311499])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 155:ℚ)
def qv158 : ℚ := ((((raw_ints% [2926948429537671684027570975649708163])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 159:ℚ)
def qv159 : ℚ := ((((raw_ints% [2505882256695474159045897863575823861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 158:ℚ)
def qv160 : ℚ := ((((raw_ints% [3011279320036452558076750615540746313])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 161:ℚ)
def qv161 : ℚ := ((((raw_ints% [10095208962168157501127678484403793767])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 163:ℚ)
def qv162 : ℚ := ((((raw_ints% [25259366172935648359834596672593159867])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 166:ℚ)
def qv163 : ℚ := ((((raw_ints% [62705884526460409797922357532971361])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 148:ℚ)
def qv164 : ℚ := ((((raw_ints% [3153445458604543232511762612139666613])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 162:ℚ)
def qv165 : ℚ := ((((raw_ints% [116065462710833604918450116736341863])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 150:ℚ)
def qv166 : ℚ := ((((raw_ints% [1312577046175313434870450873219314821])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 160:ℚ)
def qv167 : ℚ := ((((raw_ints% [99835496930888655341685385136793703])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 151:ℚ)
def qv168 : ℚ := ((((raw_ints% [8586710051106786225570950706572981])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 144:ℚ)
def qv169 : ℚ := ((((raw_ints% [483545418176809185328046370957919])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 140:ℚ)
def qv170 : ℚ := ((((raw_ints% [15])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 6:ℚ)
def qv171 : ℚ := ((((raw_ints% [61512260070656852903003262594045599])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 152:ℚ)
def qv172 : ℚ := ((((raw_ints% [137775385578563637032526208159055129])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 154:ℚ)
def qv173 : ℚ := ((((raw_ints% [3159844941131739535424313893456946191])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 164:ℚ)
def qv174 : ℚ := ((((raw_ints% [20384951165965672254607085205055966861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 169:ℚ)
def qv175 : ℚ := ((((raw_ints% [21576978785136067630969125875189634493])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 170:ℚ)
def qv176 : ℚ := ((((raw_ints% [1032761783929108084071430086526103561683])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 174:ℚ)
def qv177 : ℚ := ((((raw_ints% [21972704955097469704212329054719333812373])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 181:ℚ)
def qv178 : ℚ := ((((raw_ints% [12657161174775684756588888756499595852483])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 180:ℚ)
def qv179 : ℚ := ((((raw_ints% [6328265198750452697253463840825075213163])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 177:ℚ)
def qv180 : ℚ := ((((raw_ints% [14763561452749652928593496017574363164293])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 183:ℚ)
def qv181 : ℚ := ((((raw_ints% [160779802330564225891540541650512506976557])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 188:ℚ)
def qv182 : ℚ := ((((raw_ints% [253629200500363231384095384806869324137977])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 190:ℚ)
def qv183 : ℚ := ((((raw_ints% [977826762353595030403313850282146209776617])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 192:ℚ)
def qv184 : ℚ := ((((raw_ints% [202539887952602277577363962640883931390451])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 191:ℚ)
def qv185 : ℚ := ((((raw_ints% [837571790065418478624488614082929393491509])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 194:ℚ)
def qv186 : ℚ := ((((raw_ints% [3478560206433601384326292389252206896219])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 186:ℚ)
def qv187 : ℚ := ((((raw_ints% [684134664734917609177617082239064388967611])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 197:ℚ)
def qv188 : ℚ := ((((raw_ints% [485553199979136561654432197584598019629861])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 196:ℚ)
def qv189 : ℚ := ((((raw_ints% [415504792799967608339190077981243641970999])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 195:ℚ)
def qv190 : ℚ := ((((raw_ints% [322749002830937582419446038454849698154911])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 193:ℚ)
def qv191 : ℚ := ((((raw_ints% [12422370725022801782701071020452091181643])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 187:ℚ)
def qv192 : ℚ := ((((raw_ints% [72425411463007163631869178864356780577971])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 189:ℚ)
def qv193 : ℚ := ((((raw_ints% [5639234960385398857925945861250232036219])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 184:ℚ)
def qv194 : ℚ := ((((raw_ints% [22509298866799027504318106937633130759])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 172:ℚ)
def qv195 : ℚ := ((((raw_ints% [2922238771455326248279214192944990549847])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 179:ℚ)
def qv196 : ℚ := ((((raw_ints% [9016175908766858486516135781051514861879])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 182:ℚ)
def qv197 : ℚ := ((((raw_ints% [16073954768549924447791684090868712958287])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 185:ℚ)
def qv198 : ℚ := ((((raw_ints% [3614721419631723419594648389686791057231])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 176:ℚ)
def qv199 : ℚ := ((((raw_ints% [5055355012835877890918052740099002274719])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 178:ℚ)
def qv200 : ℚ := ((((raw_ints% [127206992164573327555859111918299626027])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 173:ℚ)
def qv201 : ℚ := ((((raw_ints% [758296849534107310036206326137043088907])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 175:ℚ)
def qv202 : ℚ := ((((raw_ints% [49954565329909528881457499372618480837])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 171:ℚ)
def qv203 : ℚ := ((((raw_ints% [2598861876435698144226658671037494779])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 168:ℚ)
def qv204 : ℚ := ((((raw_ints% [2052609659339513421744540397915966749])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 167:ℚ)
def qv205 : ℚ := ((((raw_ints% [1451454462655047563301618129487664311])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 165:ℚ)
def qv206 : ℚ := ((((raw_ints% [94575193078130285442695251054154777])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 157:ℚ)
def qv207 : ℚ := ((((raw_ints% [2264325012304854902617625260641817])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 147:ℚ)
def qv208 : ℚ := ((((raw_ints% [7208998763652535136617469425568927])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 149:ℚ)
def qv209 : ℚ := ((((raw_ints% [516853463960715800750451514689121])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 143:ℚ)
def qv210 : ℚ := ((((raw_ints% [14721593094364188205518023956613])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 139:ℚ)
def qv211 : ℚ := ((((raw_ints% [53744515910985113809050635827])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 131:ℚ)
def qv212 : ℚ := ((((raw_ints% [186782550139130695784928077])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 123:ℚ)
def qv213 : ℚ := ((((raw_ints% [23803966833621906326365809])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 117:ℚ)
def qv214 : ℚ := ((((raw_ints% [9595609373398391339782369])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 118:ℚ)
def qv215 : ℚ := ((((raw_ints% [138543008949171816499])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 68:ℚ)
def qv216 : ℚ := ((((raw_ints% [746963303247062588149])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 70:ℚ)
def qv217 : ℚ := ((((raw_ints% [66693587464226112731])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 54:ℚ)
def qv218 : ℚ := ((((raw_ints% [1089646573471283421])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 45:ℚ)
def qv219 : ℚ := ((((raw_ints% [673044128749377])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv220 : ℚ := ((((raw_ints% [3149321870956569])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv221 : ℚ := ((((raw_ints% [3562349246819517])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv222 : ℚ := ((((raw_ints% [333347048462813])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 21:ℚ)
def qv223 : ℚ := ((((raw_ints% [3331889532641593])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv224 : ℚ := ((((raw_ints% [2055635377761581])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 29:ℚ)
def qv225 : ℚ := ((((raw_ints% [3483078713858513])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv226 : ℚ := ((((raw_ints% [876026661977159])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 26:ℚ)
def qv227 : ℚ := ((((raw_ints% [10563684175636823])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 33:ℚ)
def qv228 : ℚ := ((((raw_ints% [3549448187214237])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv229 : ℚ := ((((raw_ints% [717684268750449])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv230 : ℚ := ((((raw_ints% [3627394500290253])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv231 : ℚ := ((((raw_ints% [11031362054092919])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 33:ℚ)
def qv232 : ℚ := ((((raw_ints% [1868627103406063])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 28:ℚ)
def qv233 : ℚ := ((((raw_ints% [758419688972869])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv234 : ℚ := ((((raw_ints% [762466993177043])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 25:ℚ)
def qv235 : ℚ := ((((raw_ints% [3806489249495009])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv236 : ℚ := ((((raw_ints% [489593326029731])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 23:ℚ)
def qv237 : ℚ := ((((raw_ints% [510561771539743])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 22:ℚ)
def qv238 : ℚ := ((((raw_ints% [3906144999987153])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 31:ℚ)
def qv239 : ℚ := ((((raw_ints% [34360874094393])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 15:ℚ)
def qv240 : ℚ := ((((raw_ints% [-57080365772456802279])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 36:ℚ)
def qv241 : ℚ := ((((raw_ints% [-32534992531653924059])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 41:ℚ)
def qv242 : ℚ := ((((raw_ints% [-19173784759311642083])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 32:ℚ)
def qv243 : ℚ := ((((raw_ints% [827960067744827910809])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 38:ℚ)
def qv244 : ℚ := ((((raw_ints% [879338321928874025131])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 34:ℚ)
def qv245 : ℚ := ((((raw_ints% [-1078202538520975817561])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 34:ℚ)
def qv246 : ℚ := ((((raw_ints% [-1511636997223643994751])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 34:ℚ)
def qv247 : ℚ := ((((raw_ints% [96298076584632795339])).headD 0 * (2:ℤ)^5):ℚ)/(denomAt 27:ℚ)
def qv248 : ℚ := ((((raw_ints% [7620958019872145695137])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 32:ℚ)
def qv249 : ℚ := ((((raw_ints% [-18299828939783817432289])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 34:ℚ)
def qv250 : ℚ := ((((raw_ints% [-261412118340669467473])).headD 0 * (2:ℤ)^7):ℚ)/(denomAt 24:ℚ)
def qv251 : ℚ := ((((raw_ints% [383080471849118468833])).headD 0 * (2:ℤ)^10):ℚ)/(denomAt 32:ℚ)
def qv252 : ℚ := ((((raw_ints% [2376896176282730004697])).headD 0 * (2:ℤ)^10):ℚ)/(denomAt 34:ℚ)
def qv253 : ℚ := ((((raw_ints% [-1520542728371970820901])).headD 0 * (2:ℤ)^11):ℚ)/(denomAt 34:ℚ)
def qv254 : ℚ := ((((raw_ints% [-23963660463494512511])).headD 0 * (2:ℤ)^9):ℚ)/(denomAt 17:ℚ)
def qv255 : ℚ := ((((raw_ints% [1072713578103549642829])).headD 0 * (2:ℤ)^10):ℚ)/(denomAt 30:ℚ)
def qv256 : ℚ := ((((raw_ints% [68640400369377014699])).headD 0 * (2:ℤ)^14):ℚ)/(denomAt 30:ℚ)
def qv257 : ℚ := ((((raw_ints% [-1558874792054026906097])).headD 0 * (2:ℤ)^12):ℚ)/(denomAt 34:ℚ)
def qv258 : ℚ := ((((raw_ints% [-26123862422408078377])).headD 0 * (2:ℤ)^15):ℚ)/(denomAt 30:ℚ)
def qv259 : ℚ := ((((raw_ints% [71595076845609168413])).headD 0 * (2:ℤ)^16):ℚ)/(denomAt 34:ℚ)
def qv260 : ℚ := ((((raw_ints% [56227922351759920291])).headD 0 * (2:ℤ)^15):ℚ)/(denomAt 34:ℚ)
def qv261 : ℚ := ((((raw_ints% [-30085723969536758803])).headD 0 * (2:ℤ)^16):ℚ)/(denomAt 34:ℚ)
def qv262 : ℚ := ((((raw_ints% [-2610497898612188191])).headD 0 * (2:ℤ)^17):ℚ)/(denomAt 34:ℚ)
def qv263 : ℚ := ((((raw_ints% [57286428599628491])).headD 0 * (2:ℤ)^21):ℚ)/(denomAt 32:ℚ)
def qv264 : ℚ := ((((raw_ints% [4871644567251])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 18:ℚ)
def qv265 : ℚ := ((((raw_ints% [12097156353051])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 19:ℚ)
def qv266 : ℚ := ((((raw_ints% [-1037070486837])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 19:ℚ)
def qv267 : ℚ := ((((raw_ints% [-20148097734303])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 14:ℚ)
def qv268 : ℚ := ((((raw_ints% [2723364641613])).headD 0 * (2:ℤ)^0):ℚ)/(denomAt 14:ℚ)
def qv269 : ℚ := ((((raw_ints% [16319822984619])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 12:ℚ)
def qv270 : ℚ := ((((raw_ints% [-1009951281801])).headD 0 * (2:ℤ)^1):ℚ)/(denomAt 12:ℚ)
def qv271 : ℚ := ((((raw_ints% [-10513493020107])).headD 0 * (2:ℤ)^2):ℚ)/(denomAt 12:ℚ)
def qv272 : ℚ := ((((raw_ints% [127861734693])).headD 0 * (2:ℤ)^3):ℚ)/(denomAt 12:ℚ)
def qv273 : ℚ := ((((raw_ints% [46829198031])).headD 0 * (2:ℤ)^4):ℚ)/(denomAt 11:ℚ)

def first : QSegment := ⟨(qv0,qv1),(qv0,qv1),[qv2,qv3,qv4,qv5,qv6,qv7,qv8,qv9,qv10,qv11,qv12,qv13,qv14,qv15,qv16,qv17,qv18,qv19,qv20,qv21,qv22,qv23,qv24,qv25,qv26]⟩
def second : QSegment := ⟨(qv27,qv1),(qv28,qv1),[qv29,qv30,qv31,qv32,qv33,qv34,qv35,qv36,qv37,qv38,qv39]⟩
def Y : ℚ := qv40
def sourceRadius : ℚ := qv40
def phi : ℚ := qv41
def center : ℚ := qv42
def sourceZ : ℚ := qv43
def theta : ℚ := qv44
def firstTree : BernsteinTree := (.split qv1 (.split qv45 (.leaf 24 [qv46,qv47,qv48,qv49,qv50,qv51,qv52,qv53,qv54,qv55,qv56,qv57,qv58,qv59,qv60,qv61,qv62,qv63,qv64,qv65,qv66,qv67,qv68,qv69,qv70]) (.leaf 24 [qv70,qv71,qv72,qv73,qv74,qv75,qv76,qv77,qv78,qv79,qv80,qv81,qv82,qv83,qv84,qv85,qv86,qv87,qv88,qv89,qv90,qv91,qv92,qv93,qv94])) (.split qv95 (.leaf 24 [qv94,qv96,qv97,qv98,qv99,qv100,qv101,qv102,qv103,qv104,qv105,qv106,qv107,qv108,qv109,qv110,qv111,qv112,qv113,qv114,qv115,qv116,qv117,qv118,qv119]) (.split qv120 (.leaf 24 [qv119,qv121,qv122,qv123,qv124,qv125,qv126,qv127,qv128,qv129,qv130,qv131,qv132,qv133,qv134,qv135,qv136,qv137,qv138,qv139,qv140,qv141,qv142,qv143,qv144]) (.split qv145 (.leaf 24 [qv144,qv146,qv147,qv148,qv149,qv150,qv151,qv152,qv153,qv154,qv155,qv156,qv157,qv158,qv159,qv160,qv161,qv162,qv163,qv164,qv165,qv166,qv167,qv168,qv169]) (.split qv170 (.leaf 24 [qv169,qv171,qv172,qv173,qv174,qv175,qv176,qv177,qv178,qv179,qv180,qv181,qv182,qv183,qv184,qv185,qv186,qv187,qv188,qv189,qv190,qv191,qv192,qv193,qv194]) (.leaf 24 [qv194,qv195,qv196,qv197,qv198,qv199,qv200,qv201,qv202,qv203,qv204,qv205,qv206,qv207,qv208,qv209,qv210,qv211,qv212,qv213,qv214,qv215,qv216,qv217,qv218]))))))
def secondTree : BernsteinTree := (.split qv1 (.leaf 10 [qv219,qv220,qv221,qv222,qv223,qv224,qv225,qv226,qv227,qv228,qv229]) (.leaf 10 [qv229,qv230,qv231,qv232,qv233,qv234,qv235,qv236,qv237,qv238,qv239]))
def firstMonomial : List ℚ := [qv94,qv240,qv241,qv242,qv243,qv244,qv245,qv246,qv247,qv248,qv249,qv250,qv251,qv252,qv253,qv254,qv255,qv256,qv257,qv258,qv259,qv260,qv261,qv262,qv263]
def secondMonomial : List ℚ := [qv229,qv264,qv265,qv266,qv267,qv268,qv269,qv270,qv271,qv272,qv273]
def density : DensityWitness := ⟨[firstTree,secondTree]⟩
theorem bernList_split_of {p : List ℚ} {a b : ℚ} (mid : ℚ) (L R : BernsteinTree)
    (hm : a<mid ∧ mid<b) (hL : bernListCheck p a mid L=true) (hR : bernListCheck p mid b R=true) :
    bernListCheck p a b (.split mid L R)=true := by
  simpa only [bernListCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using (show (a<mid ∧ mid<b) ∧ bernListCheck p a mid L=true ∧ bernListCheck p mid b R=true from ⟨hm,hL,hR⟩)
theorem firstMonomial_spec : qDensityCoeffs first=firstMonomial := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf0 : bernListCheck firstMonomial (-1) qv45 (.leaf 24 [qv46,qv47,qv48,qv49,qv50,qv51,qv52,qv53,qv54,qv55,qv56,qv57,qv58,qv59,qv60,qv61,qv62,qv63,qv64,qv65,qv66,qv67,qv68,qv69,qv70])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf1 : bernListCheck firstMonomial qv45 qv1 (.leaf 24 [qv70,qv71,qv72,qv73,qv74,qv75,qv76,qv77,qv78,qv79,qv80,qv81,qv82,qv83,qv84,qv85,qv86,qv87,qv88,qv89,qv90,qv91,qv92,qv93,qv94])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf2 : bernListCheck firstMonomial qv1 qv95 (.leaf 24 [qv94,qv96,qv97,qv98,qv99,qv100,qv101,qv102,qv103,qv104,qv105,qv106,qv107,qv108,qv109,qv110,qv111,qv112,qv113,qv114,qv115,qv116,qv117,qv118,qv119])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf3 : bernListCheck firstMonomial qv95 qv120 (.leaf 24 [qv119,qv121,qv122,qv123,qv124,qv125,qv126,qv127,qv128,qv129,qv130,qv131,qv132,qv133,qv134,qv135,qv136,qv137,qv138,qv139,qv140,qv141,qv142,qv143,qv144])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf4 : bernListCheck firstMonomial qv120 qv145 (.leaf 24 [qv144,qv146,qv147,qv148,qv149,qv150,qv151,qv152,qv153,qv154,qv155,qv156,qv157,qv158,qv159,qv160,qv161,qv162,qv163,qv164,qv165,qv166,qv167,qv168,qv169])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf5 : bernListCheck firstMonomial qv145 qv170 (.leaf 24 [qv169,qv171,qv172,qv173,qv174,qv175,qv176,qv177,qv178,qv179,qv180,qv181,qv182,qv183,qv184,qv185,qv186,qv187,qv188,qv189,qv190,qv191,qv192,qv193,qv194])=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_leaf6 : bernListCheck firstMonomial qv170 1 (.leaf 24 [qv194,qv195,qv196,qv197,qv198,qv199,qv200,qv201,qv202,qv203,qv204,qv205,qv206,qv207,qv208,qv209,qv210,qv211,qv212,qv213,qv214,qv215,qv216,qv217,qv218])=true := by decide +kernel
def firstGeometry : Bool := decide (cqSq first.half≠0 ∧ 0<first.coeff.length ∧
  cqSq (cqAdd first.mid first.half)≤sourceRadius^2 ∧ cqSq (cqSub first.mid first.half)≤sourceRadius^2)
set_option trace.profiler true in
theorem firstGeometry_ok : firstGeometry=true := by decide +kernel
set_option trace.profiler true in
theorem firstDensity_fast : bernListCheck (qDensityCoeffs first) (-1) 1 firstTree=true := by
  rw [firstMonomial_spec]
  exact (bernList_split_of _ _ _ (by decide +kernel) (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf0 firstDensity_leaf1) (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf2 (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf3 (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf4 (bernList_split_of _ _ _ (by decide +kernel) firstDensity_leaf5 firstDensity_leaf6)))))
theorem firstDensity_ok : bernCheck first.density (-1) 1 firstTree=true := by
  rw [← qDensityCoeffs_spec first,← bernListCheck_eq]
  exact firstDensity_fast
#print axioms firstDensity_ok
theorem secondMonomial_spec : qDensityCoeffs second=secondMonomial := by decide +kernel
set_option trace.profiler true in
theorem secondDensity_leaf0 : bernListCheck secondMonomial (-1) qv1 (.leaf 10 [qv219,qv220,qv221,qv222,qv223,qv224,qv225,qv226,qv227,qv228,qv229])=true := by decide +kernel
set_option trace.profiler true in
theorem secondDensity_leaf1 : bernListCheck secondMonomial qv1 1 (.leaf 10 [qv229,qv230,qv231,qv232,qv233,qv234,qv235,qv236,qv237,qv238,qv239])=true := by decide +kernel
def secondGeometry : Bool := decide (cqSq second.half≠0 ∧ 0<second.coeff.length ∧
  cqSq (cqAdd second.mid second.half)≤sourceRadius^2 ∧ cqSq (cqSub second.mid second.half)≤sourceRadius^2)
set_option trace.profiler true in
theorem secondGeometry_ok : secondGeometry=true := by decide +kernel
set_option trace.profiler true in
theorem secondDensity_fast : bernListCheck (qDensityCoeffs second) (-1) 1 secondTree=true := by
  rw [secondMonomial_spec]
  exact (bernList_split_of _ _ _ (by decide +kernel) secondDensity_leaf0 secondDensity_leaf1)
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
end CatalanCore.Li2.DecayCert.Simple.Data.L2_15_r24_0.In
