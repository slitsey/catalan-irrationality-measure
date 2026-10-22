module
public import CatalanCore.Cert.SigmaQuarter.PointCheck00
public import CatalanCore.Cert.SigmaQuarter.PointCheck01
public import CatalanCore.Cert.SigmaQuarter.PointCheck02
public import CatalanCore.Cert.SigmaQuarter.PointCheck03
public import CatalanCore.Cert.SigmaQuarter.PointCheck04
public import CatalanCore.Cert.SigmaQuarter.PointCheck05
public import CatalanCore.Cert.SigmaQuarter.PointCheck06
public import CatalanCore.Cert.SigmaQuarter.PointCheck07
public import CatalanCore.Cert.SigmaQuarter.PointCheck08
public import CatalanCore.Cert.SigmaQuarter.PointCheck09
public import CatalanCore.Cert.SigmaQuarter.PointCheck10
public import CatalanCore.Cert.SigmaQuarter.PointCheck11
public import CatalanCore.Cert.SigmaQuarter.PointCheck12
public import CatalanCore.Cert.SigmaQuarter.PointCheck13
public import CatalanCore.Cert.SigmaQuarter.PointCheck14
public import CatalanCore.Cert.SigmaQuarter.PointCheck15
@[expose] public section
namespace CatalanCore.Cert.SigmaQuarter
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem index_chunks : List.range pts.length = checkChunk 0 ++ checkChunk 1 ++ checkChunk 2 ++ checkChunk 3 ++ checkChunk 4 ++ checkChunk 5 ++ checkChunk 6 ++ checkChunk 7 ++ checkChunk 8 ++ checkChunk 9 ++ checkChunk 10 ++ checkChunk 11 ++ checkChunk 12 ++ checkChunk 13 ++ checkChunk 14 ++ checkChunk 15 := by decide +kernel
theorem point_check : (List.range pts.length).all pointCheck = true := by
  rw [index_chunks]
  simp only [List.all_append, checkChunk_0, checkChunk_1, checkChunk_2, checkChunk_3, checkChunk_4, checkChunk_5, checkChunk_6, checkChunk_7, checkChunk_8, checkChunk_9, checkChunk_10, checkChunk_11, checkChunk_12, checkChunk_13, checkChunk_14, checkChunk_15, Bool.and_self]
end CatalanCore.Cert.SigmaQuarter
