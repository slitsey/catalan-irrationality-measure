module
public import CatalanCore.Li2.DecayCert.Seg.Frame
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CatalanCore.Li2.DecayCert.BentData
open CatalanCore.Li2.DecayCert CatalanCore.Li2.DecayCert.Seg

def coordG2 : ℕ → CQ | 0 => (0,0) | 1 => (((1:ℚ)/200),((1:ℚ)/8)) | _ => (((89:ℚ)/100),((457:ℚ)/200))
theorem coordG2_ok : frameCoordCheck coordG2 2=true := by decide +kernel
noncomputable def frameG2 : BentFrame := bentFrameOf coordG2 2 coordG2_ok

def coordG3 : ℕ → CQ | 0 => (0,0) | 1 => (((2:ℚ)/5),((18:ℚ)/25)) | _ => (((7:ℚ)/5),((68:ℚ)/25))
theorem coordG3_ok : frameCoordCheck coordG3 2=true := by decide +kernel
noncomputable def frameG3 : BentFrame := bentFrameOf coordG3 2 coordG3_ok

def coordG4 : ℕ → CQ | 0 => (0,0) | 1 => (((6:ℚ)/25),((3:ℚ)/10)) | _ => (((167:ℚ)/100),((263:ℚ)/100))
theorem coordG4_ok : frameCoordCheck coordG4 2=true := by decide +kernel
noncomputable def frameG4 : BentFrame := bentFrameOf coordG4 2 coordG4_ok

def coordG15 : ℕ → CQ | 0 => (0,0) | 1 => (((13:ℚ)/50),((3:ℚ)/50)) | _ => (((2:ℚ)/1),((2:ℚ)/1))
theorem coordG15_ok : frameCoordCheck coordG15 2=true := by decide +kernel
noncomputable def frameG15 : BentFrame := bentFrameOf coordG15 2 coordG15_ok

end CatalanCore.Li2.DecayCert.BentData
