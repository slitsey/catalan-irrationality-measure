# RayGlue.lean, SegLineGlue.lean (ported from legacy), Final.lean (CertCore instance) for row D
import sys, json; sys.path.insert(0, '.')
ns = {}; exec(open('mkengine.py', encoding='utf-8').read().split('for src, dst in MAP.items():')[0], ns)
conv = ns['conv']; LEG = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-repo/CatalanLambda/Cert/'
OUT = 'C:/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-thmA/CatalanCore/Cert/SigmaP6/'
P = 'CatalanCore.Cert.SigmaP6.'
cfg = json.load(open('ray_cfg.json')); NRAY = cfg['nmod']; RM = 32; RPER = 32; CPM = cfg['CPM']; NCELL = cfg['ncell']; MS = cfg['Ms']; NSEG = 2048; NLINE = 512
MP = (1883395, 1000000)
def w(n, t): open(OUT + n + '.lean', 'w', encoding='utf-8', newline='\n').write(t)
def rd(n): return open(LEG + n + '.lean', encoding='utf-8').read()
def impr(t, mods): 
    import re
    t = re.sub(r'(public import CatalanLambda\.Cert\.\w+\n)+', ''.join('public import %s%s\n' % (P, m) for m in mods), t, count=1)
    return t
# ---------- RayGlue
t = rd('RayGlue')
t = conv('RayGlue', t)
import re
t = re.sub(r'(public import CatalanLambda\.Cert\.RayM\d+\n)+', ''.join('public import %sRayM%d\n' % (P, i) for i in range(NRAY)), t, count=1)
t = t.replace('public import CatalanLambda.Cert.Bridge', 'public import %sBridge' % P)
t = t.replace('global indexing of the 27 modules (27648 = 864 macros x 32 cells)', 'global indexing of the %d modules (%d = %d macros x %d cells)' % (NRAY, NCELL, NRAY * RPER, RM))
i = t.index('def rayP'); j = t.index('theorem rayAll_ok')
t = t[:i] + 'def rayP : ℕ → ℕ\n' + ''.join('  | %d => RayM%dP\n' % (k, k) for k in range(NRAY)) + '  | _ => 0\n\n' + t[j:]
i = t.index('exacts ['); j = t.index(']', i)
t = t[:i] + 'exacts [' + ', '.join('RayM%d_ok' % k for k in range(NRAY)) + t[j:]
t = t.replace('∀ m < 27', '∀ m < %d' % NRAY).replace('27648', str(NCELL))
NL = chr(10)
rayM_def = 'def rayM : ℕ → ℕ' + NL + ''.join('  | %d => %d' % (k, m) + NL for k, m in enumerate(MS)) + '  | _ => 1' + NL + NL
rayM_lem = ('theorem rayM_pos (m : ℕ) : 0 < rayM m := by' + NL + '  unfold rayM; split <;> norm_num' + NL + NL +
  'theorem rayM_dvd (m : ℕ) (hm : m < %d) : rayM m ∣ %d := by' % (NRAY, CPM) + NL + '  interval_cases m <;> decide' + NL + NL)
t = t.replace('def rayP : ℕ → ℕ', rayM_def + 'def rayP : ℕ → ℕ', 1)
t = t.replace('∀ j < 32, rayMacroOK MPRAY 32 (rayP m) j = true', '∀ j < %d / rayM m, rayMacroOK MPRAY (rayM m) (rayP m) j = true' % CPM)
t = t.replace('def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ := cellBox 32 (rayP (i / 1024)) ((i % 1024) / 32) (i % 32)',
  rayM_lem + 'def rayCellG (i : ℕ) : ℤ × ℤ × ℤ × ℤ :=' + NL + '  cellBox (rayM (i / %d)) (rayP (i / %d)) ((i %% %d) / rayM (i / %d)) (i %% rayM (i / %d))' % (CPM, CPM, CPM, CPM, CPM))
k = t.index('  rayMod_sound MPRAY 32'); k2 = t.index(NL + NL, k)
t = t[:k] + ('  rayMod_sound MPRAY (rayM (i / %d)) (rayP (i / %d)) (%d / rayM (i / %d)) (rayAll_ok (i / %d) (by omega))' % (CPM, CPM, CPM, CPM, CPM) + NL +
 '    ((i %% %d) / rayM (i / %d))' % (CPM, CPM) + NL +
 '    (Nat.div_lt_div_of_lt_of_dvd (rayM_dvd _ (by omega)) (Nat.mod_lt _ (by omega))) (i %% rayM (i / %d)) (Nat.mod_lt _ (rayM_pos _)) x y h1 h2 h3 h4' % CPM) + t[k2:]
t = t.replace('1024', str(CPM))
t = t.replace('150 * b.1 ≤ -21 * 2 ^ 40 - 50 * b.2.2.2 - 153600', '30 * b.1 ≤ -3 * 2 ^ 40 - 10 * b.2.2.2 - 30720').replace('-21 * 2 ^ 40 - 50 * b.2.2.1 + 153600 ≤ 150 * b.2.1', '-3 * 2 ^ 40 - 10 * b.2.2.1 + 30720 ≤ 30 * b.2.1')
t = t.replace('150 * (rayCellG i).1 ≤ -21 * 2 ^ 40 - 50 * (rayCellG i).2.2.2 - 153600', '30 * (rayCellG i).1 ≤ -3 * 2 ^ 40 - 10 * (rayCellG i).2.2.2 - 30720').replace('-21 * 2 ^ 40 - 50 * (rayCellG i).2.2.1 + 153600 ≤ 150 * (rayCellG i).2.1', '-3 * 2 ^ 40 - 10 * (rayCellG i).2.2.1 + 30720 ≤ 30 * (rayCellG i).2.1')
# per-module geometry / chain theorems (one kernel evaluation per module keeps memory flat)
i = t.index('theorem ray_geom : ∀ m'); j = t.index('theorem ray_ends')
NL = chr(10)
per = ''
for k in range(NRAY):
    per += "theorem ray_geom_%d : (List.range %d).all (fun i => geomCell (rayCellG (%d * %d + i))) = true := by" % (k, CPM, CPM, k) + NL + "  decide +kernel" + NL + NL
for k in range(NRAY):
    per += "theorem ray_chain_%d : (List.range %d).all (fun i => rayChainCell (%d * %d + i)) = true := by" % (k, CPM, CPM, k) + NL + "  decide +kernel" + NL + NL
per += "theorem ray_geom : ∀ m < %d, (List.range %d).all (fun i => geomCell (rayCellG (%d * m + i))) = true := by" % (NRAY, CPM, CPM) + NL + "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("ray_geom_%d" % k for k in range(NRAY)) + NL + NL
per += "theorem ray_chain : ∀ m < %d, (List.range %d).all (fun i => rayChainCell (%d * m + i)) = true := by" % (NRAY, CPM, CPM) + NL + "  intro m hm" + NL + "  interval_cases m" + NL + "  exacts [%s]" % ", ".join("ray_chain_%d" % k for k in range(NRAY)) + NL + NL
t = t[:i] + per + t[j:]
t = t.replace('27647', str(NCELL - 1))
w('RayGlue', t)
# ---------- SegLineGlue
cells = json.load(open('real_cells.json'))
SV = 0
for a, b, g in cells['seg']:
    SV += (b - a) * (g * MP[1] - MP[0] * 2 ** 32 if g * MP[1] <= MP[0] * 2 ** 32 else 0)
t = conv('SegLineGlue', rd('SegLineGlue'))
t = re.sub(r'(public import CatalanLambda\.Cert\.\w+\n)+', ''.join('public import %s%s\n' % (P, m) for m in ['SegA', 'SegB', 'LineM', 'Bridge']), t, count=1)
t = t.replace('2815', str(NSEG - 1)).replace('2816', str(NSEG)).replace('1408', str(NSEG // 2)).replace('i / 32 - 44', 'i / 32 - %d' % (NSEG // 64)).replace('704', str(NSEG // 4))
t = t.replace('50 * (segCellG 0).1 ≤ -7 * 2 ^ 40', '10 * (segCellG 0).1 ≤ -1 * 2 ^ 40')
t = t.replace('100000', str(MP[1])).replace('197179', str(MP[0]))
t = re.sub(r'def SVAL : ℤ := -?\d+', 'def SVAL : ℤ := %d' % SV, t)
w('SegLineGlue', t)
print('SVAL', SV, 'Sbase', SV / (MP[1] * 2 ** 72))
# ---------- Final
t = conv('Final', rd('Final'))
t = re.sub(r'(public import CatalanLambda\.Cert\.\w+\n)+', ''.join('public import %s%s\n' % (P, m) for m in ['RayGlue', 'SegLineGlue', 'IBound', 'Tail']) + 'public import CatalanCore.Cert.Facts\n', t, count=1)
t = t.replace('27648', str(NCELL)).replace('27647', str(NCELL - 1)).replace('2815', str(NSEG - 1)).replace('2816', str(NSEG))
t = t.replace('(150 : ℝ) * xlo ≤ -21 * 2 ^ 40 - 50 * yhi - 153600', '(30 : ℝ) * xlo ≤ -3 * 2 ^ 40 - 10 * yhi - 30720').replace('(-21 : ℝ) * 2 ^ 40 - 50 * ylo + 153600 ≤ 150 * xhi', '(-3 : ℝ) * 2 ^ 40 - 10 * ylo + 30720 ≤ 30 * xhi')
t = t.replace('7 / 50', '1 / 10').replace('-7 * 2 ^ 40', '-1 * 2 ^ 40').replace('(50 : ℝ) * ((segCellG 0).1 : ℝ)', '(10 : ℝ) * ((segCellG 0).1 : ℝ)')
t = t.replace('197179 / 100000', '1883395 / 1000000').replace('197179 * 2 ^ 32', '1883395 * 2 ^ 32').replace('* 100000 ≤', '* 1000000 ≤').replace('* 100000 -', '* 1000000 -').replace('(100000 * 2 ^ 72)', '(1000000 * 2 ^ 72)').replace('< (segCellG i).2.2 * 100000', '< (segCellG i).2.2 * 1000000')
t = t.replace('-14645 / 10000', '-14419 / 10000').replace('(197179 : ℝ) * 2 ^ 32 < ((segCellG i).2.2 : ℝ) * 100000', '(1883395 : ℝ) * 2 ^ 32 < ((segCellG i).2.2 : ℝ) * 1000000')
t = t.replace('σ = `` the K = 699 measure', 'sigma = the K = 699 measure').replace('ρ = 1/1024', 'ρ = 1/2048').replace('r0 = 7/50', 'r0 = 1/10').replace('m′ = 197179/100000', 'm′ = 1883395/1000000').replace('g_min = -14645/10000', 'g_min = -14419/10000')
t = t.replace('realCell 32 LineMP (i / 32) (i % 32)', 'realCell 16 LineMP (i / 16) (i % 16)')
t = t.replace('ℚ) 32 LineMP (i / 32) (LineM_ok (i / 32) (by omega))', 'ℚ) 16 LineMP (i / 16) (LineM_ok (i / 16) (by omega))').replace('    (i % 32) (by omega) x h1 h2', '    (i % 16) (by omega) x h1 h2')
t = t.replace('def SCERT : ℚ := 2 * (SVAL : ℚ)', 'def SBASE : ℚ := (SVAL : ℚ)')
t = t.replace('theorem Scert_le_thm : (SCERT : ℝ) ≤ 2 * ∑ i', 'theorem Sbase_le_thm : (SBASE : ℝ) ≤ ∑ i')
t = t.replace('unfold SCERT\n  push_cast\n  apply le_of_eq\n  ring', 'unfold SBASE\n  push_cast\n  apply le_of_eq\n  ring')
t = t.replace('(MPRAY : ℝ)', '(MPRAY : ℝ)')
i = t.index('/-! ### the packaged certificate -/')
t = t[:i] + '''/-! ### the packaged certificate -/

open CatalanCore.Cert in
noncomputable def certCore : CertCore 699 (1 / 2048 : ℝ) (1 / 1000 : ℝ) cS mS where
  r0 := 1 / 10
  W := 1 / 2 ^ 30
  umax := 3 / 2
  mprime := MPRAY
  gmin := -14419 / 10000
  Sbase := SBASE
  Ibound := IBOUND
  ccert := 66510 / 10000
  r0_pos := by norm_num
  W_pos := by norm_num
  hρ := by norm_num
  hε0 := by norm_num
  hε1 := by norm_num
  hm := mS_sum
  g_conj := g_conj_cert
  rayBoxes := rayBoxes
  ray_box_ok := ray_box_ok_thm
  ray_cover := ray_cover_thm
  ray_tail := ray_tail_thm
  nSeg := %d
  segA := segAq
  segB := segBq
  segG := segGq
  seg_ab := seg_ab_thm
  seg_ok := seg_ok_thm
  seg_cover := seg_cover_thm
  Sbase_le := Sbase_le_thm
  lineCells := lineCellsL
  line_ok := line_ok_thm
  line_cover := line_cover_thm
  I_ok := I_ok
  ccert_ge := by
    unfold MPRAY
    push_cast
    norm_num

open CatalanCore.Cert in
/-- The decay exponent of the row-D certificate at atom density `3` (P6). -/
theorem Dof_three : (30408 / 10000 : ℚ) ≤ certCore.Dof 3 0 (3 / 2) := by
  unfold CertCore.Dof certCore
  simp only [SBASE, IBOUND, MPRAY, SVAL]
  norm_num

end CatalanCore.Cert.SigmaP6
''' % NSEG
w('Final', t)
