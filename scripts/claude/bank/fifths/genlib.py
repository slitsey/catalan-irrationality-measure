"""Shared helpers of gen_cov.py / gen_uf.py (piece data, leaf definitions, piece proofs)."""
from pathlib import Path
from fractions import Fraction as Q
from math import lcm
import json, sys
NL = chr(10)
R = Path(__file__).resolve().parents[4]
B = R / 'CatalanCore/Uniform/Bank/FifthsContent'
S = R / 'scripts/claude/bank/fifths'
C0 = 2600000000
NS = 'CatalanCore.Uniform.Bank.FifthsContent'
al = Q(1, 9)
TEND = Q(63, 10)


def pdata(left, right, a0, b0):
    left, right, a0, b0 = Q(left), Q(right), Q(a0), Q(b0)
    D = lcm(a0.denominator, b0.denominator)
    return (left.numerator, left.denominator, right.numerator, right.denominator,
            int(a0 * D), int(b0 * D), C0 * D, D)


def mk(args):
    sn, sd, tn, td, A, Bc, E, D = args
    return 'mkPiece %d %d %d %d (%d) (%d) (%d) (%d)' % (sn, sd, tn, td, A, Bc, E, D)


def qf(x):
    return '(%d / %d)' % (x.numerator, x.denominator)


HDR = ('import CatalanCore.Uniform.Content.Member.Template' + NL +
       'import CatalanCore.Arith.Hybrid.PieceTools' + NL +
       'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL +
       'set_option maxHeartbeats 1600000' + NL +
       'namespace ' + NS + NL + 'open CatalanCore.Arith.Hybrid' + NL)


def leaf_def(name, start, end, pieces, doc=''):
    rows = (',' + NL).join('  ' + mk(a) for a in pieces)
    mass = sum((Q(a[4], a[7]) * (Q(a[2], a[3]) - Q(a[0], a[1])) +
                Q(a[5], a[7]) * (Q(a[2], a[3]) ** 2 - Q(a[0], a[1]) ** 2) / 2 for a in pieces), Q(0))
    t = HDR + doc + 'noncomputable def %s : List Piece := [%s%s]%s%s' % (name, NL, rows, NL, NL)
    t += 'def %sMass : ℚ := %s%s' % (name, qf(mass), NL)
    t += 'theorem %s_chain : Chain %s %s := by%s  norm_num [%s, Chain, mkPiece]%s' % (name, qf(start), name, NL, name, NL)
    t += 'theorem %s_end : lastEnd %s %s = %s := by%s  norm_num [%s, lastEnd, mkPiece]%s' % (name, qf(start), name, qf(end), NL, name, NL)
    t += 'theorem %s_mass : listInt %s = (%sMass : ℝ) := by%s  norm_num [%s, listInt, Piece.int, %sMass, mkPiece]%s' % (name, name, name, NL, name, name, NL)
    for suf in ('chain', 'end', 'mass'):
        t += '#print axioms %s_%s%s' % (name, suf, NL)
    t += 'end ' + NS + NL
    return t, mass


def num4():
    return '(by norm_num) (by norm_num) (by norm_num) (by norm_num)'


def head_j(name, j, args, extra_j=False, dep=False):
    sn, sd, tn, td, A, Bc, E, D = args
    h = 'theorem %s {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49)' % name
    if dep:
        h += ' (hdepth : depth ≤ 1000)'
    if extra_j:
        h += ' (j : ℕ)'
    h += ' :' + NL
    h += '    PieceOK T depth %s %d %d %d %d (%d) (%d) (%d) (%d) := by%s' % ('j' if extra_j else str(j), sn, sd, tn, td, A, Bc, E, D, NL)
    return h


def piece_proof(name, j, args, layer, meta):
    sn, sd, tn, td, A, Bc, E, D = args
    nn = '(by intro r p h1 h2; omega)'
    if layer == 'M3D':
        n0, n1, n3 = meta['n0'], meta['n1'], meta['n3']
        return head_j(name, j, args) + (
            '  refine pieceOK_m3 T depth hcF %d %d %d %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (n0, n1, n3, j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
            '  exact ⟨by omega, by omega⟩' + NL)
    if layer == 'LP':
        lpk = 'pieceOK_lp1' if Q(tn, td) <= 1 else 'pieceOK_lp2'
        return head_j(name, j, args, False, True) + (
            '  refine %s T depth hcF hdepth %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (lpk, j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
            ('  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> omega' + NL if lpk == 'pieceOK_lp1' else
             '  refine ⟨fun hlt => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, fun hge => ⟨⟨?_, ?_⟩, ?_⟩⟩ <;> omega' + NL))
    kd = meta['kind'] or 'D6'
    if kd in ('saw0', 'saw', 'D3'):
        return head_j(name, j, args) + (
            '  refine pieceOK_saw T depth hcF 0 %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (j, sn, sd, tn, td, num4(), nn, NL) +
            '  intro r p m hR hb1 hb2 h1 h2' + NL + '  unfold R0 at hR' + NL +
            '  refine ⟨⟨by omega, by omega⟩, ?_⟩' + NL + '  intro s0 hs0 hd' + NL + '  omega' + NL)
    k2 = {'D3': 'pieceOK_D3', 'D45': 'pieceOK_D45', 'D45z': 'pieceOK_D45', 'D6': 'pieceOK_D6'}[kd]
    return head_j(name, j, args) + (
        '  refine %s T depth hcF %d %d %d %d %d _ _ _ _ %s %s ?_%s' % (k2, j, sn, sd, tn, td, num4(), nn, NL) +
        '  intro r p m k hR hb1 hb2 hu0 hu1 hk h1 h2' + NL + '  unfold R0 at hR' + NL +
        '  exact ⟨⟨by omega, by omega⟩, by omega⟩' + NL)


def piece_proof_saw(name, args, q0):
    sn, sd, tn, td, A, Bc, E, D = args
    return head_j(name, 0, args, True) + (
        '  refine pieceOK_saw T depth hcF %d j %d %d %d %d _ _ _ _ %s (by intro r p h1 h2; omega) ?_%s' % (q0, sn, sd, tn, td, num4(), NL) +
        '  intro r p m hR hb1 hb2 h1 h2' + NL + '  unfold R0 at hR' + NL +
        '  refine ⟨⟨by omega, by omega⟩, ?_⟩' + NL + '  intro s0 hs0 hd' + NL + '  omega' + NL)


def cover_header(extra_imp):
    return ('import %s.Cov%s' % (NS, NL) + extra_imp +
            'set_option Elab.async false' + NL + 'set_option maxRecDepth 10000' + NL +
            'set_option maxHeartbeats 1600000' + NL +
            'namespace %s%sopen CatalanCore CatalanCore.Arith.Hybrid CatalanFrames.Fifths%s%s' % (NS, NL, NL, NL))


