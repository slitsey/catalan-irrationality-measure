#!/bin/bash
# usage: try.sh <spec file> [k n]
cd /c/Users/seanl/Documents/Codex/2026-10-11/plea/work/catalan-uniform
sed -e 's/@ENV0@/CatalanCore.Uniform.Decay.PolyWire3.Regress.Chi3.Env0/' -e 's/@ENVNS@/CatalanCore.Uniform.Decay.PolyWire3.Regress.Chi3/' scripts/claude/bank/cover/GenCover.lean.tmpl > scripts/claude/bank/cover/out/Chi3/gendev.lean
../lean-runtime/lean-4.35.0-rc2-windows/bin/lake.exe env lean --run scripts/claude/bank/cover/out/Chi3/gendev.lean "$1" ${2:-0} ${3:-1} 2>&1 | head -${4:-60} | cut -c1-400
