import Lake
open Lake

def main (args : List String) : IO Unit := do
  let paths ← IO.FS.lines (args.headD "")
  let mut output := ""
  for path in paths do
    let h ← Lake.computeTextFileHash path
    output := output ++ s!"{path}\t{h.hex}\n"
  IO.FS.writeFile (args[1]!) output
  IO.println s!"Computed {paths.size} actual Lake source hashes"
