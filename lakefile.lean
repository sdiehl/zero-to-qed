import Lake
open Lake DSL

package ZeroToQED where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

-- Dependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.24.0"

-- Main library
@[default_target]
lean_lib ZeroToQED where
  srcDir := "src"

-- Test library
lean_lib Test where
  srcDir := "test"

-- Main executable (example)
@[default_target]
lean_exe driver where
  root := `Main
  srcDir := "src"

-- Collatz
lean_exe collatz where
  root := `Examples.Collatz
  srcDir := "src"

-- FizzBuzz
lean_exe fizzbuzz where
  root := `Examples.FizzBuzz
  srcDir := "src"

-- Word frequency counter
lean_exe wordfreq where
  root := `Examples.WordFreq
  srcDir := "src"

-- D&D character generator
lean_exe dnd where
  root := `Examples.DndCharacter
  srcDir := "src"

-- JSON serializer demo
lean_exe json where
  root := `Examples.JsonSerializer
  srcDir := "src"

-- Units of measurement demo
lean_exe units where
  root := `Examples.Units
  srcDir := "src"

-- MTG mana system
lean_exe mtg where
  root := `Examples.MtgMana
  srcDir := "src"

-- Spell effects demo
lean_exe spells where
  root := `Examples.SpellEffects
  srcDir := "src"

-- Transporter demo
lean_exe transporter where
  root := `Examples.Transporter
  srcDir := "src"

-- Test executable
@[default_target]
lean_exe tests where
  root := `Test.Main
  srcDir := "test"

-- Test runner script
@[test_driver]
script test do
  let proc ← IO.Process.spawn {
    cmd := ".lake/build/bin/tests"
  }
  let exitCode ← proc.wait
  return if exitCode = 0 then 0 else 1

-- Documentation builder script
script docs do
  IO.println "Building documentation..."

  -- Create docbuild directory if it doesn't exist
  let docbuildPath : System.FilePath := ⟨"docbuild"⟩
  if !(← docbuildPath.pathExists) then
    IO.FS.createDir docbuildPath

  -- Create lakefile.lean for docbuild
  let lakefilePath := docbuildPath / "lakefile.lean"
  let lakefileContent := "import Lake
open Lake DSL

package «docbuild»

require «ZeroToQED» from \"..\"

require «doc-gen4» from git
  \"https://github.com/leanprover/doc-gen4\" @ \"31cc380\"
"
  IO.FS.writeFile lakefilePath lakefileContent

  -- Copy lean-toolchain
  let toolchainSrc : System.FilePath := ⟨"lean-toolchain"⟩
  let toolchainDst := docbuildPath / "lean-toolchain"
  if ← toolchainSrc.pathExists then
    let content ← IO.FS.readFile toolchainSrc
    IO.FS.writeFile toolchainDst content

  -- Run lake update in docbuild
  IO.println "Updating dependencies..."
  let updateProc ← IO.Process.spawn {
    cmd := "lake"
    args := #["update"]
    cwd := docbuildPath
    env := #[("MATHLIB_NO_CACHE_ON_UPDATE", "1")]
  }
  let updateExitCode ← updateProc.wait
  if updateExitCode ≠ 0 then
    IO.println "Error: Failed to update dependencies"
    return 1

  -- Build documentation
  IO.println "Generating documentation..."
  let buildProc ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "ZeroToQED:docs"]
    cwd := docbuildPath
  }
  let buildExitCode ← buildProc.wait
  if buildExitCode ≠ 0 then
    IO.println "Error: Failed to build documentation"
    return 1

  IO.println "Documentation generated successfully!"
  IO.println "View docs at: docbuild/.lake/build/doc/"
  IO.println "To serve locally, run:"
  IO.println "  cd docbuild/.lake/build/doc && python3 -m http.server"
  return 0
