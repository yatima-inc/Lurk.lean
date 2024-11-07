import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/argumentcomputer/Poseidon.lean" @ "poseidon2"

require YatimaStdLib from git
  "https://github.com/argumentcomputer/YatimaStdLib.lean" @ "v4.12.0"

require LSpec from git
  "https://github.com/argumentcomputer/LSpec.git" @ "v4.12.0"

require LightData from git
  "https://github.com/argumentcomputer/LightData" @ "v4.12.0"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "main"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.12.0"

lean_exe Tests.Evaluation
lean_exe Tests.Roundtrip
lean_exe Tests.Parsing
lean_exe Tests.Pruning
