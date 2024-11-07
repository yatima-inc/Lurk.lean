import Lake
open Lake DSL

package Lurk


@[default_target]
lean_lib Lurk

lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/lurk-lab/Poseidon.lean" @ "afe6069e38ae07cdffd7ae923c379aeb41009002"

require YatimaStdLib from git
  "https://github.com/lurk-lab/YatimaStdLib.lean" @ "10f2b444390a41ede90ca5c038c6ff972014d433"

require LSpec from git
  "https://github.com/lurk-lab/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require LightData from git
  "https://github.com/lurk-lab/LightData" @ "6dfd01c9e056deaf5b76e20f995c39e840bbde86"

require Megaparsec from git
  "https://github.com/lurk-lab/Megaparsec.lean" @ "3a0fc855661b9179362aac65cbeb08560be32f29"

require Cli from git
  "https://github.com/lurk-lab/Cli.lean" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

lean_exe Tests.Evaluation
lean_exe Tests.Roundtrip
lean_exe Tests.Parsing
lean_exe Tests.Pruning
