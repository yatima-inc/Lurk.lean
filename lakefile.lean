import Lake
open Lake DSL

package Lurk

lean_lib Lurk

@[default_target]
lean_exe lurk where
  root := `Main

require Poseidon from git
  "https://github.com/yatima-inc/Poseidon.lean" @ "4180a316a7822b924e05cda1729d8612fcc81ee7"

require YatimaStdLib from git
  "https://github.com/yatima-inc/YatimaStdLib.lean" @ "10f2b444390a41ede90ca5c038c6ff972014d433"

require LSpec from git
  "https://github.com/yatima-inc/LSpec.git" @ "88f7d23e56a061d32c7173cea5befa4b2c248b41"

require Megaparsec from git
  "https://github.com/yatima-inc/Megaparsec.lean" @ "3a0fc855661b9179362aac65cbeb08560be32f29"

require std from git
  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"

lean_exe Tests.Evaluation
lean_exe Tests.Roundtrip
lean_exe Tests.Parsing
lean_exe Tests.SerDe
lean_exe Tests.Pruning
