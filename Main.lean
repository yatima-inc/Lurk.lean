import Lurk.Eval
import Lurk.LightData
import Cli

def lurkRun (p : Cli.Parsed) : IO UInt32 := do
  let store ← match p.flag? "lightstore" |>.map (·.value) with
    | none => pure .empty
    | some store =>
      let store ← IO.FS.readBinFile ⟨store⟩
      let store : LightData ← match Encodable.decode store with
        | .error err => IO.eprintln err; return 1
        | .ok (store : LightData) => pure store
      match Encodable.decode store with
      | .error err => IO.eprintln err; return 1
      | .ok store => pure store

  match p.positionalArg? "source" |>.map (·.value) with
  | none => unreachable!
  | some src =>
    let path := ⟨src⟩
    let code ← IO.FS.readFile path
    match Lurk.Parser.parse code with
    | .error err => do IO.eprintln s!"Parsing error:\n{err}"; return 1
    | .ok x => match x.toExpr with
      | .error err => do IO.eprintln s!"Formatting error:\n{err}"; return 1
      | .ok e => match e.evaluate store with
        | .ok (v, n) => do IO.println s!"[{n} evaluations] => {v}"; return 0
        | .error (err, frames) => do
          IO.eprintln s!"Evaluation error:\n{err}"
          let nFrames := (p.flag? "frames").map (·.as! Nat) |>.getD 5
          IO.FS.writeFile (path.withExtension "frames") (frames.pprint nFrames)
          return 1

def lurkCmd : Cli.Cmd := `[Cli|
  lurk VIA lurkRun; ["0.0.1"]
  "An evaluator for the Lurk language"

  FLAGS:
    ls, "lightstore" : String; "Optional path to the data store"
    f, "frames" : Nat; "The number of frames dumped to a file in case of an error (defaults to 5)"

  ARGS:
    source : String; "Lurk source file"
]

def main (args : List String) : IO UInt32 := do
  lurkCmd.validate args
