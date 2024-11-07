import YatimaStdLib.RBMap
import Lurk.Field

namespace Lurk

/--
Reserved symbols are expected to be in uppercase. Planned to be dropped in favor
of LDON.
-/
inductive LDON
  | num : F → LDON
  | comm : Digest → LDON
  | u64 : UInt64 → LDON
  | char : Char → LDON
  | str : String → LDON
  | sym : String → LDON
  | cons : LDON → LDON → LDON
  deriving Ord, BEq, Repr, Inhabited

namespace LDON

@[match_pattern] def nil : LDON := sym "nil"
@[match_pattern] def t   : LDON := sym "t"

def telescopeCons (acc : Array LDON := #[]) : LDON → Array LDON × LDON
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

def consWith (xs : List LDON) (init : LDON) : LDON :=
  xs.foldr (init := init) cons

def reservedSyms : Std.RBSet String compare := .ofList [
  "nil",
  "t",
  "&rest",
  "atom",
  "apply",
  "begin",
  "car",
  "cdr",
  "char",
  "commit",
  "comm",
  "bignum",
  "cons",
  "current-env",
  "emit",
  "empty-env",
  "eval",
  "eq",
  "eqq",
  "type-eq",
  "type-eqq",
  "hide",
  "if",
  "lambda",
  "let",
  "letrec",
  "u64",
  "open",
  "quote",
  "secret",
  "strcons",
  "list",
  "+",
  "-",
  "*",
  "/",
  "%",
  "=",
  "<",
  ">",
  "<=",
  ">=",
  "breakpoint",
  "fail"] _

open Std Format in
partial def toFormat (esc : Bool) : LDON → Format
  | num n => format n
  | comm d => s!"#c{d.asHex}"
  | u64 n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => if esc && !reservedSyms.contains s then s!"|{s}|" else s
  | x@(.cons ..) =>
    match x.telescopeCons with
    | (xs, nil) => paren $ fmtList xs.data
    | (xs, y) => paren $ fmtList xs.data ++ line ++ "." ++ line ++ (y.toFormat esc)
where
  fmtList : List LDON → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ (x.toFormat esc)) (x.toFormat esc)

def toString (esc : Bool) : LDON → String :=
  ToString.toString ∘ toFormat esc

instance : Std.ToFormat LDON := ⟨toFormat false⟩
instance : ToString LDON := ⟨toString false⟩

namespace Macro

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[$xs,*]) => do
    let ret ← xs.getElems.foldrM (fun x xs => `(LDON.cons $x $xs)) (← `(LDON.nil))
    return ret

end Macro

open Macro in
/-- This helper is needed for the DSL and for the parser -/
def mkQuote (x : LDON) : LDON :=
  ~[sym "quote", x]

class ToLDON (α : Type _) where
  toLDON : α → LDON

export ToLDON (toLDON)

instance : ToLDON Nat where
  toLDON := .num ∘ .ofNat

instance : ToLDON Char where
  toLDON := .char

instance : ToLDON String where
  toLDON := .str

instance [ToLDON α] : ToLDON (List α) where
  toLDON es := LDON.consWith (es.map toLDON) .nil

instance [ToLDON α] : ToLDON (Array α) where
  toLDON es := LDON.consWith (es.data.map toLDON) .nil

instance : ToLDON LDON := ⟨id⟩

end Lurk.LDON
