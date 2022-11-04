namespace Lurk.Syntax

/-- Symbols are expected to be in uppercase -/
inductive AST
  | nil
  | num : Nat → AST
  | char : Char → AST
  | str : String → AST
  | sym : String → AST
  | cons : AST → AST → AST
  deriving Ord, BEq, Repr, Inhabited

namespace AST

def telescopeCons (acc : Array AST := #[]) : AST → Array AST × AST
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

def escapeSyms : AST → AST
  | sym s => sym s!"|{s}|"
  | cons x y => cons x.escapeSyms y.escapeSyms
  | x => x

open Std Format in
partial def toFormat : AST → Format
  | nil => "NIL"
  | num n => format n
  | char c => s!"#\\{c}"
  | str s => s!"\"{s}\""
  | sym s => s
  | x@(.cons ..) =>
    match x.telescopeCons with
    | (xs, nil) => paren $ fmtList xs.data
    | (xs, y)   => paren $ fmtList xs.data ++ line ++ "." ++ line ++ y.toFormat
where
  fmtList : List AST → Format
    | [] => .nil
    | x::xs => xs.foldl (fun acc x => acc ++ line ++ x.toFormat) x.toFormat

instance : Std.ToFormat AST := ⟨toFormat⟩
instance : ToString AST := ⟨toString ∘ toFormat⟩

section ASThelpers

def consWith (xs : List AST) (init : AST) : AST :=
  xs.foldr (init := init) fun x acc => cons x acc

scoped syntax "~[" withoutPosition(term,*) "]"  : term

macro_rules
  | `(~[$xs,*]) => do
    let ret ← xs.getElems.foldrM (fun x xs => `(AST.cons $x $xs)) (← `(AST.nil))
    return ret

def mkQuote (x : AST) : AST :=
  ~[sym "QUOTE", x]

def mkLambda (args : List String) (body : AST) : AST :=
  ~[sym "LAMBDA", consWith (args.map sym) nil, body]

def mkBindings (binders : List $ String × AST) : AST :=
  consWith (binders.map fun (s, v) => ~[sym s, v]) nil

def mkBlock (kind : String) (binders : List $ String × AST) (body : AST) : AST :=
  ~[sym kind, mkBindings binders, body]

def mkLet (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LET" binders body

def mkLetrec (binders : List $ String × AST) (body : AST) : AST :=
  mkBlock "LETREC" binders body

end ASThelpers

end Lurk.Syntax.AST
