import Lurk.Field
import Lurk.Syntax.AST

open Std

namespace Lurk.Evaluation

/-- Basic Lurk primitives -/
inductive Lit
  -- `t` and `nil`
  | t | nil
  -- Numerical values
  | num  : F → Lit
  -- Strings
  | str  : String → Lit
  -- Characters
  | char : Char → Lit
  deriving Repr, BEq

namespace Lit

def toString : Lit → String
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => ToString.toString n
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

def pprint : Lit → Format
  | .nil        => "NIL"
  | .t          => "T"
  | .num n      => n.asHex
  | .str s      => s!"\"{s}\""
  | .char c     => s!"#\\{c}"

instance : ToFormat Lit where
  format := pprint

def toAST : Lit → Syntax.AST
  | .nil    => .nil
  | .t      => .t
  | .num n  => .num n
  | .str s  => .str s
  | .char c => .char c

end Lit

inductive Op₁
  | atom | car | cdr | emit
  | commit | comm | «open»
  | num | char
  deriving Repr, BEq

open Std Format in
def Op₁.toFormat : Op₁ → Format
| .atom => "ATOM" 
| .car => "CAR" 
| .cdr => "CDR" 
| .emit => "EMIT"
| .commit => "COMMIT" 
| .comm => "COMM" 
| .open => "OPEN"
| .num => "NUM" 
| .char => "CHAR"

instance : Std.ToFormat Op₁ := ⟨Op₁.toFormat⟩

inductive Op₂
  | cons | strcons
  | add | sub | mul | div | numEq | lt | gt | le | ge | eq
  | hide
  deriving Repr, BEq

open Std Format in
def Op₂.toFormat : Op₂ → Format
  | .cons => "CONS" 
  | .strcons => "STRCONS"
  | .add => "+" 
  | .sub => "-" 
  | .mul => "*" 
  | .div => "/" 
  | .numEq => "=" 
  | .lt => "<" 
  | .gt => ">" 
  | .le => "<=" 
  | .ge => ">=" 
  | .eq => "eq"
  | .hide => "hide"

instance : Std.ToFormat Op₂ := ⟨Op₂.toFormat⟩

inductive Expr
  | lit : Lit → Expr
  | sym : String → Expr
  | env : Expr
  | op₁ : Op₁ → Expr → Expr
  | op₂ : Op₂ → Expr → Expr → Expr
  | begin : Expr → Expr → Expr
  | «if» : Expr → Expr → Expr → Expr
  | app₀ : Expr → Expr
  | app  : Expr → Expr → Expr
  | lambda : String → Expr → Expr
  | «let»  : String → Expr → Expr → Expr
  | letrec : String → Expr → Expr → Expr
  | quote : Syntax.AST → Expr
  deriving Repr, Inhabited, BEq

namespace Expr

/-- Telescopes `(lambda (x₁ x₂ ..) body)` into `(body, [x₁, x₂])` -/
def telescopeLam (expr : Expr) : Expr × List String :=
  telescopeLamAux expr []
where
  telescopeLamAux (expr : Expr) (bindAcc : List String) :=
    match expr with
    | .lambda name body => telescopeLamAux body $ name :: bindAcc
    | _ => (expr, bindAcc)

/-- Telescopes `(fn a₁ a₂ ..)` into `(fn, [a₁, a₂, ..])` -/
def telescopeApp (expr : Expr) : Expr × List Expr:=
  telescopeAppAux expr []
where
  telescopeAppAux (expr : Expr) (bindAcc : List Expr) :=
    match expr with
    | .app fn arg => telescopeAppAux fn $ arg :: bindAcc
    | _ => (expr, bindAcc.reverse)

/-- Telescopes `(let ((n₁ e₁) (n₂ e₂) ..) body)` into 
  `(body, [(n₁, e₁), (n₂, e₂), ..])` -/
def telescopeLet (expr : Expr) : Expr × List (String × Expr) :=
  telescopeLetAux expr []
where
  telescopeLetAux (expr : Expr) (bindAcc : List (String × Expr)) :=
    match expr with
    | .let name value body => telescopeLetAux body $ (name, value) :: bindAcc
    | _ => (expr, bindAcc.reverse)

/-- Telescopes `(letrec ((n₁ e₁) (n₂ e₂) ..) body)` into 
  `(body, [(n₁, e₁), (n₂, e₂), ..])` -/
def telescopeLetrec (expr : Expr) : Expr × List (String × Expr) :=
  telescopeLetrecAux expr []
where
  telescopeLetrecAux (expr : Expr) (bindAcc : List (String × Expr)) :=
    match expr with
    | .letrec name value body => telescopeLetrecAux body $ (name, value) :: bindAcc
    | _ => (expr, bindAcc.reverse)

open Std Format Syntax.AST in
partial def toFormat (esc := false) (e : Expr) : Format := 
  let _ : ToFormat Expr := ⟨toFormat⟩ 
  match e with
  | .lit l => format l
  | .sym s => formatSym s
  | .env => .text "CURRENT-ENV"
  | .op₁ op e => 
    paren <| format op ++ " " ++ e.toFormat esc
  | .op₂ op e₁ e₂ => 
    paren <| format op ++ " " ++ e₁.toFormat esc ++ line ++ e₂.toFormat esc
  | .begin e₁ e₂ => 
    paren <| "begin" ++ line ++ e₁.toFormat esc ++ line ++ e₂.toFormat esc
  | .if cond e₁ e₂ => 
    paren <| "if " ++ cond.toFormat esc ++ indentD (e₁.toFormat esc ++ line ++ e₂.toFormat esc)
  | .app₀ fn => paren <| fn.toFormat esc
  | e@(.app ..) => 
    let (fn, args) := telescopeApp e
    let args := args.map $ toFormat esc
    paren <| fn.toFormat esc ++ indentD (joinSep args " ")
  | e@(.lambda ..) => 
    let (body, args) := telescopeLam e
    let args := args.map formatSym
    paren <| "lambda " ++ nest 2 (paren (joinSep args " ")) ++ indentD (body.toFormat esc)
  | e@(.let ..) => 
    let (body, binds) := telescopeLet e
    let binds := binds.map fun (n, e) => paren <| formatSym n ++ indentD (e.toFormat esc)
    paren <| "let " ++ nest 4 (paren <| joinSep binds line) ++ indentD (body.toFormat esc)
  | e@(.letrec ..) => 
    let (body, binds) := telescopeLetrec e
    let binds := binds.map fun (n, e) => paren <| formatSym n ++ indentD (e.toFormat esc)
    paren <| "letrec " ++ nest 7 (paren <| joinSep binds line) ++ indentD (body.toFormat esc)
  | .quote datum => paren <| "quote" ++ line ++ format datum
where 
  formatSym s := if esc && !reservedSyms.contains s then s!"|{s}|" else s

def toString (esc := false) : Expr → String :=
  ToString.toString ∘ toFormat esc

instance : Std.ToFormat Expr := ⟨toFormat⟩
instance : ToString Expr := ⟨toString⟩

end Expr
end Lurk.Evaluation
