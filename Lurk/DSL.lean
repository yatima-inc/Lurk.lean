import Lean
import Lurk.ExprLDON

namespace Lurk

open Lean Elab Meta Term

namespace DSL

declare_syntax_cat    atom_
scoped syntax "t"   : atom_
scoped syntax "T"   : atom_
scoped syntax "nil" : atom_
scoped syntax "NIL" : atom_

declare_syntax_cat       op₁
scoped syntax "atom"   : op₁
scoped syntax "ATOM"   : op₁
scoped syntax "car"    : op₁
scoped syntax "CAR"    : op₁
scoped syntax "cdr"    : op₁
scoped syntax "CDR"    : op₁
scoped syntax "emit"   : op₁
scoped syntax "EMIT"   : op₁
scoped syntax "commit" : op₁
scoped syntax "COMMIT" : op₁
scoped syntax "comm"   : op₁
scoped syntax "COMM"   : op₁
scoped syntax "open"   : op₁
scoped syntax "OPEN"   : op₁
scoped syntax "num"    : op₁
scoped syntax "NUM"    : op₁
scoped syntax "u64"    : op₁
scoped syntax "U64"    : op₁
scoped syntax "char"   : op₁
scoped syntax "CHAR"   : op₁

declare_syntax_cat        op₂
scoped syntax "cons"    : op₂
scoped syntax "CONS"    : op₂
scoped syntax "strcons" : op₂
scoped syntax "STRCONS" : op₂
scoped syntax "+"       : op₂
scoped syntax "-"       : op₂
scoped syntax "*"       : op₂
scoped syntax "/"       : op₂
scoped syntax "%"       : op₂
scoped syntax "="       : op₂
scoped syntax "<"       : op₂
scoped syntax ">"       : op₂
scoped syntax "<="      : op₂
scoped syntax ">="      : op₂
scoped syntax "eq"      : op₂
scoped syntax "EQ"      : op₂
scoped syntax "hide"    : op₂
scoped syntax "HIDE"    : op₂

end DSL

namespace LDON.DSL

declare_syntax_cat    sym
scoped syntax ident : sym
scoped syntax atom_ : sym
scoped syntax op₁   : sym
scoped syntax op₂   : sym
-- these can't be simple idents because they'd clash with Lean's syntax
scoped syntax "if"  : sym
scoped syntax "IF"  : sym
scoped syntax "let" : sym
scoped syntax "LET" : sym
scoped syntax "letrec" : sym
scoped syntax "LETREC" : sym
scoped syntax "lambda" : sym
scoped syntax "LAMBDA" : sym
scoped syntax "begin" : sym
scoped syntax "BEGIN" : sym
scoped syntax "quote" : sym
scoped syntax "QUOTE" : sym
scoped syntax "eval" : sym
scoped syntax "EVAL" : sym
-- a workaround for the dash
scoped syntax "current-env" : sym
scoped syntax "CURRENT-ENV" : sym
-- escaping symbols
scoped syntax "|" sym "|" : sym
-- symbols with a dot followed by a number
scoped syntax ident noWs "." noWs num : sym
scoped syntax "[anonymous]" : sym

def mergeWithDot (s : String) (n : Nat) : String :=
  s!"{s}.{n}"

private def mkSym (sym : String) :=
  mkAppM ``LDON.sym #[mkStrLit sym]

open Lurk.DSL in
def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)   | `(atom_| t)   => mkSym "T"
  | `(atom_| NIL) | `(atom_| nil) => mkSym "NIL"
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
def elabOp₁ : TSyntax `op₁ → TermElabM Lean.Expr
  | `(op₁| ATOM)   | `(op₁| atom)   => mkSym "ATOM"
  | `(op₁| CAR)    | `(op₁| car)    => mkSym "CAR"
  | `(op₁| CDR)    | `(op₁| cdr)    => mkSym "CDR"
  | `(op₁| EMIT)   | `(op₁| emit)   => mkSym "EMIT"
  | `(op₁| COMMIT) | `(op₁| commit) => mkSym "COMMIT"
  | `(op₁| COMM)   | `(op₁| comm)   => mkSym "COMM"
  | `(op₁| OPEN)   | `(op₁| open)   => mkSym "OPEN"
  | `(op₁| NUM)    | `(op₁| num)    => mkSym "NUM"
  | `(op₁| U64)    | `(op₁| u64)    => mkSym "U64"
  | `(op₁| CHAR)   | `(op₁| char)   => mkSym "CHAR"
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
def elabOp₂ : TSyntax `op₂ → TermElabM Lean.Expr
  | `(op₂| CONS)    | `(op₂| cons)    => mkSym "CONS"
  | `(op₂| STRCONS) | `(op₂| strcons) => mkSym "STRCONS"
  | `(op₂| EQ)      | `(op₂| eq)      => mkSym "EQ"
  | `(op₂| HIDE)    | `(op₂| hide)    => mkSym "HIDE"
  | `(op₂| +)  => mkSym "+"
  | `(op₂| -)  => mkSym "-"
  | `(op₂| *)  => mkSym "*"
  | `(op₂| /)  => mkSym "/"
  | `(op₂| %)  => mkSym "%"
  | `(op₂| =)  => mkSym "="
  | `(op₂| <)  => mkSym "<"
  | `(op₂| >)  => mkSym ">"
  | `(op₂| <=) => mkSym "<="
  | `(op₂| >=) => mkSym ">="
  | _ => throwUnsupportedSyntax

partial def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident) =>
    let i  := i.getId.toString
    let iU := i.toUpper
    if LDON.reservedSyms.contains iU then
      mkSym iU
    else
      mkSym i
  | `(sym| $a:atom_) => elabAtom a
  | `(sym| $o:op₁) => elabOp₁ o
  | `(sym| $o:op₂) => elabOp₂ o
  | `(sym| current-env) | `(sym| CURRENT-ENV) => mkSym "CURRENT-ENV"
  | `(sym| if)          | `(sym| IF)          => mkSym "IF"
  | `(sym| let)         | `(sym| LET)         => mkSym "LET"
  | `(sym| letrec)      | `(sym| LETREC)      => mkSym "LETREC"
  | `(sym| lambda)      | `(sym| LAMBDA)      => mkSym "LAMBDA"
  | `(sym| begin)       | `(sym| BEGIN)       => mkSym "BEGIN"
  | `(sym| quote)       | `(sym| QUOTE)       => mkSym "QUOTE"
  | `(sym| eval)        | `(sym| EVAL)        => mkSym "EVAL"
  | `(sym| | $i:ident |) => mkSym i.getId.toString
  | `(sym| | current-env |)  => mkSym "current-env"
  | `(sym| | if |)  => mkSym "if"
  | `(sym| | let |) => mkSym "let"
  | `(sym| $i:ident.$n:num)
  | `(sym| | $i:ident.$n:num |) => do
    let sym ← mkAppM ``mergeWithDot #[mkStrLit i.getId.toString, mkNatLit n.getNat]
    mkAppM ``LDON.sym #[sym]
  | `(sym| [anonymous])
  | `(sym| |[anonymous]|) => mkSym "[anonymous]"
  | _ => throwUnsupportedSyntax

declare_syntax_cat                       ldon
scoped syntax num                      : ldon
scoped syntax char                     : ldon
scoped syntax str                      : ldon
scoped syntax sym                      : ldon
scoped syntax "(" ldon* ")"            : ldon
scoped syntax "(" ldon+ " . " ldon ")" : ldon
scoped syntax "," ldon                 : ldon -- quoting

mutual

partial def elabLDONCons (xs : Array $ TSyntax `ldon) (init : Lean.Expr) : TermElabM Lean.Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``LDON.cons #[← elabLDON e, acc]

partial def elabLDON : TSyntax `ldon → TermElabM Lean.Expr
  | `(ldon| $n:num) => do mkAppM ``LDON.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(ldon| $c:char) => do
    mkAppM ``LDON.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ldon| $s:str) => mkAppM ``LDON.str #[mkStrLit s.getString]
  | `(ldon| $s:sym) => elabSym s
  | `(ldon| ()) => pure $ mkConst ``LDON.nil
  | `(ldon| ($xs*)) => elabLDONCons xs (mkConst ``LDON.nil)
  | `(ldon| ($x . $y)) => do mkAppM ``LDON.cons #[← elabLDON x, ← elabLDON y]
  | `(ldon| ($xs* . $x)) => do elabLDONCons xs (← elabLDON x)
  | `(ldon| ,$x:ldon) => do mkAppM ``LDON.mkQuote #[← elabLDON x]
  | `(ldon| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``LDON.toLDON #[e]
    else throwUnsupportedSyntax

end

scoped elab "⟪" x:ldon "⟫" : term =>
  elabLDON x

end LDON.DSL

namespace Expr.DSL

open Lurk.DSL in
def elabAtom : TSyntax `atom_ → TermElabM Lean.Expr
  | `(atom_| T)   | `(atom_| t)   => return mkConst ``Atom.t
  | `(atom_| NIL) | `(atom_| nil) => return mkConst ``Atom.nil
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
def elabOp₁ : TSyntax `op₁ → TermElabM Lean.Expr
  | `(op₁| ATOM)   | `(op₁| atom)   => return mkConst ``Op₁.atom
  | `(op₁| CAR)    | `(op₁| car)    => return mkConst ``Op₁.car
  | `(op₁| CDR)    | `(op₁| cdr)    => return mkConst ``Op₁.cdr
  | `(op₁| EMIT)   | `(op₁| emit)   => return mkConst ``Op₁.emit
  | `(op₁| COMMIT) | `(op₁| commit) => return mkConst ``Op₁.commit
  | `(op₁| COMM)   | `(op₁| comm)   => return mkConst ``Op₁.comm
  | `(op₁| OPEN)   | `(op₁| open)   => return mkConst ``Op₁.open
  | `(op₁| NUM)    | `(op₁| num)    => return mkConst ``Op₁.num
  | `(op₁| U64)    | `(op₁| u64)    => return mkConst ``Op₁.u64
  | `(op₁| CHAR)   | `(op₁| char)   => return mkConst ``Op₁.char
  | _ => throwUnsupportedSyntax

open Lurk.DSL in
def elabOp₂ : TSyntax `op₂ → TermElabM Lean.Expr
  | `(op₂| CONS)    | `(op₂| cons)    => return mkConst ``Op₂.cons
  | `(op₂| STRCONS) | `(op₂| strcons) => return mkConst ``Op₂.strcons
  | `(op₂| EQ)      | `(op₂| eq)      => return mkConst ``Op₂.eq
  | `(op₂| HIDE)    | `(op₂| hide)    => return mkConst ``Op₂.hide
  | `(op₂| +)  => return mkConst ``Op₂.add
  | `(op₂| -)  => return mkConst ``Op₂.sub
  | `(op₂| *)  => return mkConst ``Op₂.mul
  | `(op₂| /)  => return mkConst ``Op₂.div
  | `(op₂| %)  => return mkConst ``Op₂.mod
  | `(op₂| =)  => return mkConst ``Op₂.numEq
  | `(op₂| <)  => return mkConst ``Op₂.lt
  | `(op₂| >)  => return mkConst ``Op₂.gt
  | `(op₂| <=) => return mkConst ``Op₂.le
  | `(op₂| >=) => return mkConst ``Op₂.ge
  | _ => throwUnsupportedSyntax

declare_syntax_cat                                   expr
scoped syntax atom_                                : expr
scoped syntax ident                                : expr
scoped syntax num                                  : expr
scoped syntax "#c" noWs num                        : expr -- Commitments
scoped syntax char                                 : expr
scoped syntax str                                  : expr
scoped syntax "(" "current-env" ")"                : expr
scoped syntax "(" "CURRENT-ENV" ")"                : expr
scoped syntax "(" op₁ expr ")"                     : expr
scoped syntax "(" op₂ expr expr ")"                : expr
scoped syntax "(" "begin" expr* ")"                : expr
scoped syntax "(" "BEGIN" expr* ")"                : expr
scoped syntax "(" "if" expr expr expr ")"          : expr
scoped syntax "(" "IF" expr expr expr ")"          : expr
scoped syntax "(" "lambda" "(" ident* ")" expr ")" : expr
scoped syntax "(" "LAMBDA" "(" ident* ")" expr ")" : expr
scoped syntax "(" "quote" ldon ")"                 : expr
scoped syntax "(" "QUOTE" ldon ")"                 : expr
scoped syntax "," ldon                             : expr
scoped syntax "(" "eval" expr (expr)? ")"          : expr
scoped syntax "(" "EVAL" expr (expr)? ")"          : expr
scoped syntax (priority := low) "(" expr* ")"      : expr

declare_syntax_cat binder
scoped syntax "(" ident expr ")" : binder

scoped syntax "(" "let"    "(" binder* ")" expr ")" : expr
scoped syntax "(" "LET"    "(" binder* ")" expr ")" : expr
scoped syntax "(" "letrec" "(" binder* ")" expr ")" : expr
scoped syntax "(" "LETREC" "(" binder* ")" expr ")" : expr

mutual

partial def elabExpr : TSyntax `expr → TermElabM Lean.Expr
  | `(expr| $a:atom_) => do mkAppM ``Expr.atom #[← elabAtom a]
  | `(expr| $s:ident) => do mkAppM ``Expr.sym #[mkStrLit s.getId.toString]
  | `(expr| $n:num) => do
    let atom ← mkAppM ``Atom.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
    mkAppM ``Expr.atom #[atom]
  | `(expr | #c$n:num) => do
    let atom ← mkAppM ``Atom.commit #[← mkAppM ``Digest.fromComm #[mkNatLit n.getNat]]
    mkAppM ``Expr.atom #[atom]
  | `(expr| $c:char) => do
    let atom ← mkAppM ``Atom.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
    mkAppM ``Expr.atom #[atom]
  | `(expr| $s:str) => do
    let atom ← mkAppM ``Atom.str #[mkStrLit s.getString]
    mkAppM ``Expr.atom #[atom]
  | `(expr| (current-env)) | `(expr| (CURRENT-ENV)) => return mkConst ``Expr.env
  | `(expr| ($o:op₁ $e)) => do mkAppM ``Expr.op₁ #[← elabOp₁ o, ← elabExpr e]
  | `(expr| ($o:op₂ $e₁ $e₂)) => do
    mkAppM ``Expr.op₂ #[← elabOp₂ o, ← elabExpr e₁, ← elabExpr e₂]
  | `(expr| (BEGIN)) | `(expr| (begin)) => mkAppM ``Expr.atom #[mkConst ``Atom.nil]
  | `(expr| (BEGIN $es*)) | `(expr| (begin $es*)) => do
    es.foldrM (init := mkConst ``Expr.nil) fun e acc => do
      mkAppM ``Expr.begin #[← elabExpr e, acc]
  | `(expr| (IF $a $b $c)) | `(expr| (if $a $b $c)) => do
    mkAppM ``Expr.if #[← elabExpr a, ← elabExpr b, ← elabExpr c]
  | `(expr| (LAMBDA ($ss*) $b:expr))
  | `(expr| (lambda ($ss*) $b:expr)) => do
    if ss.size == 0 then
      mkAppM ``Expr.lambda #[mkStrLit "_", ← elabExpr b]
    else
      ss.foldrM (init := ← elabExpr b) fun s acc => do
        mkAppM ``Expr.lambda #[mkStrLit s.getId.toString, acc]
  | `(expr| (LET ($bs*) $bd:expr))
  | `(expr| (let ($bs*) $bd:expr)) => do
    bs.foldrM (init := ← elabExpr bd) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.let #[s, v, acc]
  | `(expr| (LETREC ($bs*) $bd:expr))
  | `(expr| (letrec ($bs*) $bd:expr)) => do
    bs.foldrM (init := ← elabExpr bd) fun b acc => do
      let (s, v) ← elabBinder b; mkAppM ``Expr.letrec #[s, v, acc]
  | `(expr| (QUOTE $d)) | `(expr| (quote $d)) | `(expr| ,$d) => do
    mkAppM ``Expr.quote #[← LDON.DSL.elabLDON d]
  | `(expr| (EVAL $e $(env?)?)) | `(expr| (eval $e $(env?)?)) => do
    let env := ← match env? with
      | some env? => elabExpr env?
      | none => return mkConst ``Expr.nil
    mkAppM ``Expr.eval #[← elabExpr e, env]
  | `(expr| ()) => return mkConst ``Expr.nil
  | `(expr| ($e:expr $es:expr*)) => do
    if es.size == 0 then
      mkAppM ``Expr.app₀ #[← elabExpr e]
    else
      es.foldlM (init := ← elabExpr e) fun acc e => do
        mkAppM ``Expr.app #[acc, ← elabExpr e]
  | `(expr| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      mkAppM ``Expr.toExpr #[e]
    else throwUnsupportedSyntax

partial def elabBinder : TSyntax `binder → TermElabM (Lean.Expr × Lean.Expr)
  | `(binder| ($s:ident $v:expr)) => return (mkStrLit s.getId.toString, ← elabExpr v)
  | _ => throwUnsupportedSyntax

end

scoped elab "⟦" e:expr "⟧" : term =>
  elabExpr e

end Expr.DSL

end Lurk
