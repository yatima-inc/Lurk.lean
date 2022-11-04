import Lean
import Lurk.Syntax.AST

namespace Lurk.Syntax
open Lean Elab Meta Term

namespace DSL

declare_syntax_cat    sym
scoped syntax ident : sym
scoped syntax "+"   : sym
scoped syntax "*"   : sym
scoped syntax "-"   : sym
scoped syntax "/"   : sym
scoped syntax "="   : sym
scoped syntax "<"   : sym
scoped syntax ">"   : sym
scoped syntax "<="  : sym
scoped syntax ">="  : sym
-- these can't be simple idents because they'd clash with Lean's syntax
scoped syntax "if"  : sym
scoped syntax "let" : sym
-- escaping symbols
scoped syntax "|" sym "|" : sym

partial def elabSym : TSyntax `sym → TermElabM Lean.Expr
  | `(sym| $i:ident ) => mkAppM ``AST.sym #[mkStrLit i.getId.toString.toUpper]
  | `(sym| +)  => mkAppM ``AST.sym #[mkStrLit "+"]
  | `(sym| *)  => mkAppM ``AST.sym #[mkStrLit "*"]
  | `(sym| -)  => mkAppM ``AST.sym #[mkStrLit "-"]
  | `(sym| /)  => mkAppM ``AST.sym #[mkStrLit "/"]
  | `(sym| =)  => mkAppM ``AST.sym #[mkStrLit "="]
  | `(sym| <)  => mkAppM ``AST.sym #[mkStrLit "<"]
  | `(sym| >)  => mkAppM ``AST.sym #[mkStrLit ">"]
  | `(sym| <=) => mkAppM ``AST.sym #[mkStrLit "<="]
  | `(sym| >=) => mkAppM ``AST.sym #[mkStrLit ">="]
  | `(sym| if) => mkAppM ``AST.sym #[mkStrLit "IF"]
  | `(sym| let) => mkAppM ``AST.sym #[mkStrLit "LET"]
  | `(sym| |$i:ident|) => mkAppM ``AST.sym #[mkStrLit i.getId.toString]
  | `(sym| |if|) => mkAppM ``AST.sym #[mkStrLit "if"]
  | `(sym| |let|) => mkAppM ``AST.sym #[mkStrLit "let"]
  | `(sym| |$s:sym|) => elabSym s
  | _ => throwUnsupportedSyntax

declare_syntax_cat                     ast
scoped syntax num                    : ast
scoped syntax char                   : ast
scoped syntax str                    : ast
scoped syntax sym                    : ast
scoped syntax "(" ast* ")"           : ast
scoped syntax "(" ast+ " . " ast ")" : ast
scoped syntax "," ast                : ast -- quoting
-- symbols separated by a dash (only handles one dash)
scoped syntax sym noWs "-" noWs sym  : ast
scoped syntax sym noWs "-" noWs num  : ast

def mergeSymSym : AST → AST → AST
  | .sym a, .sym b => .sym s!"{a}-{b}"
  | x, _ => x

def mergeSymNat : AST → Nat → AST
  | .sym a, n => .sym s!"{a}-{n}"
  | x, _ => x

mutual

partial def elabASTCons (xs : Array $ TSyntax `ast) (init : Expr) : TermElabM Expr :=
  xs.foldrM (init := init) fun e acc => do mkAppM ``AST.cons #[← elabAST e, acc]

partial def elabAST : TSyntax `ast → TermElabM Expr
  | `(ast| $n:num) => mkAppM ``AST.num #[mkNatLit n.getNat]
  | `(ast| $c:char) => do
    mkAppM ``AST.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(ast| $s:str) => mkAppM ``AST.str #[mkStrLit s.getString]
  | `(ast| $s:sym) => elabSym s
  | `(ast| $a:sym-$b:sym) => do mkAppM ``mergeSymSym #[← elabSym a, ← elabSym b]
  | `(ast| $a:sym-$n:num) => do mkAppM ``mergeSymNat #[← elabSym a, mkNatLit n.getNat]
  | `(ast| ()) => mkAppM ``AST.sym #[mkStrLit "NIL"]
  | `(ast| ($xs*)) => elabASTCons xs (mkConst ``AST.nil)
  | `(ast| ($x . $y)) => do mkAppM ``AST.cons #[← elabAST x, ← elabAST y]
  | `(ast| ($xs* . $x)) => do elabASTCons xs (← elabAST x)
  | `(ast| ,$x:ast) => do mkAppM ``AST.mkQuote #[← elabAST x]
  | `(ast| $x) => do
    if x.raw.isAntiquot then
      let stx := x.raw.getAntiquotTerm
      let e ← elabTerm stx none
      let e ← whnf e
      trace[debug] e
      mkAppM ``ToAST.toAST #[e]
    else throwUnsupportedSyntax

end

elab "⟦ " x:ast " ⟧" : term =>
  elabAST x

end DSL

end Lurk.Syntax
