import Lurk.LDON
import Lurk.Expr

namespace Lurk

def Atom.toLDON : Atom → LDON
  | .nil => .nil
  | .t   => .t
  | .num x => .num x
  | .u64 x => .u64 x
  | .str x => .str x
  | .char x => .char x

namespace Expr

open LDON Macro

partial def toLDON : Expr → LDON
  | .atom a => a.toLDON
  | .sym s => .sym s
  | .env => ~[.sym "current-env"]
  | .op₁ o e => ~[.sym o.toString, e.toLDON]
  | .op₂ o e₁ e₂ => ~[.sym o.toString, e₁.toLDON, e₂.toLDON]
  | e@(.begin ..) =>
    let (es, e) := e.telescopeBegin
    .cons (.sym "begin") $ es.foldr (.cons ·.toLDON ·) e.toLDON
  | .if a b c => .cons (.sym "if") $ .cons a.toLDON $ .cons b.toLDON $ .cons c.toLDON .nil
  | .app₀ e => ~[e.toLDON]
  | .app f a => ~[f.toLDON, a.toLDON]
  | .lambda s e =>
    let (ss, b) := e.telescopeLam #[s]
    .cons (.sym "lambda") $
      .cons (ss.foldr (fun s acc => .cons (.sym s) acc) .nil) $ .cons b.toLDON .nil
  | .let s v b =>
    let (bs, b) := b.telescopeLet #[(s, v)]
    .cons (.sym "let") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .letrec s v b =>
    let (bs, b) := b.telescopeLetrec #[(s, v)]
    .cons (.sym "letrec") $
      .cons (bs.foldr (fun (s, v) acc =>
          .cons (.cons (.sym s) (.cons v.toLDON .nil)) acc) .nil) $
        .cons b.toLDON .nil
  | .quote d => ~[.sym "quote", d]
  | .eval e env? =>
    if env? == .nil then
      ~[.sym "eval", e.toLDON]
    else
      ~[.sym "eval", e.toLDON, env?.toLDON]

def symOfString : String → Expr
  | "nil" => .nil
  | "t"   => .t
  | x     => .sym x

end Expr

def mkOp₁ (op₁ : String) : Expr → Expr := match op₁ with
  | "atom"   => .op₁ .atom
  | "car"    => .op₁ .car
  | "cdr"    => .op₁ .cdr
  | "emit"   => .op₁ .emit
  | "commit" => .op₁ .commit
  | "comm"   => .op₁ .comm
  | "open"   => .op₁ .open
  | "num"    => .op₁ .num
  | "u64"    => .op₁ .u64
  | "char"   => .op₁ .char
  | x => fun y => .app (.symOfString x) y

def mkOp₂ (op₂ : String) : Expr → Expr → Expr := match op₂ with
  | "cons"    => .op₂ .cons
  | "strcons" => .op₂ .strcons
  | "+"       => .op₂ .add
  | "-"       => .op₂ .sub
  | "*"       => .op₂ .mul
  | "/"       => .op₂ .div
  | "="       => .op₂ .numEq
  | "<"       => .op₂ .lt
  | ">"       => .op₂ .gt
  | "<="      => .op₂ .le
  | ">="      => .op₂ .ge
  | "eq"      => .op₂ .eq
  | "hide"    => .op₂ .hide
  | x => fun y z => .app (.app (.symOfString x) y) z

namespace LDON

def asArgs : LDON → Except String (List String)
  | .nil => return []
  | .cons (.sym x) xs => return x :: (← xs.asArgs)
  | x => throw s!"expected list of symbols but got {x}"

open Macro

def asBindings : LDON → Except String (List (String × LDON))
  | .nil => return []
  | .cons ~[.sym x, y] xs => return (x, y) :: (← xs.asBindings)
  | x => throw s!"expected list of (symbol, body) pairs but got {x}"

partial def toExpr : LDON → Except String Expr
  -- trivial cases
  | .num  n  => return .atom $ .num (.ofNat n)
  | .u64  n  => return .atom $ .u64 n
  | .char c  => return .atom $ .char c
  | .str  s  => return .atom $ .str s
  | ~[.sym "current-env"] => return .env
  | .sym s  => return .symOfString s
  -- `begin` is a sequence of expressions
  | .cons (.sym "begin") tail => match tail.telescopeCons with
    | (xs, .nil) =>
      xs.foldrM (init := .nil) fun x acc => do
        pure $ .begin (← x.toExpr) acc
    | x => throw s!"expected a list terminating with `nil` but got {x}"
  -- `if` is a sequence of (up to) three expressions
  | ~[.sym "if"] => return .if .nil .nil .nil
  | ~[.sym "if", x] => return .if (← x.toExpr) .nil .nil
  | ~[.sym "if", x, y] => return .if (← x.toExpr) (← y.toExpr) .nil
  | ~[.sym "if", x, y, z] => return .if (← x.toExpr) (← y.toExpr) (← z.toExpr)
  -- `lambda` requires a gradual consumption of a symbol
  | ~[.sym "lambda", args, body] => do
    let args ← args.asArgs
    if args.isEmpty then
      return .lambda "_" (← body.toExpr)
    else
      return args.foldr (init := ← body.toExpr) fun arg acc => .lambda arg acc
  -- let and letrec are in the same case
  | ~[.sym "let", bindings, body] => do
    let bindings ← bindings.asBindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .let n e acc
  | ~[.sym "letrec", bindings, body] => do
    let bindings ← bindings.asBindings
    let bindings ← bindings.mapM fun (x, y) => return (x, ← y.toExpr)
    return bindings.foldr (init := ← body.toExpr)
      fun (n, e) acc => .letrec n e acc
  -- quoting consumes the expression as-is
  | ~[.sym "quote", x] => return .quote x
  | ~[.sym "eval", x] => return .eval (← x.toExpr) .nil
  | ~[.sym "eval", x, y] => return .eval (← x.toExpr) (← y.toExpr)
  -- binary operators
  | ~[.sym op₂, x, y] => return mkOp₂ op₂ (← x.toExpr) (← y.toExpr)
  -- unary operators
  | ~[.sym op₁, x] => return mkOp₁ op₁ (← x.toExpr)
  -- everything else is just an `app`
  | cons fn args => match args.telescopeCons with
    | (args, nil) =>
      if args.isEmpty then
        return .app₀ (← fn.toExpr)
      else do
        args.foldlM (init := ← fn.toExpr) fun acc arg => do
          pure $ .app acc (← arg.toExpr)
    | x => throw s!"expected a list terminating with `nil` but got {x}"

end Lurk.LDON
