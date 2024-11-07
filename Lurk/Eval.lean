import Lurk.ExprUtils
import Lurk.ExprLDON
import Lurk.Scalar
import Batteries.Data.RBMap

namespace Lurk

open Scalar

structure EvalState where
  hashState : LDONHashState
  evalCount : Nat
  deriving Inhabited

mutual

inductive EnvImg
  | mk : Bool → Value → EnvImg

inductive Env
  | mk : Lean.RBNode String (fun _ => EnvImg) → Env

-- Does it make sense to extend LDON and use it here instead?
inductive Value where
  | num  : F      → Value
  | u64  : UInt64 → Value
  | char : Char   → Value
  | str  : String → Value
  | sym  : String → Value
  | comm  : Digest → Value
  | «fun» : String → Env → Expr → Value
  | cons : Value  → Value → Value
  deriving Inhabited

end

abbrev Frames := List $ Expr × Env

namespace EvalState

def withHashState (stt : LDONHashState) : EvalState → EvalState
  | .mk _ n => .mk stt n

def withIterCountSucc : EvalState → EvalState
  | .mk stt n => .mk stt n.succ

end EvalState

namespace EnvImg

def recr : EnvImg → Bool
  | .mk recr _ => recr

def value : EnvImg → Value
  | .mk _ value => value

end EnvImg

namespace Value

@[match_pattern] def t   := Value.sym "t"
@[match_pattern] def nil := Value.sym "nil"

section ValueDSL
/- The following metaprogramming layer is merely for testing -/

declare_syntax_cat                        value
scoped syntax ident                     : value
scoped syntax char                      : value
scoped syntax num                       : value
scoped syntax str                       : value
scoped syntax "(" value " . " value ")" : value
scoped syntax "(" value+ ")"            : value

open Lean Meta Elab Term in
partial def elabValue : Lean.TSyntax `value → TermElabM Lean.Expr
  | `(value| $i:ident) => mkAppM ``Value.sym #[mkStrLit i.getId.toString]
  | `(value| $c:char) => do
    mkAppM ``Value.char #[← mkAppM ``Char.ofNat #[mkNatLit c.getChar.val.toNat]]
  | `(value| $n:num) => do
    mkAppM ``Value.num #[← mkAppM ``F.ofNat #[mkNatLit n.getNat]]
  | `(value| $s:str) => do
    mkAppM ``Value.str #[mkStrLit s.getString]
  | `(value| ($v₁:value . $v₂:value)) => do
    mkAppM ``Value.cons #[← elabValue v₁, ← elabValue v₂]
  | `(value| ($vs:value*)) => do
    vs.foldrM (init := mkConst ``Value.nil) fun v acc => do
      mkAppM ``Value.cons #[← elabValue v, acc]
  | _ => throwUnsupportedSyntax

scoped elab "⦃" v:value "⦄" : term =>
  elabValue v

end ValueDSL

partial def telescopeCons (acc : Array Value := #[]) : Value → Array Value × Value
  | cons x y => telescopeCons (acc.push x) y
  | x => (acc, x)

def ofLDON : LDON → Value
  | .num  x => .num  x
  | .u64  x => .u64  x
  | .char x => .char x
  | .str  x => .str  x
  | .sym  x => .sym  x
  | .cons x y => .cons (ofLDON x) (ofLDON y)

def ofAtom : Atom → Value
  | .t      => .t
  | .nil    => .nil
  | .num  x => .num  x
  | .u64  x => .u64  x
  | .char x => .char x
  | .str  x => .str  x

def toLDON : Value → LDON
  | num x => .num x
  | u64 x => .u64 x
  | char x => .char x
  | str x => .str x
  | sym x => .sym x
  | cons x y => .cons x.toLDON y.toLDON
  | comm _ => panic! "TODO"
  | .fun .. => panic! "TODO"

def depthLE (v : Value) (n : Nat) : Bool :=
  if n == 0 then false else
  match v with
  | .cons x y => let n := n.pred; x.depthLE n && y.depthLE n
  | _ => true

end Value

namespace Env

def find? (s : String) : Env → Option EnvImg
  | mk e => e.find compare s

def insert (s : String) (v : EnvImg) : Env → Env
  | mk e => mk $ e.insert compare s v

def toArray : Env → Array (String × EnvImg)
  | mk e => e.fold (init := #[]) fun acc k v => acc.push (k, v)

def ofArray : Array (String × EnvImg) → Env
  | es => es.foldl (init := .mk .leaf) fun acc (name, img) => acc.insert name img

def toList : Env → List (String × EnvImg)
  | mk e => e.fold (init := []) fun acc k v => (k, v) :: acc

def toRBMap : Env → Batteries.RBMap String EnvImg compare
  | mk e => e.fold (init := default) fun acc k v => acc.insert k v

end Env

partial def Value.toString : Value → String
  | .num x => x.asHex
  | .nil => "nil"
  | .t   => "t"
  | .sym x => s!"|{x}|"
  | .u64 x => s!"{x}u64"
  | .char c => s!"#\\{c}"
  | .str s => s!"\"{s}\""
  | v@(.cons ..) =>
    if v.depthLE 20 then
      match v.telescopeCons with
      | (#[], .nil) => "nil"
      | (vs, v) =>
        let vs := " ".intercalate $ vs.data.map toString
        match v with
        | .nil => "(" ++ vs ++ ")"
        | _ => s!"({vs} . {v.toString})"
    else "( ⋯ )"
  | .comm c => s!"<comm {c.asHex}>"
  | .fun n _ b =>
    let (ns, b) := b.telescopeLam #[n]
    if b.depthLE 20 then s!"<fun ({" ".intercalate ns.data}) {b}>"
    else s!"<fun ({" ".intercalate ns.data}) ⋯>"

instance : ToString Value where
  toString := Value.toString

instance : Inhabited Env := ⟨.mk .leaf⟩

abbrev EvalM := ReaderT Frames $ EStateM (String × Frames) EvalState

def Frames.pprint (frames : Frames) (n : Nat) : String :=
  let rec aux (acc : String) : List (Expr × Env) → String
    | [] => acc
    | f :: fs => aux s!"{acc}\n{frameToString f}" fs
  aux default (frames.take n) |>.trimLeft
where
  frameToString : Expr × Env → String
    | (e, env) =>
      let fVars := e.getFreeVars
      -- considering relevant variables, only
      let env := env.toRBMap |>.filter fun s _ => fVars.contains s
      let init := "\n########################################################\n"
        ++ e.toString ++ "\n"
        ++ "--------------------------------------------------------"
      env.foldl (init := init) fun acc s ⟨_, v⟩ => s!"{acc}\n{s} ⇒ {v}"

mutual

partial def EnvImg.beq : EnvImg → EnvImg → Bool
  | .mk r₁ v₁, .mk r₂ v₂ => r₁ == r₂ && v₁.beq v₂

partial def Env.beq (e₁ e₂ : Env) : Bool :=
  let e := e₁.toList.zip e₂.toList
  e.all fun ((n₁, v₁), (n₂, v₂)) => n₁ == n₂ && v₁.beq v₂

partial def Value.beq : Value → Value → Bool
  | .num    x, .num    y => x == y
  | .u64    x, .u64    y => x == y
  | .char   x, .char   y => x == y
  | .str    x, .str    y => x == y
  | .sym    x, .sym    y => x == y
  | .cons x y, .cons w z => x.beq w && y.beq z
  | .comm c₁,  .comm c₂  => c₁ == c₂
  | .fun ns₁ env₁ e₁, .fun ns₂ env₂ e₂ => ns₁ == ns₂ && env₁.beq env₂ && e₁ == e₂
  | _, _ => false

end

instance : BEq Value := ⟨Value.beq⟩

instance : Coe Bool Value where coe
  | true  => .t
  | false => .nil

instance : Coe Char Value := ⟨.char⟩

instance : Coe String Value := ⟨.str⟩

instance : OfNat Value n where
  ofNat := .num (.ofNat n)

def error (e : Expr) (msg : String) : EvalM α := do
  throw (s!"Error when evaluating {e}:\n{msg}", (← read))

def numAdd (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x + y)
  | .u64 x, .u64 y => return .u64 (x + y)
  | .num x, .u64 y => return .num (x + (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) + y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numSub (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x - y)
  | .u64 x, .u64 y => return .u64 (x - y)
  | .num x, .u64 y => return .num (x - (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) - y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMul (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x * y)
  | .u64 x, .u64 y => return .u64 (x * y)
  | .num x, .u64 y => return .num (x * (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) * y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numDiv (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return .num (x / y)
  | .u64 x, .u64 y => return .u64 (x / y)
  | .num x, .u64 y => return .num (x / (.ofNat y.toNat))
  | .u64 x, .num y => return .num ((.ofNat x.toNat) / y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numMod (e : Expr) : Value → Value → EvalM Value
  | .u64 x, .u64 y => return .u64 (x % y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numEq (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return decide (x == y)
  | .u64 x, .u64 y => return decide (x == y)
  | .num x, .u64 y => return decide (x == (.ofNat y.toNat))
  | .u64 x, .num y => return decide ((.ofNat x.toNat) == y)
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLt (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.lt x y
  | .u64 x, .u64 y => return decide (x < y)
  | .num x, .u64 y => return F.lt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.lt (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGt (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.gt x y
  | .u64 x, .u64 y => return decide (x > y)
  | .num x, .u64 y => return F.gt x (.ofNat y.toNat)
  | .u64 x, .num y => return F.gt (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numLe (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.le x y
  | .u64 x, .u64 y => return decide (x <= y)
  | .num x, .u64 y => return F.le x (.ofNat y.toNat)
  | .u64 x, .num y => return F.le (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def numGe (e : Expr) : Value → Value → EvalM Value
  | .num x, .num y => return F.ge x y
  | .u64 x, .u64 y => return decide (x >= y)
  | .num x, .u64 y => return F.ge x (.ofNat y.toNat)
  | .u64 x, .num y => return F.ge (.ofNat x.toNat) y
  | v₁, v₂ => error e s!"expected numeric values, got\n  {v₁} and {v₂}"

def hideLDON (secret : Digest) (ldon : LDON) : EvalM Value := do
  let (comm, hashState) := ldon.hide secret (← get).hashState
  modifyGet fun stt => (.comm comm, stt.withHashState hashState)

def Expr.evalOp₁ (e : Expr) : Op₁ → Value → EvalM Value
  | .atom, .cons .. => return .nil
  | .atom, _ => return .t
  | .car, .nil => return .nil
  | .car, .cons car _ => return car
  | .car, .str ⟨[]⟩ => return .nil
  | .car, .str ⟨h::_⟩ => return .char h
  | .car, v => error e s!"expected cons value, got\n  {v}"
  | .cdr, .cons _ cdr => return cdr
  | .cdr, .str ⟨[]⟩ => return .str ""
  | .cdr, .str ⟨_::cs⟩ => return .str ⟨cs⟩
  | .cdr, v => error e s!"expected cons value, got\n  {v}"
  | .emit, v => dbg_trace v; return v
  | .commit, v => hideLDON .zero v.toLDON
  | .comm, .num n => return .comm <| Digest.ofSmallNat n.val
  | .comm, v => error e s!"expected a num, got\n  {v}"
  | .open, .num f => do
    match (← get).hashState.store.open (.ofSmallNat f.val) with
    | .error err => error e err
    | .ok ldon => return .ofLDON ldon
  | .open, .comm d =>  do
    match (← get).hashState.store.open d with
    | .error err => error e err
    | .ok ldon => return .ofLDON ldon
  | .open, v => error e s!"expected a num or comm, got\n  {v}"
  | .num, x@(.num _) => return x
  | .num, .u64 n => return .num (.ofNat n.toNat)
  | .num, .char c => return .num (.ofNat c.toNat)
  | .num, .comm c => return .num <| .ofNat c.toNatAsBytes
  | .num, v => error e s!"expected char, num, u64, or comm value, got\n  {v}"
  | .u64, x@(.u64 _) => return x
  | .u64, .num n => return .u64 (.ofNat n.val)
  | .u64, v => error e s!"expected num or u64, got\n  {v}"
  | .char, .char c => return .char c
  | .char, .num ⟨n, _⟩ =>
    let charVal := n.toUInt32
    if h : isValidChar charVal then return .char ⟨charVal, h⟩
    else error e s!"{charVal} is not a valid char value"
  | .char, v => error e s!"expected char or num value, got\n  {v}"

def Expr.evalOp₂ (e : Expr) : Op₂ → Value → Value → EvalM Value
  | .cons, v₁, v₂ => return .cons v₁ v₂
  | .strcons, .char c, .str s => return .str ⟨c :: s.data⟩
  | .strcons, v₁, v₂ => error e s!"expected char and string value, got {v₁} and {v₂}"
  | .add, v₁, v₂ => numAdd e v₁ v₂
  | .sub, v₁, v₂ => numSub e v₁ v₂
  | .mul, v₁, v₂ => numMul e v₁ v₂
  | .div, v₁, v₂ => numDiv e v₁ v₂
  | .mod, v₁, v₂ => numMod e v₁ v₂
  | .numEq, v₁, v₂ => numEq e v₁ v₂
  | .lt, v₁, v₂ => numLt e v₁ v₂
  | .gt, v₁, v₂ => numGt e v₁ v₂
  | .le, v₁, v₂ => numLe e v₁ v₂
  | .ge, v₁, v₂ => numGe e v₁ v₂
  | .eq, v₁, v₂ => return v₁.beq v₂
  | .hide, .num f, v => hideLDON (.ofSmallNat f.val) v.toLDON
  | .hide, v, _ => error e s!"expected a num, got {v}"


def Value.toEnv (env? : Value) (e : Expr) : EvalM Env :=
  match env?.toLDON.telescopeCons with
  | (binds, .nil) => do
    let binds := ← binds.mapM fun bind => match bind with
      | .cons (.sym name) v => return (name, EnvImg.mk false (Value.ofLDON v))
      | x => do error e s!"expected a binding `(sym . expr)`, got {x}"
    return .ofArray binds
  | (_, tail) => error e s!"expected a `nil` terminated list, got {tail}"

def withFrame (fr : Expr × Env) : EvalM α → EvalM α :=
  withReader (fr :: ·)

mutual

partial def Expr.evalApp₀ (fn : Expr) (env : Env) : EvalM Value := do
  match fn with
  | .sym n =>
    let some ⟨r, v⟩ := env.find? n
      | error fn s!"{n} not found"
    let .fun "_" fnEnv body := v
      | error fn s!"error evaluating\n{fn}\ninvalid 0-arity app"
    let fnEnv := if !r then fnEnv else fnEnv.insert n ⟨r, v⟩
    body.evalM fnEnv
  | fn =>
    let .fun "_" fnEnv body ← fn.evalM env
      | error fn s!"error evaluating\n{fn}\ninvalid 0-arity app"
    body.evalM fnEnv

partial def Expr.evalApp (fn : Expr) (arg : Expr) (env : Env) : EvalM Value := do
  match fn with
  | .sym n =>
    let some ⟨r, v⟩ := env.find? n
      | error fn s!"{n} not found"
    match v with
    | .fun "_" .. => error fn s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun argname fnEnv body =>
      let fnEnv := if !r then fnEnv else fnEnv.insert n ⟨r, v⟩
      let fnEnv := fnEnv.insert argname ⟨false, ← arg.evalM env⟩
      body.evalM fnEnv
    | x => error fn s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"
  | fn =>
    match ← fn.evalM env with
    | .fun "_" .. => error fn s!"error evaluating\n{fn}\ncannot apply argument to 0-arg lambda"
    | .fun argname fnEnv body =>
      let fnEnv := fnEnv.insert argname ⟨false, ← arg.evalM env⟩
      body.evalM fnEnv
    | x => error fn s!"error evaluating\n{fn}\nlambda was expected, got\n  {x}"

partial def Expr.evalM (e : Expr) (env : Env) : EvalM Value := withFrame (e, env) do
  modify .withIterCountSucc
  match e with
  | .atom a => return .ofAtom a
  | .sym n => match env.find? n with
    | some ⟨r, v⟩ => match v with
      | .fun name env body =>
        let env := if !r then env else env.insert n ⟨r, v⟩
        return .fun name env body
      | v => return v
    | none => error e s!"{n} not found"
  | .env =>
    return env.toArray.foldr (init := .nil)
      fun (k, v) acc => .cons (.cons (.sym k) v.value) acc
  | .begin x .nil => x.evalM env
  | .begin x y => do discard $ x.evalM env; y.evalM env
  | .if x y z => do match ← x.evalM env with
    | .nil => z.evalM env
    | _ => y.evalM env
  | .app₀ fn => fn.evalApp₀ env
  | .app fn arg => fn.evalApp arg env
  | x@(.op₁ op e) => do evalOp₁ x op (← e.evalM env)
  | x@(.op₂ op e₁ e₂) => do evalOp₂ x op (← e₁.evalM env) (← e₂.evalM env)
  | .lambda s e => return .fun s env e
  | .let    s v b => do b.evalM (env.insert s ⟨false, ← v.evalM env⟩)
  | .letrec s v b => do b.evalM (env.insert s ⟨true, ← v.evalM env⟩)
  | .quote d => return .ofLDON d
  | .eval e .nil => do
    match (← e.evalM env).toLDON.toExpr with
    | .error err => error e err
    | .ok e => e.evalM default
  | .eval e env? => do
    match (← e.evalM env).toLDON.toExpr with
    | .error err => error e err
    | .ok e =>
      let env? ← env?.evalM env
      e.evalM (← env?.toEnv e)

end

def Expr.evaluate (e : Expr) (store : Scalar.Store := default) :
    Except (String × Frames) (Value × Nat) :=
  match EStateM.run (ReaderT.run (e.evalM default) default)
    ⟨⟨store, default, default⟩, 0⟩ with
  | .ok v stt => .ok (v, stt.evalCount)
  | .error err _ => .error err

def Expr.evaluate' (e : Expr) (store : Scalar.Store := default) :
    Except String Value :=
  match EStateM.run (ReaderT.run (e.evalM default) default)
    ⟨⟨store, default, default⟩, 0⟩ with
  | .ok v _ => .ok v
  | .error err _ => .error err.1

end Lurk
