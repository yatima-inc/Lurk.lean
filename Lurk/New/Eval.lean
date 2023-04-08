import Std.Data.RBMap
import Lurk.New.ExprPtrArith
import Lurk.New.Store

open Std (RBMap)
open Store

def car (exprPtr : ExprPtr) : StoreM ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons x _ => pure x
  | _ => if ← isNil exprPtr then pure exprPtr else throw "car failed"

def cdr (exprPtr : ExprPtr) : StoreM ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons _ x => pure x
  | _ => if ← isNil exprPtr then pure exprPtr else throw "cdr failed"

def cadr (exprPtr : ExprPtr) : StoreM $ ExprPtr × ExprPtr := do
  match ← getExprPtrImg exprPtr with
  | .cons x y => pure (x, y)
  | _ => if ← isNil exprPtr then pure (exprPtr, exprPtr) else throw "cadr failed"

def uncons (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr) := do
  match ← getExprPtrImg exprPtr with
  | .cons a b => pure (a, b)
  | _ => throw "uncons failed"

def unfold1 (exprPtr : ExprPtr) : StoreM ExprPtr := do
  let (car, cdr) ← uncons exprPtr
  if ← isNil cdr then return car
  throw "unfold1 failed"

def unfold2 (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← uncons exprPtr
  let (car₂, cdr) ← uncons cdr
  if ← isNil cdr then return (car₁, car₂)
  throw "unfold2 failed"

def unfold3 (exprPtr : ExprPtr) : StoreM (ExprPtr × ExprPtr × ExprPtr) := do
  let (car₁, cdr) ← uncons exprPtr
  let (car₂, cdr) ← uncons cdr
  let (car₃, cdr) ← uncons cdr
  if ← isNil cdr then return (car₁, car₂, car₃)
  throw "unfold3 failed"

def insert (envPtr symPtr valPtr : ExprPtr) : StoreM ExprPtr := do
  let pair ← addToExprStore
    ⟨.cons, hash4 symPtr.tag.toF symPtr.val valPtr.tag.toF valPtr.val⟩
    (.cons symPtr valPtr)
  addToExprStore
    ⟨.cons, hash4 pair.tag.toF pair.val envPtr.tag.toF envPtr.val⟩
    (.cons pair envPtr)

-- eliminate this linear cost
partial def find? (envPtr symPtr : ExprPtr) : StoreM (Option ExprPtr) := do
  if ← isNil envPtr then return none
  let (head, tail) ← uncons envPtr
  let (symPtr', valPtr) ← cadr head
  if symPtr' == symPtr then return some valPtr
  find? tail symPtr

def getCont0 (contPtr : ContPtr) : StoreM ContPtr := do
  match (← get).contData.find? contPtr with
  | some $ .cont0 a => return a
  | _ => throw "getCont0 failed"

def getCont1 (contPtr : ContPtr) : StoreM (ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont1 a b => return (a, b)
  | _ => throw "getCont1 failed"

def getCont2 (contPtr : ContPtr) : StoreM (ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont2 a b c => return (a, b, c)
  | _ => throw "getCont2 failed"

def getCont3 (contPtr : ContPtr) : StoreM (ExprPtr × ExprPtr × ExprPtr × ContPtr) := do
  match (← get).contData.find? contPtr with
  | some $ .cont3 a b c d => return (a, b, c, d)
  | _ => throw "getCont3 failed"

@[inline] def mkFunPtr (argsSymsPtr funEnvPtr bodyPtr : ExprPtr) : StoreM ExprPtr :=
  addToExprStore
    ⟨.fun, hash6 argsSymsPtr.tag.toF argsSymsPtr.val funEnvPtr.tag.toF funEnvPtr.val
      bodyPtr.tag.toF bodyPtr.val⟩
    (.fun argsSymsPtr funEnvPtr bodyPtr)

structure State where
  expr : ExprPtr
  env  : ExprPtr
  cont : ContPtr
  deriving BEq

instance : ToString State where
  toString x := s!"⟨{x.expr}, {x.env}, {x.cont}⟩"

abbrev StepInto := ExprPtr × ContPtr → StoreM State

def intoUnOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do
    let contPtr' ← addToContStore
      ⟨tag, hash2 contPtr.tag.toF contPtr.val⟩
      (.cont0 contPtr)
    return ⟨← unfold1 tailPtr, envPtr, contPtr'⟩

def intoBinOp (tag : ContTag) (tailPtr : ExprPtr) : StepInto :=
  fun (envPtr, contPtr) => do
    let (x, y) ← unfold2 tailPtr
    let contPtr' ← addToContStore
      ⟨tag, hash4 y.tag.toF y.val contPtr.tag.toF contPtr.val⟩
      (.cont1 y contPtr)
    return ⟨x, envPtr, contPtr'⟩

def intoApp (fnPtr argsPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let contPtr' ← addToContStore
    ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
    (.cont1 argsPtr contPtr)
  return ⟨fnPtr, envPtr, contPtr'⟩

def intoIf (tailPtr : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let (propPtr, tailPtr) ← cadr tailPtr
  let (truePtr, tailPtr) ← cadr tailPtr
  let (falsePtr, tailPtr) ← cadr tailPtr
  if ← isNotNil tailPtr then throw "To many arguments for `if`"
  let contPtr' ← addToContStore
    ⟨.if, hash6 truePtr.tag.toF truePtr.val falsePtr.tag.toF falsePtr.val
      contPtr.tag.toF contPtr.val⟩
    (.cont2 truePtr falsePtr contPtr)
  return ⟨propPtr, envPtr, contPtr'⟩

def intoBody (bodyPtr envPtr₀ : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  let contPtr' ← addToContStore
    ⟨.body, hash4 envPtr₀.tag.toF envPtr₀.val contPtr.tag.toF contPtr.val⟩
    (.cont1 envPtr₀ contPtr)
  return ⟨bodyPtr, envPtr, contPtr'⟩

def intoLet (bindsPtr bodyPtr envPtr₀ : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  if ← isNil bindsPtr then intoBody bodyPtr envPtr₀ (envPtr, contPtr) else
  let bindPtr ← car bindsPtr
  let (_, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.let, hash8 bindsPtr.tag.toF bindsPtr.val bodyPtr.tag.toF bodyPtr.val
      envPtr₀.tag.toF envPtr₀.val contPtr.tag.toF contPtr.val⟩
    (.cont3 bindsPtr bodyPtr envPtr₀ contPtr)
  return ⟨bindExprPtr, envPtr, contPtr'⟩

def intoLetrec (bindsPtr bodyPtr envPtr₀ : ExprPtr) : StepInto := fun (envPtr, contPtr) => do
  if ← isNil bindsPtr then intoBody bodyPtr envPtr₀ (envPtr, contPtr) else
  let bindPtr ← car bindsPtr
  let (bindSymPtr, bindExprPtr) ← unfold2 bindPtr
  let contPtr' ← addToContStore
    ⟨.letrec, hash8 bindsPtr.tag.toF bindsPtr.val bodyPtr.tag.toF bodyPtr.val
      envPtr₀.tag.toF envPtr₀.val contPtr.tag.toF contPtr.val⟩
    (.cont3 bindsPtr bodyPtr envPtr₀ contPtr)
  let thunkPtr ← addToExprStore
    ⟨.thunk, hash2 bindExprPtr.tag.toF bindExprPtr.val⟩
    (.thunk bindExprPtr)
  let envPtr' ← insert envPtr bindSymPtr thunkPtr
  return ⟨bindExprPtr, envPtr', contPtr'⟩

def mkRet (stt : State) : StoreM State := do
  let contPtr := stt.cont
  let contPtr' ← addToContStore
    ⟨.ret, hash2 contPtr.tag.toF contPtr.val⟩
    (.cont0 contPtr)
  return { stt with cont := contPtr' }

def State.finishUnOp (stt : State) : UnOp → StoreM State
  | .car => return ⟨← car stt.expr, stt.env, ← getCont0 stt.cont⟩

def State.finishBinOp (stt : State) (op : BinOp) : StoreM State := do
  let ((x, contPtr), y) := (← getCont1 stt.cont, stt.expr)
  match op with
  | .add => return ⟨← x.add y, stt.env, contPtr⟩
  | .numEq => return ⟨← boolToExprPtr $ ← x.numEq y, stt.env, contPtr⟩

def State.continue (stt : State) : StoreM State := do
  match stt.cont.tag with
  | .done => return stt
  | .unOp op => stt.finishUnOp op
  | .binOp₁ op =>
    let x := stt.expr
    let (y, contPtr) ← getCont1 stt.cont
    let contPtr' ← addToContStore
      ⟨.binOp₂ op, hash4 x.tag.toF x.val contPtr.tag.toF contPtr.val⟩
      (.cont1 x contPtr)
    return ⟨y, stt.env, contPtr'⟩
  | .binOp₂ op => stt.finishBinOp op
  | .appFn =>
    let fnPtr := stt.expr
    let (argsPtr, contPtr) ← getCont1 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr bodyPtr =>
      match ← isNil argsSymsPtr, ← isNil argsPtr with
      | true,  true  => intoBody bodyPtr stt.env (funEnvPtr, contPtr) -- fulfilled
      | false, true  => return ⟨fnPtr, stt.env, contPtr⟩ -- still missing args
      | true,  false => throw "Too many arguments"
      | false, false => -- currying
        let (argPtr, argsPtr) ← uncons argsPtr
        let contPtr' ← addToContStore
          ⟨.appArg, hash6 fnPtr.tag.toF fnPtr.val argsPtr.tag.toF argsPtr.val
            contPtr.tag.toF contPtr.val⟩
          (.cont2 fnPtr argsPtr contPtr)
        return ⟨argPtr, stt.env, contPtr'⟩
    | _ => throw s!"Error evaluating app function. Head function expected"
  | .appArg =>
    let (fnPtr, argsPtr, contPtr) ← getCont2 stt.cont
    match ← getExprPtrImg fnPtr with
    | .fun argsSymsPtr funEnvPtr bodyPtr =>
      let (argSymPtr, argsSymsPtr) ← uncons argsSymsPtr
      let funEnvPtr ← insert funEnvPtr argSymPtr stt.expr
      let funPtr ← mkFunPtr argsSymsPtr funEnvPtr bodyPtr
      let contPtr' ← addToContStore
        ⟨.appFn, hash4 argsPtr.tag.toF argsPtr.val contPtr.tag.toF contPtr.val⟩
        (.cont1 argsPtr contPtr)
      return ⟨funPtr, stt.env, contPtr'⟩
    | _ => throw "Error applying app argument. Head function expected"
  | .if =>
    let (truePtr, falsePtr, contPtr) ← getCont2 stt.cont
    if ← isNil stt.expr then mkRet ⟨falsePtr, stt.env, contPtr⟩
    else mkRet ⟨truePtr, stt.env, contPtr⟩
  | .let =>
    let (bindsPtr, bodyPtr, envPtr₀, contPtr) ← getCont3 stt.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert stt.env bindSymPtr stt.expr
    intoLet bindsPtr' bodyPtr envPtr₀ (envPtr, contPtr)
  | .letrec =>
    let (bindsPtr, bodyPtr, envPtr₀, contPtr) ← getCont3 stt.cont
    let (bindPtr, bindsPtr') ← uncons bindsPtr
    let (bindSymPtr, _) ← unfold2 bindPtr
    let envPtr ← insert stt.env bindSymPtr stt.expr
    intoLetrec bindsPtr' bodyPtr envPtr₀ (envPtr, contPtr)
  | .body =>
    let (envPtr₀, contPtr) ← getCont1 stt.cont
    return ⟨stt.expr, envPtr₀, contPtr⟩
  | .ret => return { stt with cont := ← getCont0 stt.cont }

@[inline] def State.stepIntoParams (stt : State) : ExprPtr × ContPtr :=
  (stt.env, stt.cont)

def State.step (stt : State) : StoreM State := do
  match stt.expr.tag with
  | .num | .u64 | .char | .str | .comm | .fun => stt.continue
  | .sym =>
    let symPtr := stt.expr
    match ← getSym symPtr with
    | .nil | .t => stt.continue
    | sym => match ← find? stt.env symPtr with
      | some valPtr =>
        if valPtr.tag != .thunk then State.continue { stt with expr := valPtr }
        else return stt
      | none => throw s!"{sym} not found"
  | .thunk =>
    let .thunk expr ← getExprPtrImg stt.expr
      | throw "Expected thunk. Malformed store"
    return ⟨expr, stt.env, stt.cont⟩
  | .cons =>
    let .cons head tail ← getExprPtrImg stt.expr
      | throw "Expected cons. Malformed store"
    if head.tag == .sym then match ← getSym head with
      | .ofString "car" => intoUnOp (.unOp .car) tail stt.stepIntoParams
      | .ofString "+" => intoBinOp (.binOp₁ .add) tail stt.stepIntoParams
      | .ofString "=" => intoBinOp (.binOp₁ .numEq) tail stt.stepIntoParams
      | .ofString "lambda" =>
        let (argsSymsPtr, bodyPtr) ← unfold2 tail
        let envPtr := stt.env
        let funPtr ← mkFunPtr argsSymsPtr envPtr bodyPtr
        return ⟨funPtr, envPtr, stt.cont⟩
      | .ofString "if" => intoIf tail stt.stepIntoParams
      | .ofString "let" =>
        let (bindsPtr, bodyPtr) ← unfold2 tail
        intoLet bindsPtr bodyPtr stt.env stt.stepIntoParams
      | .ofString "letrec" =>
        let (bindsPtr, bodyPtr) ← unfold2 tail
        intoLetrec bindsPtr bodyPtr stt.env stt.stepIntoParams
      | _ => intoApp head tail stt.stepIntoParams
    else intoApp head tail stt.stepIntoParams

def State.eval (stt : State) : StoreM $ State × Array State := do
  let mut stt' ← stt.step
  let mut stts := #[stt, stt']
  dbg_trace stt
  dbg_trace stt'
  while stt'.cont.tag != .done do
    stt' ← stt'.step
    dbg_trace stt'
    stts := stts.push stt'
  return (stt', stts)

def LDON.evalM (ldon : LDON) : StoreM $ State × Array State := do
  State.eval ⟨← putLDON ldon, ← putSym .nil, ⟨.done, .zero⟩⟩

def LDON.eval (ldon : LDON) (store : Store := default) :
    Except String $ State × (Array State) × Store :=
  match EStateM.run ldon.evalM store with
  | .ok (stt, stts) store => return (stt, stts, store)
  | .error e _ => throw e

def test (ldon : LDON) : Except String Nat :=
  match ldon.eval with
  | .ok x => return x.2.1.size.pred
  | .error x => throw x

-- (letrec ((count10 (lambda (i) (if (= i 10) i (count10 (+ i 1)))))) (count10 0))
-- (let ((a 1) (b a)) b)
-- (if nil 1 (+ 1 2))
-- ((lambda (x y) (+ x y)) (+ 1 1) 3)
open LDON.DSL
def main : IO Unit :=
  let code := ⟪
    (letrec ((count10 (lambda (i) (if (= i 10) i (count10 (+ i 1)))))) (count10 0))
  ⟫
  match test code with
  | .ok e | .error e => IO.println e
