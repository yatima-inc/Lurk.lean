import Lurk.Scalar.Datatypes

namespace Lurk.Scalar.SerDe

structure SerializeState where
  bytes : ByteArray
  cache : Std.RBMap F ByteArray compare
  deriving Inhabited

abbrev SerializeM := ReaderT ScalarStore $ StateM SerializeState

def serF (n : F) : SerializeM Unit := do
  match (← get).cache.find? n with
  | some bytes => modify fun stt => { stt with bytes := stt.bytes ++ bytes }
  | none =>
    let bytes := n.toBytes -- this can be a bottleneck so we cache it
    modify fun stt => { stt with
      bytes := stt.bytes ++ bytes
      cache := stt.cache.insert n bytes }

def serPtr (ptr : ScalarPtr) : SerializeM Unit := do
  serF ptr.tag.toF
  serF ptr.val

def serExpr : ScalarExpr → SerializeM Unit
  | .cons car cdr => do serPtr car; serPtr cdr
  | .comm n ptr => do serF n; serPtr ptr
  | .sym ptr => serPtr ptr
  | .fun arg body env => do serPtr arg; serPtr body; serPtr env
  | .num n => serF n
  | .strNil => serPtr ⟨.str, F.zero⟩
  | .strCons head tail => do serPtr head; serPtr tail
  | .char c => serF c
  | .uInt n => serF n

def serStore : SerializeM Unit := do
  let store ← read
  let mut opqPtrs := #[]
  let mut exprs := #[]
  for (ptr, expr?) in store.exprs do
    match expr? with
    | none => opqPtrs := opqPtrs.push ptr
    | some expr => exprs := exprs.push (ptr, expr)
  -- writing opaque pointers
  serF $ .ofNat opqPtrs.size
  opqPtrs.forM fun ptr => serPtr ptr
  -- writing expressions
  serF $ .ofNat exprs.size
  exprs.forM fun (ptr, expr) => do serPtr ptr; serExpr expr
  -- writing comms
  serF $ .ofNat store.comms.size
  store.comms.forM fun n ptr => do serF n; serPtr ptr

def serializeM (roots : List ScalarPtr) : SerializeM Unit := do
  serF $ .ofNat roots.length
  roots.sort.forM serPtr
  serStore

def serialize (roots : List ScalarPtr) (store : ScalarStore) : ByteArray :=
  (StateT.run (ReaderT.run (serializeM roots) store) default).2.bytes

end Lurk.Scalar.SerDe