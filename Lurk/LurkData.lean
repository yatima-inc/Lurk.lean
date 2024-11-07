import Lurk.Expr
import Poseidon.Parameters.BabyBear
import LightData

open Poseidon2.BabyBear (p)
open Std (HashMap)

inductive Tag
  | u64 | num | bigNum | comm | char | str| key | func
  | builtin | coroutine| sym | cons | env | fix | err
deriving BEq, Hashable

def Tag.toNat : Tag -> Nat
  | Tag.u64 => 0
  | Tag.num => 1
  | Tag.bigNum => 2
  | Tag.comm => 3
  | Tag.char => 4
  | Tag.str => 5
  | Tag.key => 6
  | Tag.func => 7
  | Tag.builtin => 8
  | Tag.coroutine => 9
  | Tag.sym => 10
  | Tag.cons => 11
  | Tag.env => 12
  | Tag.fix => 13
  | Tag.err => 14

instance : Hashable <| Zmod p where
  hash a := hash a.rep

structure ZPtr where
  tag : Tag
  digest : Array (Zmod p)
deriving BEq, Hashable

inductive ZPtrType
  | atom
  | tuple11 (a : ZPtr) (b : ZPtr)
  | tuple110 (a : ZPtr) (b : ZPtr) (c : ZPtr)

def ZDag := HashMap ZPtr ZPtrType

structure LurkData where
  zptr : ZPtr
  zdag : ZDag

structure CommData where
  secret : Array (Zmod p)
  payload : ZPtr
  zdag : ZDag

