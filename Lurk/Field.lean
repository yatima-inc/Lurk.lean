import YatimaStdLib.Nat
import YatimaStdLib.ByteArray
import YatimaStdLib.Zmod

namespace Lurk

def N := 2013265921

abbrev F := Fin N

def F.toZmod : F → Zmod N := fun x => x.val

instance : Coe F (Zmod N) where
  coe := F.toZmod

def F.ofNat (n : Nat) : F :=
  .ofNat n

def F.asHex (n : F) : String :=
  n.val.asHex 32

instance : Inhabited F := ⟨.ofNat 0⟩

@[match_pattern] def F.zero : F :=
  .ofNat 0

@[inline] def F.toBytes (n : F) : ByteArray :=
  let bytes := n.val.toByteArrayLE
  bytes.pushZeros $ 32 - bytes.size

@[inline] def F.ofBytes (bytes : ByteArray) : F :=
  .ofNat bytes.asLEtoNat

def F.lt (x y : F) : Bool :=
  match (decide $ x.val < N / 2, decide $ y.val < N / 2) with
    | (true, false) => false
    | (false, true) => true
    | _ => x < y

def F.le (x y : F) : Bool :=
  match (decide $ x.val < N / 2, decide $ y.val < N / 2) with
    | (true, false) => false
    | (false, true) => true
    | _ => x <= y

@[inline] def F.gt (x y : F) : Bool :=
  F.lt y x

@[inline] def F.ge (x y : F) : Bool :=
  F.le y x

/-- Has to be size 8 -/
abbrev Digest := Array F

def Digest.toZmodArray (x : Digest) : Array (Zmod N) := x.map F.toZmod

instance : Coe Digest (Array <| Zmod N) where
  coe x := x.toZmodArray

def Digest.ofZmodArray (x : Array (Zmod N)) : Digest := x.map fun y => .ofNat y.norm

instance : Coe (Array <| Zmod N) Digest where
  coe x := .ofZmodArray x

@[match_pattern] def Digest.zero : Digest := #[.zero, .zero, .zero, .zero, .zero, .zero, .zero, .zero]

def Digest.asHex (digest : Digest) : String :=
  let hex := digest.map F.asHex
  String.join hex.toList

def Digest.toNatAsBytes (digest : Digest) : Nat := digest.reverse.foldl (fun acc elem => acc * (2 ^ 8) + elem) 0

def Digest.ofSmallNat (n : Nat) : Digest := Digest.zero.set! 0 <| .ofNat n

def Digest.ofChar (c : Char) : Digest :=
  let u32 := c.val
  let byte1 := u32 &&& 0b11111111
  let byte2 := (u32 >>> 8) &&& 0b11111111
  let byte3 := (u32 >>> 16) &&& 0b11111111
  let byte4 := (u32 >>> 24) &&& 0b11111111
  #[.ofNat byte1.toNat, .ofNat byte2.toNat, .ofNat byte3.toNat, .ofNat byte4.toNat, .zero, .zero, .zero, .zero]

def Digest.ofUInt64 (u : UInt64) : Digest :=
  let byte1 := u &&& 0b11111111
  let byte2 := (u >>> 8) &&& 0b11111111
  let byte3 := (u >>> 16) &&& 0b11111111
  let byte4 := (u >>> 24) &&& 0b11111111
  let byte5 := (u >>> 32) &&& 0b11111111
  let byte6 := (u >>> 40) &&& 0b11111111
  let byte7 := (u >>> 48) &&& 0b11111111
  let byte8 := (u >>> 56) &&& 0b11111111
  #[.ofNat byte1.toNat, .ofNat byte2.toNat, .ofNat byte3.toNat, .ofNat byte4.toNat, .ofNat byte5.toNat, .ofNat byte6.toNat, .ofNat byte7.toNat, .ofNat byte8.toNat]

end Lurk
