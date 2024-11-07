import Std.Internal.Parsec.String
import Lurk.LDON

def Char.asHexDigitToNat (c : Char) : Nat :=
  if c.isDigit then c.val.toNat - 48
  else 10 + c.val.toNat - 97

namespace Lurk.Parser

open Std.Internal.Parsec String

private def between {α : Type} (init final : Char) (p : Parser α) : Parser α := do
  skipChar init
  let d ← p
  skipChar final
  return d

def nonHexNumP : Parser LDON := do
  let d ← digits
  return .num <| .ofNat d

def hexNumP : Parser LDON := do
  skipString "0x"
  _ ← many <| skipChar '0'
  let chars ← many1 <| hexDigit
  let (n, _) := chars.foldr (init := (0, 1)) fun c (n, p) =>
    (n + p * c.asHexDigitToNat, 16 * p)
  return .num <| .ofNat n

def numP : Parser LDON :=
  hexNumP <|> nonHexNumP

def charP : Parser LDON := do
  discard <| pstring "#\\"
  return .char (←asciiLetter)

def strP : Parser LDON := between '"' '"' $
  .str <$> .mk <$> Array.data <$> many1 (satisfy (· != '\"'))

def validSpecialSymChar : Char → Bool
  | '+' | '-' | '*' | '/' | '=' | '<' | '>' => true
  | _ => false

def noEscSymP : Parser LDON := do
  let c ← satisfy fun c => c.isAlpha || validSpecialSymChar c
  let x ← many (satisfy fun c => c.isAlphanum || validSpecialSymChar c)
  let i : String := ⟨c :: x.data⟩
  let iU := i.toUpper
  if LDON.reservedSyms.contains iU then
    return .sym iU
  else
    return .sym i

def escSymP : Parser LDON := between '|' '|' $
  .sym <$> String.mk <$> Array.data <$> many1 (satisfy (· != '|'))

def symP : Parser LDON :=
  escSymP <|> noEscSymP

def blanksP : Parser Unit :=
  discard <| many <| satisfy (fun x => x == ' ' || x == '\n' || x == '\t')

def atomP : Parser LDON :=
  symP <|> numP <|> charP <|> strP

mutual

partial def quoteP : Parser LDON := do
  skipChar '\''
  let x ← astP
  return .mkQuote x

partial def listP : Parser LDON := between '(' ')' $ do
  blanksP
  let x ← many astP
  return .consWith x.data .nil

partial def dottedListP : Parser LDON := between '(' ')' $ do
  let xs ← many1 astP
  skipChar '.'
  let x ← astP
  return .consWith xs.data x

partial def astP : Parser LDON := do
  blanksP
  let x ← atomP <|> (attempt listP) <|> dottedListP <|> quoteP
  blanksP
  return x

end

protected def parse (code : String) : Except String LDON := astP.run code

end Lurk.Parser
