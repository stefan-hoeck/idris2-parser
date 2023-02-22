module Text.JSON.Parser

import Text.Parse.Manual
import Text.JSON.Lexer
import Text.JSON.Value

%inline
fromChar : Char -> JSToken
fromChar = Symbol

0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded JSToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b JSToken xs JSErr t

array : Bounds -> SnocList JSON -> Rule True JSON

object : Bounds -> SnocList (String,JSON) -> Rule True JSON

value : Rule True JSON
value (B (Lit y) _ :: xs)        _      = Succ0 y xs
value (B '[' _ :: B ']' _ :: xs) _      = Succ0 (JArray []) xs
value (B '[' b :: xs)            (SA r) = succT $ array b [<] xs r
value (B '{' _ :: B '}' _ :: xs) _      = Succ0 (JObject []) xs
value (B '{' b :: xs)            (SA r) = succT $ object b [<] xs r
value (x :: xs) _                       = unexpected x
value [] _                              = eoi

array b sv xs sa@(SA r) = case value xs sa of
  Succ0 v (B ',' _ :: ys) => succT $ array b (sv :< v) ys r
  Succ0 v (B ']' _ :: ys) => Succ0 (JArray $ sv <>> [v]) ys
  res                     => failInParen b '[' res

object b sv (B (Lit $ JString l) _ :: B ':' _ :: xs) (SA r) =
  case succT $ value xs r of
    Succ0 v (B ',' _ :: ys) => succT $ object b (sv :< (l,v)) ys r
    Succ0 v (B '}' _ :: ys) => Succ0 (JObject $ sv <>> [(l,v)]) ys
    res                     => failInParen b '[' res
object b sv (B (Lit $ JString _) _ :: x :: xs) _ = expected x.bounds ':'
object b sv (x :: xs)                          _ = custom x.bounds ExpectedString
object b sv []                                 _ = eoi

export
parseJSON :
     Origin
  -> String
  -> Either (FileContext, ParseErr) JSON
parseJSON o str = case lexJSON str of
  Right ts => case value ts suffixAcc of
    Fail0 x         => Left (fromBounded o x)
    Succ0 v []      => Right v
    Succ0 v (x::xs) => Left (fromBounded o $ Unexpected <$> x)
  Left err => Left (fromBounded o err)
