module ParseJSON

import Derive.Prelude
import LexJSON
import Text.Parse.Manual

%language ElabReflection
%default total

0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded JSToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b JSToken xs JSErr t

array : Bounds -> SnocList JSON -> Rule True JSON

object : Bounds -> SnocList (String,JSON) -> Rule True JSON

value : Rule True JSON
value (B (Lit y) _ :: xs)        _      = Succ y xs
value (B '[' _ :: B ']' _ :: xs) _      = Succ (JArray []) xs
value (B '[' b :: xs)            (SA r) = succ $ array b [<] xs r
value (B '{' _ :: B '}' _ :: xs) _      = Succ (JObject []) xs
value (B '{' b :: xs)            (SA r) = succ $ object b [<] xs r
value xs                         _      = fail xs

array b sv xs sa@(SA r) = case value xs sa of
  Succ v (B ',' _ :: ys)  => succ $ array b (sv :< v) ys r
  Succ v (B ']' _ :: ys)  => Succ (JArray $ sv <>> [v]) ys
  res                     => failInParen b '[' res

object b sv (B (Lit $ JString l) _ :: B ':' _ :: xs) (SA r) =
  case succ $ value xs r of
    Res.Succ v (B ',' _ :: ys)  => succ $ object b (sv :< (l,v)) ys r
    Succ v (B '}' _ :: ys)      => Succ (JObject $ sv <>> [(l,v)]) ys
    res                         => failInParen b '{' res
object b sv (B (Lit $ JString _) _ :: x :: xs) _ = expected x.bounds ':'
object b sv (x :: xs)                          _ = custom x.bounds ExpectedString
object b sv []                                 _ = eoi

export
parseJSON :
     Origin
  -> String
  -> Either (FileContext, JSParseErr) JSON
parseJSON o str = case lexJSON str of
  Right ts => case value ts suffixAcc of
    Fail x         => Left (fromBounded o x)
    Succ v []      => Right v
    Succ v (x::xs) => Left (fromBounded o $ Unexpected <$> x)
  Left err => Left (fromBounded o $ Reason <$> err)

export
testParse : String -> IO ()
testParse s = case parseJSON Virtual s of
  Right json => putStrLn "Success: \{show json}"
  Left  err  => putStrLn (uncurry (printParseError s) err)
