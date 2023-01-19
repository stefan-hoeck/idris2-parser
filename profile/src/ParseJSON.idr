module ParseJSON

import Derive.Prelude
import JSON
import LexJSON
import Text.Lex
import Text.Parse

%language ElabReflection
%default total

public export
data JPErr : Type where
  LexErr           : JPErr
  UnmatchedBracket : Bounds -> JPErr
  UnmatchedBrace   : Bounds -> JPErr
  Unexpected       : Bounded Tok  -> JPErr
  EOI              : JPErr

%runElab derive "JPErr" [Show,Eq]

||| Result of running a parser.
public export
data JRes :
     (strict : Bool)
  -> (ts : List $ Bounded Tok)
  -> (a : Type)
  -> Type where

  Fail : (err : JPErr) -> JRes b ts a

  Succ :
       (res   : a)
    -> (toks  : List $ Bounded Tok)
    -> (0 prf : Suffix b toks ts)
    -> JRes b ts a

||| This is the identity at runtime
export
mapPrf :
     {0 a     : Type}
  -> {0 as,bs : List $ Bounded Tok}
  -> (0 f :
          {ts : List $ Bounded Tok}
       -> Suffix b1 ts as
       -> Suffix b2 ts bs
     )
  -> JRes b1 as a
  -> JRes b2 bs a
mapPrf f (Fail err)          = Fail err
mapPrf f (Succ res toks prf) = Succ res toks (f prf)

export %inline
weaken : JRes b1 ts a -> JRes False ts a
weaken = mapPrf weaken

export %inline
weakens : JRes True ts a -> JRes b ts a
weakens = mapPrf weakens

export %inline
(~>) : JRes s1 ts a -> (0 p : Suffix s2 ts bs) -> JRes (s2 || s1) bs a
r ~> p = mapPrf (\q => swapOr $ trans q p) r

export %inline
(~?>) : JRes s1 ts a -> (0 p : Suffix s2 ts bs) -> JRes False bs a
r ~?> p = mapPrf (\q => weaken $ trans q p) r

0 Rule : Bool -> Type -> Type
Rule b t =
     (ts : List $ Bounded Tok)
  -> (0 acc : SuffixAcc ts)
  -> JRes b ts t

array : Bounds -> SnocList JSON -> Rule True JSON

object : Bounds -> SnocList (String,JSON) -> Rule True JSON

value : Rule True JSON
value (x :: xs) (Access rec) = case x.val of 
  TLit y    => Succ y xs %search
  TBracketO => array  x.bounds [<] xs (rec xs cons1) ~> cons1
  TBraceO   => object x.bounds [<] xs (rec xs cons1) ~> cons1
  _         => Fail (Unexpected x)
value [] acc        = Fail EOI

array b sv []                  (Access rec) = Fail (UnmatchedBracket b)
array b sv (MkBounded TBracketC _ :: xs) (Access rec) = Succ (JArray $ sv <>> Nil) xs %search
array b sv xs                  (Access rec) =
  let Succ v (MkBounded TComma _ :: xs2) p := value xs (Access rec)
        | Succ v (MkBounded TBracketC _ :: xs2) p =>
            Succ (JArray $ sv <>> [v]) xs2 $ cons1 ~> p
        | Succ _ (x :: xs2) _  => Fail (Unexpected x)
        | Succ _ [] _          => Fail (UnmatchedBracket b)
        | Fail EOI             => Fail (UnmatchedBracket b)
        | Fail err             => Fail err
      0 p' := cons1 ~> p
   in array b (sv :< v) xs2 (rec xs2 p') ~> p'

object b sv []                  (Access rec) = Fail (UnmatchedBrace b)
object b sv (MkBounded TBraceC _ :: xs) (Access rec) = Succ (JObject $ sv <>> Nil) xs %search
object b sv (MkBounded (TLit $ JString l) _ :: MkBounded TColon _ :: xs) (Access rec) =
  let Succ v (MkBounded TComma _ :: xs2) p := value xs (rec xs %search) ~> cons1 ~> cons1
        | Succ v (MkBounded TBraceC _ :: xs2) p =>
            Succ (JObject $ sv <>> [(l,v)]) xs2 $ cons1 ~> p
        | Succ _ (x :: xs2) _  => Fail (Unexpected x)
        | Succ _ [] _          => Fail (UnmatchedBrace b)
        | Fail EOI             => Fail (UnmatchedBrace b)
        | Fail err             => Fail err
      0 p' := cons1 ~> p
   in object b (sv :< (l,v)) xs2 (rec xs2 p') ~> p'
object b sv (x :: xs) (Access rec) = Fail (Unexpected x)

0 Ru : Bool -> Type -> Type
Ru b a = Grammar b () Tok Void a

str : Ru True String
str = terminal $ \case {TLit (JString s) => Just s; _ => Nothing}

lit : Ru True JSON
lit = terminal $ \case
  TLit j  => Just j
  _        => Nothing

val,vals,obj,prs,arr : Ru True JSON

val = lit <|> arr <|> obj

vals = JArray <$> (sepBy (is TComma) val <* is TBracketC)

arr = is TBracketO >>= \_ => vals

pr : Ru True (String,JSON)
pr = [| MkPair (str <* is TColon) val |]

prs = JObject <$> (sepBy (is TComma) pr <* is TBraceC)

obj = is TBraceO >>= \_ => prs

export
fastParse : String -> Either JPErr JSON
fastParse str = case json str of
  (ts,l,c,[]) => case value (ts <>> []) (ssAcc _) of
    Fail x  => Left x
    Succ v [] _  => Right v
    Succ v (x::xs) _  => Left (Unexpected x)
  (_,l,c,_) => Left LexErr

export
niceParse : String -> Either (ReadError Tok Void) JSON
niceParse str = case json str of
  (ts,l,c,[]) => case parse val () (ts <>> []) of
    Left errs => Left $ parseFailed Virtual errs
    Right (_,res,[]) => Right res
    Right (_,res, (x::xs))  => Left (ParseFailed $ singleton $ virtualFromBounded (Unexpected <$> x))
  (_,l,c,_) => Left (LexFailed (FC Virtual $ MkBounds l c l (c+1)) NoRuleApply)
