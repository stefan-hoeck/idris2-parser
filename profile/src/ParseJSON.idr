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
       (res  : a)
    -> (toks : List $ Bounded Tok)
    -> {auto 0 prf  : Suffix b toks ts}
    -> JRes b ts a

export %inline
weaken : JRes b1 ts a -> JRes False ts a
weaken (Fail err)           = Fail err
weaken (Succ res toks @{p}) = Succ res toks @{weaken p}

export %inline
weakens : JRes True ts a -> JRes b ts a
weakens (Fail err)           = Fail err
weakens (Succ res toks @{p}) = Succ res toks @{weakens p}

export %inline
succ : JRes b ts a -> {auto 0 p : Suffix True ts bs} -> JRes b bs a
succ (Fail err)             = Fail err
succ (Succ res toks @{prf}) = Succ res toks @{weakens $ p <~ prf}

0 Rule : Bool -> Type -> Type
Rule b t = (xs : List $ Bounded Tok) -> (0 acc : SuffixAcc xs) -> JRes b xs t

array : Bounds -> SnocList JSON -> Rule True JSON

object : Bounds -> SnocList (String,JSON) -> Rule True JSON

value : Rule True JSON
value (BD (Lit y) _ :: xs)                   _      = Succ y xs
value (BD BracketO _ :: BD BracketC _ :: xs) _      = Succ (JArray []) xs
value (BD BracketO b :: xs)                  (SA r) = succ $ array b [<] xs r
value (BD BraceO _ :: BD BraceC _ :: xs)     _      = Succ (JObject []) xs
value (BD BraceO b :: xs)                    (SA r) = succ $ object b [<] xs r
value (x :: xs) _                                   = Fail (Unexpected x)
value [] _                                          = Fail EOI

array b sv xs sa@(SA r) = case value xs sa of
  Succ v (BD Comma _    :: ys) => succ $ array b (sv :< v) ys r
  Succ v (BD BracketC _ :: ys) => Succ (JArray $ sv <>> [v]) ys
  Succ v (y             :: ys) => Fail (Unexpected y)
  Succ _ []                    => Fail (UnmatchedBracket b)
  Fail EOI                     => Fail (UnmatchedBracket b)
  Fail err                     => Fail err

object b sv (BD (Lit $ JString l) _ :: BD Colon _ :: xs) (SA r) =
  case succ $ value xs r of
    Succ v (BD Comma _    :: ys) => succ $ object b (sv :< (l,v)) ys r
    Succ v (BD BracketC _ :: ys) => Succ (JObject $ sv <>> [(l,v)]) ys
    Succ v (y             :: ys) => Fail (Unexpected y)
    Succ _ []                    => Fail (UnmatchedBrace b)
    Fail EOI                     => Fail (UnmatchedBrace b)
    Fail err                     => Fail err
object b sv (BD (Lit $ JString _) _ :: x :: xs) _ = Fail (Unexpected x)
object b sv (x :: xs)                           _ = Fail (Unexpected x)
object b sv []                                  _ = Fail EOI

0 Ru : Bool -> Type -> Type
Ru b a = Grammar b () Tok Void a

str : Ru True String
str = terminal $ \case {Lit (JString s) => Just s; _ => Nothing}

lit : Ru True JSON
lit = terminal $ \case
  Lit j  => Just j
  _        => Nothing

val,vals,obj,prs,arr : Ru True JSON

val = lit <|> arr <|> obj

vals = JArray <$> (sepBy (is Comma) val <* is BracketC)

arr = is BracketO >>= \_ => vals

pr : Ru True (String,JSON)
pr = [| MkPair (str <* is Colon) val |]

prs = JObject <$> (sepBy (is Comma) pr <* is BraceC)

obj = is BraceO >>= \_ => prs

export
fastParse : String -> Either JPErr JSON
fastParse str = case json str of
  (ts,l,c,[]) => case value (ts <>> []) suffixAcc of
    Fail x         => Left x
    Succ v []      => Right v
    Succ v (x::xs) => Left (Unexpected x)
  (_,l,c,_) => Left LexErr

export
niceParse : String -> Either (ReadError Tok Void) JSON
niceParse str = case json str of
  (ts,l,c,[]) => case parse val () (ts <>> []) of
    Left errs => Left $ parseFailed Virtual errs
    Right (_,res,[]) => Right res
    Right (_,res, (x::xs))  => Left (ParseFailed $ singleton $ virtualFromBounded (Unexpected <$> x))
  (_,l,c,_) => Left (LexFailed (FC Virtual $ BS l c l (c+1)) NoRuleApply)
