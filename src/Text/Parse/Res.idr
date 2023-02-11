module Text.Parse.Res

import Data.List.Suffix
import Text.Bounded
import Text.ParseError

%default total

||| Result of running a (hand-written) parser.
public export
data Res :
     (strict : Bool)
  -> (t   : Type)
  -> (ts  : List $ Bounded t)
  -> (e,a : Type)
  -> Type where

  Fail  :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List $ Bounded t}
    -> (err : Bounded $ ParseError t e)
    -> Res b t ts e a

  Succ :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List $ Bounded t}
    -> (res  : a)
    -> (toks : List $ Bounded t)
    -> {auto 0 prf  : Suffix b toks ts}
    -> Res b t ts e a

public export
FailParse (Res b t ts e) t e where
  parseFail b err = Fail (B err b)

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Res (x || y) t ts e a -> Res (y || x) t ts e a
swapOr = swapOr (\k => Res k t ts e a)

public export %inline
orSame : {0 x : _} -> Res (x || x) t ts e a -> Res x t ts e a
orSame = orSame (\k => Res k t ts e a)

public export %inline
orTrue : {0 x : _} -> Res (x || True) t ts e a -> Res True t ts e a
orTrue = orTrue (\k => Res k t ts e a)

public export %inline
orFalse : {0 x : _} -> Res (x || False) t ts e a -> Res x t ts e a
orFalse = orFalse (\k => Res k t ts e a)

public export %inline
swapAnd : {0 x,y : _} -> Res (x && y) t ts e a -> Res (y && x) t ts e a
swapAnd = swapAnd (\k => Res k t ts e a)

public export %inline
andSame : {0 x : _} -> Res (x && x) t ts e a -> Res x t ts e a
andSame = andSame (\k => Res k t ts e a)

public export %inline
andTrue : {0 x : _} -> Res (x && True) t ts e a -> Res x t ts e a
andTrue = andTrue (\k => Res k t ts e a)

public export %inline
andFalse : {0 x : _} -> Res (x && False) t ts e a -> Res False t ts e a
andFalse = andFalse (\k => Res k t ts e a)

public export %inline
weaken : {0 x : _} -> Res x t ts e a -> Res False t ts e a
weaken (Succ val xs @{p}) = Succ val xs @{weaken p}
weaken (Fail err) = Fail err

public export %inline
weakens : {0 x : _} -> Res True t ts e a -> Res x t ts e a
weakens (Succ val xs @{p}) = Succ val xs @{weakens p}
weakens (Fail err) = Fail err

public export %inline
and1 : {0 x : _} -> Res x t ts e a -> Res (x && y) t ts e a
and1 (Succ val xs @{p}) = Succ val xs @{and1 p}
and1 (Fail err) = Fail err

public export %inline
and2 : {0 x : _} -> Res x t ts e a -> Res (y && x) t ts e a
and2 r = swapAnd $ and1 r

public export %inline
trans : Res b1 t xs e a -> (0 _ : Suffix b2 xs ys) -> Res (b1 || b2) t ys e a
trans (Succ val ts @{p}) q = Succ val ts @{p ~> q}
trans (Fail err)         _ = Fail err

||| Operator alias for `trans`.
public export %inline
(~>) : Res b1 t xs e a -> (0 _ : Suffix b2 xs ys) -> Res (b1 || b2) t ys e a
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : (0 _ : Suffix b1 xs ys) -> Res b2 t xs e a -> Res (b1 || b2) t ys e a
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) : Res b1 t xs e a -> (0 _ : Suffix b2 xs ys) -> Res False t ys e a
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Suffix` dominates.
public export %inline
(~~>) : Res b1 t xs e a -> (0 _ : Suffix True xs ys) -> Res b1 t ys e a
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Suffix` dominates.
public export %inline
(<~~) : (0 _ : Suffix b1 xs ys) -> Res True t xs e a -> Res b1 t ys e a
(<~~) x y = weakens $ y ~> x

public export %inline
succ :
      Res b1 t xs e a
  -> {auto 0 p : Suffix True xs ys}
  -> Res True t ys e a
succ r = p <~ r

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     Res b1 t ts e a
  -> Lazy (Res b2 t ts e a)
  -> Res (b1 && b2) t ts e a
Succ v xs @{p} <|> _  = Succ v xs @{and1 p}
Fail _         <|> r2 = and2 r2

public export
Functor (Res b t ts e) where
  map f (Succ v xs) = Succ (f v) xs
  map _ (Fail err)  = Fail err

--------------------------------------------------------------------------------
--          Error Messages
--------------------------------------------------------------------------------

||| General catch-all error generator when parsing within some kind
||| of opening token: Will fail with an `Unclosed` error if at the
||| end of input, or with an `Unknown` error wrapping the next token.
||| Otherwise, will rethrow the current error.
|||
||| @ b   : Bounds of the opening paren or token
||| @ tok : Opening paren or token
||| @ res : Current parsing result
public export
failInParen : (b : Bounds) -> (tok : t) -> Res b1 t ts e a -> Res b2 t ts e a
failInParen b tok (Fail (B (Reason EOI) _)) = unclosed b tok
failInParen b tok (Fail err)                = Fail err
failInParen b tok (Succ _ [])               = unclosed b tok
failInParen b tok (Succ _ (x :: xs))        = unexpected x
