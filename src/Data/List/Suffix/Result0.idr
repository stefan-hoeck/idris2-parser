module Data.List.Suffix.Result0

import Data.List.Suffix

%default total

||| Result of consuming and converting a (possibly strict) prefix
||| of a list of tokens.
|||
||| This comes with an erased proof about the number of tokens
||| consumed. Consider using `Data.List.Suffix.Result` if you need
||| to keep track of the number of tokens consumed at runtime.
|||
||| Use this for manually writing high-performance parsers, which
||| (in the case of strict results) are guaranteed to terminate.
||| See module `Text.Parse.Manual` for
||| utilities for consuming and converting prefixes
||| of tokens, but for a nicer interface, consider using `Text.Parse.Core`
||| (at the cost of a drop in performance).
|||
||| @ strict : True if a strict prefix of the list of tokens has
|||            been consumed.
||| @ t      : the type of token consumed.
||| @ ts     : the original list of tokens
||| @ e      : the error type in case of a failure
||| @ a      : the result type
public export
data Result0 :
     (strict : Bool)
  -> (t : Type)
  -> List t
  -> (e,a : Type)
  -> Type where

  Succ0 :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto 0 p : Suffix b xs ts}
    -> Result0 b t ts e a

  Fail0 :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (err : e)
    -> Result0 b t ts e a

||| Alias for `Succ`, which takes the proof as an
||| explicit argument
public export %inline
succ : 
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> {xs : List t}
    -> (0 p : Suffix b xs ts)
    -> Result0 b t ts e a
succ val _ = Succ0 val xs

public export
Functor (Result0 b t ts e) where
  map f (Succ0 v xs) = Succ0 (f v) xs
  map _ (Fail0 err)  = Fail0 err

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Result0 (x || y) t ts e a -> Result0 (y || x) t ts e a
swapOr = swapOr (\k => Result0 k t ts e a)

public export %inline
orSame : {0 x : _} -> Result0 (x || x) t ts e a -> Result0 x t ts e a
orSame = orSame (\k => Result0 k t ts e a)

public export %inline
orTrue : {0 x : _} -> Result0 (x || True) t ts e a -> Result0 True t ts e a
orTrue = orTrue (\k => Result0 k t ts e a)

public export %inline
orFalse : {0 x : _} -> Result0 (x || False) t ts e a -> Result0 x t ts e a
orFalse = orFalse (\k => Result0 k t ts e a)

public export %inline
swapAnd : {0 x,y : _} -> Result0 (x && y) t ts e a -> Result0 (y && x) t ts e a
swapAnd = swapAnd (\k => Result0 k t ts e a)

public export %inline
andSame : {0 x : _} -> Result0 (x && x) t ts e a -> Result0 x t ts e a
andSame = andSame (\k => Result0 k t ts e a)

public export %inline
andTrue : {0 x : _} -> Result0 (x && True) t ts e a -> Result0 x t ts e a
andTrue = andTrue (\k => Result0 k t ts e a)

public export %inline
andFalse : {0 x : _} -> Result0 (x && False) t ts e a -> Result0 False t ts e a
andFalse = andFalse (\k => Result0 k t ts e a)

public export %inline
weaken : {0 x : _} -> Result0 x t ts e a -> Result0 False t ts e a
weaken (Succ0 val xs @{p}) = Succ0 val xs @{weaken p}
weaken (Fail0 err)         = Fail0 err

public export %inline
weakens : {0 x : _} -> Result0 True t ts e a -> Result0 x t ts e a
weakens (Succ0 val xs @{p}) = Succ0 val xs @{weakens p}
weakens (Fail0 err)         = Fail0 err

public export %inline
and1 : {0 x : _} -> Result0 x t ts e a -> Result0 (x && y) t ts e a
and1 (Succ0 val xs @{p}) = Succ0 val xs @{and1 p}
and1 (Fail0 err)         = Fail0 err

public export %inline
and2 : {0 x : _} -> Result0 x t ts e a -> Result0 (y && x) t ts e a
and2 r = swapAnd $ and1 r

public export %inline
trans :
     Result0 b1 t xs e a
  -> (0 _ : Suffix b2 xs ys)
  -> Result0 (b1 || b2) t ys e a
trans (Succ0 val ts @{p}) q = Succ0 val ts @{p ~> q}
trans (Fail0 err)         _ = Fail0 err

||| Operator alias for `trans`.
public export %inline
(~>) :
     Result0 b1 t xs e a
  -> (0 _ : Suffix b2 xs ys)
  -> Result0 (b1 || b2) t ys e a
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) :
     (0 _ : Suffix b1 xs ys)
  -> Result0 b2 t xs e a
  -> Result0 (b1 || b2) t ys e a
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) :
     Result0 b1 t xs e a
  -> (0 _ : Suffix b2 xs ys)
  -> Result0 False t ys e a
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Suffix` dominates.
public export %inline
(~~>) : Result0 b1 t xs e a -> (0 _ : Suffix True xs ys) -> Result0 b1 t ys e a
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Suffix` dominates.
public export %inline
(<~~) : (0 _ : Suffix b1 xs ys) -> Result0 True t xs e a -> Result0 b1 t ys e a
(<~~) x y = weakens $ y ~> x

public export %inline
succT :
      Result0 b1 t xs e a
  -> {auto 0 p : Suffix True xs ys}
  -> Result0 True t ys e a
succT r = p <~ r

public export %inline
succF :
      Result0 b1 t xs e a
  -> {auto 0 p : Suffix True xs ys}
  -> Result0 False t ys e a
succF r = r ~?> p

--------------------------------------------------------------------------------
--          Combinators
-----------------------------------------------------------------------------

public export
(<|>) :
     Result0 b1 t ts e a
  -> Lazy (Result0 b2 t ts e a)
  -> Result0 (b1 && b2) t ts e a
Succ0 v xs @{p} <|> _  = Succ0 v xs @{and1 p}
Fail0 _         <|> r2 = and2 r2

--------------------------------------------------------------------------------
--          Running a Parser
-----------------------------------------------------------------------------

||| Repeatedly consumes a strict prefix of a list of items
||| until the whole list is consumed.
|||
||| This is provably total, due to the strictness of the consuming
||| function.
public export
run :
     {0 t,e,a : Type}
  -> ((ts : List t) -> Result0 True t ts e a)
  -> List t -> Either e (List a)
run f cs = go [<] cs suffixAcc
  where
    go : SnocList a
      -> (ts : List t)
      -> (0 acc : SuffixAcc ts)
      -> Either e (List a)
    go sx [] _      = Right $ sx <>> []
    go sx xs (SA r) = case f xs of
      Succ0 v xs2 => go (sx :< v) xs2 r
      Fail0 err   => Left err

||| Repeatedly consumes a strict prefix of a list of characters
||| until the whole list is consumed. Drops all white space
||| it encounters (unsing `Prelude.isSpace` to determine, what is
||| a whitespace character).
|||
||| This is provably total, due to the strictness of the consuming
||| function.
public export
runDropWhitespace :
     {0 e,a : Type}
  -> ((cs : List Char) -> Result0 True Char cs e a)
  -> List Char -> Either e (List a)
runDropWhitespace f cs = go [<] cs suffixAcc
  where
    go : SnocList a
      -> (cs : List Char)
      -> (0 acc : SuffixAcc cs)
      -> Either e (List a)
    go sx [] _           = Right $ sx <>> []
    go sx (x::xs) (SA r) = 
      if isSpace x then go sx xs r
      else case f (x::xs) of
        Succ0 v xs2 => go (sx :< v) xs2 r
        Fail0 err   => Left err
